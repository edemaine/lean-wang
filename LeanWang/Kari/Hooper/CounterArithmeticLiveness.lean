/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.CounterArithmetic

/-!
# Arbitrary-entry liveness of the counter arithmetic blocks

The functional-correctness theorems in `CounterArithmetic` start at the
advertised entry of each block.  Hooper's converse argument also needs the
stronger finite-control fact that an arbitrary configuration cannot remain
forever after entering in the middle of a block.  This file proves that every
owned source state of fixed addition, multiplication, and division reaches an
advertised exit, for arbitrary register values.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterArithmeticLiveness

open CounterMachine CounterProgram CounterArithmetic

/-! ## A generic untouched-clock invariant -/

/-- The register operated on by one primitive instruction. -/
def instructionRegister : Instruction → Register
  | .increment register _ => register
  | .decrement register _ _ => register

/-- No rule in the program operates on the clock register. -/
def AvoidsClock (program : Program) : Prop :=
  ∀ rule ∈ program, instructionRegister rule.2 ≠ .clock

@[simp]
theorem instructionRegister_relocateInstruction
    (offset : State) (instruction : Instruction) :
    instructionRegister (relocateInstruction offset instruction) =
      instructionRegister instruction := by
  cases instruction <;> rfl

theorem avoidsClock_relocate {program : Program}
    (hprogram : AvoidsClock program) (offset : State) :
    AvoidsClock (relocate offset program) := by
  intro rule hrule
  rcases List.mem_map.mp hrule with ⟨original, horiginal, rfl⟩
  simpa [relocateRule] using hprogram original horiginal

theorem avoidsClock_denseProgram
    {sourceCount : Nat} {instruction : State → Instruction}
    (hinstruction : ∀ state < sourceCount,
      instructionRegister (instruction state) ≠ .clock) :
    AvoidsClock (denseProgram sourceCount instruction) := by
  intro rule hrule
  rcases List.mem_map.mp hrule with ⟨state, hstate, rfl⟩
  exact hinstruction state (List.mem_range.mp hstate)

theorem avoidsClock_append {first second : Program}
    (hfirst : AvoidsClock first) (hsecond : AvoidsClock second) :
    AvoidsClock (first ++ second) := by
  intro rule hrule
  rcases List.mem_append.mp hrule with hrule | hrule
  · exact hfirst rule hrule
  · exact hsecond rule hrule

/-- One step of a clock-avoiding program preserves the clock value. -/
theorem clock_eq_of_step {program : Program} (hprogram : AvoidsClock program)
    {cfg nextCfg : Cfg} (hstep : step program cfg = some nextCfg) :
    nextCfg.registers.clock = cfg.registers.clock := by
  cases hlookup : lookupInstruction program cfg.state with
  | none => simp [step, hlookup] at hstep
  | some instruction =>
      have hrule := rule_mem_of_lookupInstruction_eq_some hlookup
      have hregister := hprogram (cfg.state, instruction) hrule
      cases instruction with
      | increment register next =>
          rw [step, hlookup] at hstep
          cases Option.some.inj hstep
          cases register <;>
            simp_all [instructionRegister, Registers.increment,
              Registers.set, Registers.get]
      | decrement register ifZero ifPositive =>
          rw [step, hlookup] at hstep
          by_cases hzero : cfg.registers.get register = 0
          · simp only [hzero, if_pos] at hstep
            cases Option.some.inj hstep
            rfl
          · simp only [hzero, if_false] at hstep
            cases Option.some.inj hstep
            cases register <;>
              simp_all [instructionRegister, Registers.decrement,
                Registers.set, Registers.get]

/-- A finite path through a clock-avoiding program preserves the clock. -/
theorem clock_eq_of_reaches {program : Program} (hprogram : AvoidsClock program)
    {start finish : Cfg}
    (hreach : StateTransition.Reaches (step program) start finish) :
    finish.registers.clock = start.registers.clock := by
  induction hreach with
  | refl => rfl
  | tail hpath hstep ih =>
      have hlast := clock_eq_of_step hprogram (by simpa using hstep)
      exact hlast.trans ih

theorem addFixed_avoidsClock (register : Register) (hregister : register ≠ .clock)
    (amount offset : Nat) :
    AvoidsClock ((addFixedBlock register amount).instantiate offset) := by
  apply avoidsClock_relocate
  apply avoidsClock_denseProgram
  intro state hstate
  simpa [addFixedBlock, denseBlock, addFixedInstruction,
    instructionRegister] using hregister

theorem multiplyFixed_avoidsClock
    (target temp : Register) (htarget : target ≠ .clock)
    (htemp : temp ≠ .clock) (factor offset : Nat) :
    AvoidsClock ((multiplyFixedBlock target temp factor).instantiate offset) := by
  apply avoidsClock_relocate
  apply avoidsClock_denseProgram
  intro state hstate
  by_cases hzero : state = 0
  · simp [multiplyFixedInstruction, hzero, instructionRegister, htarget]
  · by_cases hle : state ≤ factor
    · simp [multiplyFixedInstruction, hzero, hle, instructionRegister, htemp]
    · by_cases htransfer : state = factor + 1
      · simp [multiplyFixedInstruction, hzero, hle, htransfer,
          instructionRegister, htemp]
      · simp [multiplyFixedInstruction, hzero, hle, htransfer,
          instructionRegister, htarget]

theorem divideFixed_avoidsClock
    (target temp : Register) (htarget : target ≠ .clock)
    (htemp : temp ≠ .clock) (divisor offset : Nat) :
    AvoidsClock ((divideFixedBlock target temp divisor).instantiate offset) := by
  apply avoidsClock_relocate
  apply avoidsClock_denseProgram
  intro state hstate
  by_cases hmain : state < divisor
  · simp [divideFixedInstruction, hmain, instructionRegister, htarget]
  · by_cases hgroup : state = divisor
    · simp [divideFixedInstruction, hmain, hgroup, instructionRegister, htemp]
    · by_cases heven : (state - (divisor + 1)) % 2 = 0
      · simp [divideFixedInstruction, hmain, hgroup, heven,
          instructionRegister, htemp]
      · simp [divideFixedInstruction, hmain, hgroup, heven,
          instructionRegister, htarget]

/-- A transfer loop embedded in a larger program terminates whenever its two
lookup entries have the advertised instructions. -/
theorem transfer_reaches_of_lookup
    {program : Program} {entry work exit : State}
    {source target : Register}
    (hentry : lookupInstruction program entry =
      some (.decrement source exit work))
    (hwork : lookupInstruction program work =
      some (.increment target entry))
    (hsourceTarget : source ≠ target)
    (registers : Registers) :
    StateTransition.Reaches (step program)
      ⟨entry, registers⟩
      ⟨exit, transferResult source target registers⟩ := by
  generalize hn : registers.get source = n
  induction n generalizing registers with
  | zero =>
      have hresult : transferResult source target registers = registers :=
        transferResult_eq_self_of_source_zero hsourceTarget hn
      rw [hresult]
      apply Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      exact (by simpa using step_of_lookup_decrement_zero hentry hn)
  | succ n ih =>
      have hpositive : 0 < registers.get source := by omega
      let afterDecrement := registers.decrement source
      let afterPair := afterDecrement.increment target
      have hsourceAfter : afterPair.get source = n := by
        dsimp [afterPair, afterDecrement]
        rw [Registers.get_increment_other
          (registers.decrement source) hsourceTarget]
        simp [hn]
      have hfirst : step program ⟨entry, registers⟩ =
          some ⟨work, afterDecrement⟩ := by
        simpa [afterDecrement] using
          step_of_lookup_decrement_positive hentry hpositive
      have hsecond : step program ⟨work, afterDecrement⟩ =
          some ⟨entry, afterPair⟩ := by
        simpa [afterPair] using step_of_lookup_increment hwork
      have hprefix : StateTransition.Reaches (step program)
          ⟨entry, registers⟩ ⟨entry, afterPair⟩ :=
        Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
            (by simpa using hfirst))
          (by simpa using hsecond)
      have htail := ih afterPair hsourceAfter
      have hresult : transferResult source target afterPair =
          transferResult source target registers :=
        transferResult_pair hsourceTarget hpositive
      rw [hresult] at htail
      exact hprefix.trans htail

/-! ## Addition -/

/-- Fixed addition terminates from every local state at or before its exit. -/
theorem addFixed_reaches_from
    (register : Register) (amount offset localState : Nat)
    (hlocal : localState ≤ amount) (registers : Registers) :
    StateTransition.Reaches
      (step ((addFixedBlock register amount).instantiate offset))
      ⟨offset + localState, registers⟩
      ⟨offset + amount, addResult register (amount - localState) registers⟩ := by
  let remaining := amount - localState
  have hsum : localState + remaining = amount := by
    simp [remaining, Nat.add_sub_of_le hlocal]
  clear_value remaining
  induction remaining generalizing localState registers with
  | zero =>
      have heq : localState = amount := by omega
      subst localState
      simp only [Nat.sub_self, addResult_zero]
      exact Relation.ReflTransGen.refl
  | succ remaining ih =>
      have hlt : localState < amount := by omega
      have hlookup :
          lookupInstruction
              ((addFixedBlock register amount).instantiate offset)
              (offset + localState) =
            some (.increment register (offset + (localState + 1))) := by
        simpa [addFixedBlock, addFixedInstruction] using
          (lookup_denseBlock_instantiate
            (width := amount) (offset := offset)
            (instruction := addFixedInstruction register) hlt)
      have hstep :
          step ((addFixedBlock register amount).instantiate offset)
              ⟨offset + localState, registers⟩ =
            some ⟨offset + (localState + 1), registers.increment register⟩ :=
        step_of_lookup_increment hlookup
      have htail := ih (localState + 1) (by omega)
        (registers.increment register) (by omega)
      have hremaining : amount - localState = remaining + 1 := by omega
      have hremaining' : amount - (localState + 1) = remaining := by omega
      rw [hremaining', addResult_increment] at htail
      rw [hremaining]
      exact (Relation.ReflTransGen.single (by simpa using hstep)).trans htail

/-! ## Multiplication -/

private theorem lookup_multiply_entry
    {target temp : Register} {factor offset : Nat} (hfactor : 0 < factor) :
    lookupInstruction
        ((multiplyFixedBlock target temp factor).instantiate offset) offset =
      some (.decrement target (offset + (factor + 1)) (offset + 1)) := by
  simpa [multiplyFixedBlock, multiplyFixedInstruction] using
    (lookup_denseBlock_instantiate
      (width := factor + 3) (offset := offset)
      (instruction := multiplyFixedInstruction target temp factor)
      (show 0 < factor + 3 by omega))

private theorem lookup_multiply_add
    {target temp : Register} {factor offset localState : Nat}
    (hlocal : 0 < localState) (hle : localState ≤ factor) :
    lookupInstruction
        ((multiplyFixedBlock target temp factor).instantiate offset)
        (offset + localState) =
      some (.increment temp
        (offset + (if localState = factor then 0 else localState + 1))) := by
  have hsource : localState < factor + 3 := by omega
  simpa [multiplyFixedBlock, multiplyFixedInstruction, hlocal.ne', hle] using
    (lookup_denseBlock_instantiate
      (width := factor + 3) (offset := offset)
      (instruction := multiplyFixedInstruction target temp factor) hsource)

private theorem lookup_multiply_transfer_entry
    {target temp : Register} {factor offset : Nat} :
    lookupInstruction
        ((multiplyFixedBlock target temp factor).instantiate offset)
        (offset + (factor + 1)) =
      some (.decrement temp (offset + (factor + 3))
        (offset + (factor + 2))) := by
  simpa [multiplyFixedBlock, multiplyFixedInstruction,
    show factor + 1 ≠ 0 by omega, show ¬ factor + 1 ≤ factor by omega] using
    (lookup_denseBlock_instantiate
      (width := factor + 3) (offset := offset)
      (instruction := multiplyFixedInstruction target temp factor)
      (show factor + 1 < factor + 3 by omega))

private theorem lookup_multiply_transfer_work
    {target temp : Register} {factor offset : Nat} :
    lookupInstruction
        ((multiplyFixedBlock target temp factor).instantiate offset)
        (offset + (factor + 2)) =
      some (.increment target (offset + (factor + 1))) := by
  simpa [multiplyFixedBlock, multiplyFixedInstruction,
    show factor + 2 ≠ 0 by omega, show ¬ factor + 2 ≤ factor by omega,
    show factor + 2 ≠ factor + 1 by omega] using
    (lookup_denseBlock_instantiate
      (width := factor + 3) (offset := offset)
      (instruction := multiplyFixedInstruction target temp factor)
      (show factor + 2 < factor + 3 by omega))

/-- An arbitrary state in the factor-sized addition phase returns to the
multiplication entry. -/
private theorem multiply_add_reaches_entry
    (target temp : Register) (factor offset localState : Nat)
    (hpositive : 0 < localState) (hle : localState ≤ factor)
    (registers : Registers) :
    ∃ finishRegisters,
      StateTransition.Reaches
        (step ((multiplyFixedBlock target temp factor).instantiate offset))
        ⟨offset + localState, registers⟩ ⟨offset, finishRegisters⟩ := by
  let remaining := factor + 1 - localState
  have hremaining : 0 < remaining := by
    dsimp [remaining]
    omega
  have hsum : localState + remaining = factor + 1 := by
    dsimp [remaining]
    omega
  clear_value remaining
  induction remaining generalizing localState registers with
  | zero => omega
  | succ remaining ih =>
      have hlocalFactor : localState ≤ factor := by omega
      have hlookup := lookup_multiply_add
        (target := target) (temp := temp) (offset := offset)
        (localState := localState) (by omega) hlocalFactor
      by_cases hlast : localState = factor
      · subst localState
        have hlookup' : lookupInstruction
            ((multiplyFixedBlock target temp factor).instantiate offset)
            (offset + factor) = some (.increment temp offset) := by
          simpa using hlookup
        refine ⟨registers.increment temp, ?_⟩
        apply Relation.ReflTransGen.single
        simpa using step_of_lookup_increment hlookup'
      · rcases ih (localState + 1) (by omega) (by omega)
            (registers.increment temp) (by omega) (by omega) with
            ⟨finish, hfinish⟩
        have hlookup' : lookupInstruction
            ((multiplyFixedBlock target temp factor).instantiate offset)
            (offset + localState) =
              some (.increment temp (offset + (localState + 1))) := by
          simpa [hlast] using hlookup
        refine ⟨finish, (Relation.ReflTransGen.single ?_).trans hfinish⟩
        simpa using step_of_lookup_increment hlookup'

/-- Every owned state of fixed multiplication reaches its fall-through exit,
even when the temporary register is initially nonzero. -/
theorem multiplyFixed_reaches_from_source
    {target temp : Register} (hne : target ≠ temp)
    {factor : Nat} (hfactor : 0 < factor) (offset localState : Nat)
    (hlocal : localState < factor + 3) (registers : Registers) :
    ∃ finishRegisters,
      StateTransition.Reaches
        (step ((multiplyFixedBlock target temp factor).instantiate offset))
        ⟨offset + localState, registers⟩
        ⟨offset + (factor + 3), finishRegisters⟩ := by
  by_cases hzero : localState = 0
  · subst localState
    exact ⟨multiplyResult target temp factor registers,
      multiplyFixed_reaches hne hfactor offset registers⟩
  by_cases hadd : localState ≤ factor
  · rcases multiply_add_reaches_entry target temp factor offset localState
      (Nat.pos_of_ne_zero hzero) hadd registers with ⟨middle, hmiddle⟩
    exact ⟨multiplyResult target temp factor middle,
      hmiddle.trans (multiplyFixed_reaches hne hfactor offset middle)⟩
  have hlower : factor + 1 ≤ localState := by omega
  have hcases : localState = factor + 1 ∨ localState = factor + 2 := by omega
  rcases hcases with rfl | rfl
  · exact ⟨transferResult temp target registers,
      transfer_reaches_of_lookup lookup_multiply_transfer_entry
        lookup_multiply_transfer_work (Ne.symm hne) registers⟩
  · let middle := registers.increment target
    have hfirst : step
        ((multiplyFixedBlock target temp factor).instantiate offset)
        ⟨offset + (factor + 2), registers⟩ =
        some ⟨offset + (factor + 1), middle⟩ := by
      simpa [middle] using step_of_lookup_increment
        (lookup_multiply_transfer_work
          (target := target) (temp := temp) (factor := factor)
          (offset := offset))
    refine ⟨transferResult temp target middle,
      (Relation.ReflTransGen.single (by simpa using hfirst)).trans ?_⟩
    exact transfer_reaches_of_lookup lookup_multiply_transfer_entry
      lookup_multiply_transfer_work (Ne.symm hne) middle

/-! ## Division -/

private theorem lookup_divide_main
    {target temp : Register} {divisor offset localState : Nat}
    (hlocal : localState < divisor) :
    lookupInstruction
        ((divideFixedBlock target temp divisor).instantiate offset)
        (offset + localState) =
      some (.decrement target
        (offset + divisionTransferEntry divisor localState)
        (offset + (localState + 1))) := by
  have hsource : localState < divisionSourceCount divisor := by
    simp [divisionSourceCount]
    omega
  simpa [divideFixedBlock, divideFixedInstruction, hlocal] using
    (lookup_denseBlock_instantiate
      (width := divisionWidth divisor) (offset := offset)
      (instruction := divideFixedInstruction target temp divisor) hsource)

private theorem lookup_divide_group
    {target temp : Register} {divisor offset : Nat} (hdivisor : 0 < divisor) :
    lookupInstruction
        ((divideFixedBlock target temp divisor).instantiate offset)
        (offset + divisor) =
      some (.increment temp offset) := by
  have hsource : divisor < divisionSourceCount divisor := by
    simp [divisionSourceCount]
    omega
  simpa [divideFixedBlock, divideFixedInstruction] using
    (lookup_denseBlock_instantiate
      (width := divisionWidth divisor) (offset := offset)
      (instruction := divideFixedInstruction target temp divisor) hsource)

private theorem lookup_divide_transfer_entry
    {target temp : Register} {divisor offset remainder : Nat}
    (hremainder : remainder < divisor) :
    lookupInstruction
        ((divideFixedBlock target temp divisor).instantiate offset)
        (offset + divisionTransferEntry divisor remainder) =
      some (.decrement temp
        (offset + divisionExit divisor remainder)
        (offset + divisionTransferWork divisor remainder)) := by
  have hsource : divisionTransferEntry divisor remainder <
      divisionSourceCount divisor := by
    have hdouble : remainder + remainder < divisor + divisor :=
      Nat.add_lt_add hremainder hremainder
    have h := Nat.add_lt_add_left hdouble (divisor + 1)
    simpa [divisionTransferEntry, divisionSourceCount, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using h
  have hlarge : ¬ divisionTransferEntry divisor remainder < divisor := by
    exact not_lt_of_ge (by
      unfold divisionTransferEntry
      simpa [Nat.add_assoc] using
        (Nat.le_add_right divisor (1 + remainder + remainder)))
  have hne : divisionTransferEntry divisor remainder ≠ divisor := by
    exact ne_of_gt (by
      unfold divisionTransferEntry
      simpa [Nat.add_assoc] using
        (Nat.lt_add_of_pos_right (a := divisor) (by omega)))
  have hsub : divisionTransferEntry divisor remainder - (divisor + 1) =
      remainder + remainder := by
    simpa [divisionTransferEntry, Nat.add_assoc] using
      (Nat.add_sub_cancel_left (divisor + 1) (remainder + remainder))
  have hinstruction :
      divideFixedInstruction target temp divisor
          (divisionTransferEntry divisor remainder) =
        .decrement temp (divisionExit divisor remainder)
          (divisionTransferWork divisor remainder) := by
    rw [divideFixedInstruction, if_neg hlarge, if_neg hne]
    rw [hsub, ← two_mul remainder]
    simp [divisionTransferWork]
  have hlookup := lookup_denseBlock_instantiate
      (width := divisionWidth divisor) (offset := offset)
      (instruction := divideFixedInstruction target temp divisor) hsource
  rw [hinstruction] at hlookup
  exact hlookup

private theorem lookup_divide_transfer_work
    {target temp : Register} {divisor offset remainder : Nat}
    (hremainder : remainder < divisor) :
    lookupInstruction
        ((divideFixedBlock target temp divisor).instantiate offset)
        (offset + divisionTransferWork divisor remainder) =
      some (.increment target
        (offset + divisionTransferEntry divisor remainder)) := by
  have hsource : divisionTransferWork divisor remainder <
      divisionSourceCount divisor := by
    have hdouble : remainder + 1 + remainder < divisor + divisor :=
      Nat.add_lt_add_of_le_of_lt (Nat.succ_le_iff.mpr hremainder) hremainder
    have h := Nat.add_lt_add_left hdouble (divisor + 1)
    simpa [divisionTransferWork, divisionTransferEntry, divisionSourceCount,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hlarge : ¬ divisionTransferWork divisor remainder < divisor := by
    exact not_lt_of_ge (by
      unfold divisionTransferWork divisionTransferEntry
      simpa [Nat.add_assoc] using
        (Nat.le_add_right divisor (1 + remainder + remainder + 1)))
  have hne : divisionTransferWork divisor remainder ≠ divisor := by
    exact ne_of_gt (by
      unfold divisionTransferWork divisionTransferEntry
      simpa [Nat.add_assoc] using
        (Nat.lt_add_of_pos_right (a := divisor) (by omega)))
  have hsub : divisionTransferWork divisor remainder - (divisor + 1) =
      remainder + remainder + 1 := by
    simpa [divisionTransferWork, divisionTransferEntry, Nat.add_assoc] using
      (Nat.add_sub_cancel_left (divisor + 1) (remainder + remainder + 1))
  have hback : divisionTransferWork divisor remainder - 1 =
      divisionTransferEntry divisor remainder := by
    simp [divisionTransferWork]
  have hinstruction :
      divideFixedInstruction target temp divisor
          (divisionTransferWork divisor remainder) =
        .increment target (divisionTransferEntry divisor remainder) := by
    rw [divideFixedInstruction, if_neg hlarge, if_neg hne]
    rw [hsub, show remainder + remainder + 1 = 2 * remainder + 1 by
      simp [two_mul]]
    simp [hback]
  have hlookup := lookup_denseBlock_instantiate
      (width := divisionWidth divisor) (offset := offset)
      (instruction := divideFixedInstruction target temp divisor) hsource
  rw [hinstruction] at hlookup
  exact hlookup

private theorem subtractResult_decrement
    (register : Register) (amount : Nat) (registers : Registers)
    (hbound : amount + 1 ≤ registers.get register) :
    subtractResult register amount (registers.decrement register) =
      subtractResult register (amount + 1) registers := by
  cases register <;> cases registers <;>
    simp_all [subtractResult, Registers.get, Registers.set,
      Registers.decrement] <;> omega

/-- Execute a known-successful suffix of the tentative-decrement phase from
an arbitrary main-phase state. -/
private theorem division_decrement_reaches_from
    (target temp : Register) (divisor offset start count : Nat)
    (hend : start + count ≤ divisor)
    (registers : Registers) (hcount : count ≤ registers.get target) :
    StateTransition.Reaches
      (step ((divideFixedBlock target temp divisor).instantiate offset))
      ⟨offset + start, registers⟩
      ⟨offset + (start + count), subtractResult target count registers⟩ := by
  induction count generalizing start registers with
  | zero =>
      simp only [Nat.add_zero, subtractResult_zero]
      exact Relation.ReflTransGen.refl
  | succ count ih =>
      have hstart : start < divisor := by omega
      have hpositive : 0 < registers.get target := by omega
      let afterDecrement := registers.decrement target
      have hlookup := lookup_divide_main
        (target := target) (temp := temp) (offset := offset) hstart
      have hfirst :
          step ((divideFixedBlock target temp divisor).instantiate offset)
              ⟨offset + start, registers⟩ =
            some ⟨offset + (start + 1), afterDecrement⟩ := by
        simpa [afterDecrement] using
          step_of_lookup_decrement_positive hlookup hpositive
      have hcountAfter : count ≤ afterDecrement.get target := by
        dsimp [afterDecrement]
        simp only [Registers.get_decrement_same]
        omega
      have htail := ih (start + 1) (by omega) afterDecrement hcountAfter
      have hresult : subtractResult target count afterDecrement =
          subtractResult target (count + 1) registers :=
        subtractResult_decrement target count registers hcount
      rw [hresult] at htail
      have hpath := (Relation.ReflTransGen.single
        (by simpa using hfirst)).trans htail
      have hstate : offset + ((start + 1) + count) =
          offset + (start + (count + 1)) := by omega
      rw [← hstate]
      exact hpath

/-- Starting in the tentative-subtraction prefix always reaches one of the
reserved remainder exits. -/
private theorem division_main_reaches_exit
    {target temp : Register} (hne : target ≠ temp)
    {divisor : Nat} (hdivisor : 0 < divisor) (offset start : Nat)
    (hstart : start < divisor) (registers : Registers) :
    ∃ remainder finishRegisters,
      remainder < divisor ∧
      StateTransition.Reaches
        (step ((divideFixedBlock target temp divisor).instantiate offset))
        ⟨offset + start, registers⟩
        ⟨offset + divisionExit divisor remainder, finishRegisters⟩ := by
  by_cases henough : divisor - start ≤ registers.get target
  · let count := divisor - start
    have hcountState : start + count = divisor := by
      dsimp [count]
      omega
    have hdecrements := division_decrement_reaches_from target temp divisor
      offset start count (by omega) registers henough
    let afterSubtract := subtractResult target count registers
    let afterGroup := afterSubtract.increment temp
    have hgroup : step
        ((divideFixedBlock target temp divisor).instantiate offset)
        ⟨offset + divisor, afterSubtract⟩ = some ⟨offset, afterGroup⟩ := by
      simpa [afterGroup] using step_of_lookup_increment
        (lookup_divide_group
          (target := target) (temp := temp) (offset := offset) hdivisor)
    have htail := divideFixed_reaches hne hdivisor offset afterGroup
    refine ⟨afterGroup.get target % divisor,
      divideResult target temp divisor afterGroup,
      Nat.mod_lt _ hdivisor, ?_⟩
    have hdecrements' : StateTransition.Reaches
        (step ((divideFixedBlock target temp divisor).instantiate offset))
        ⟨offset + start, registers⟩ ⟨offset + divisor, afterSubtract⟩ := by
      simpa [hcountState, afterSubtract] using hdecrements
    exact (hdecrements'.trans
      (Relation.ReflTransGen.single (by simpa using hgroup))).trans htail
  · let count := registers.get target
    have hcount : count < divisor - start := by
      dsimp [count]
      omega
    have hremainder : start + count < divisor := by omega
    have hdecrements := division_decrement_reaches_from target temp divisor
      offset start count (by omega) registers (by simp [count])
    let afterSubtract := subtractResult target count registers
    have hzero : afterSubtract.get target = 0 := by
      dsimp [afterSubtract, count]
      rw [subtractResult_get_same]
      omega
    have hfailure : step
        ((divideFixedBlock target temp divisor).instantiate offset)
        ⟨offset + (start + count), afterSubtract⟩ =
        some ⟨offset + divisionTransferEntry divisor (start + count),
          afterSubtract⟩ := by
      exact step_of_lookup_decrement_zero
        (lookup_divide_main
          (target := target) (temp := temp) (offset := offset) hremainder)
        hzero
    have htransfer := transfer_reaches_of_lookup
      (lookup_divide_transfer_entry
        (target := target) (temp := temp) (offset := offset) hremainder)
      (lookup_divide_transfer_work
        (target := target) (temp := temp) (offset := offset) hremainder)
      (Ne.symm hne) afterSubtract
    refine ⟨start + count, transferResult temp target afterSubtract,
      hremainder, ?_⟩
    exact (hdecrements.trans
      (Relation.ReflTransGen.single (by simpa using hfailure))).trans htransfer

/-- Every source state above the division group state is one of the two
states in a unique remainder-transfer pair. -/
private theorem division_above_group_cases
    {divisor localState : Nat} (hdivisor : 0 < divisor)
    (hlower : divisor < localState)
    (hupper : localState < divisionSourceCount divisor) :
    ∃ remainder, remainder < divisor ∧
      (localState = divisionTransferEntry divisor remainder ∨
        localState = divisionTransferWork divisor remainder) := by
  let index := localState - (divisor + 1)
  have hstate : localState = divisor + 1 + index := by
    dsimp [index]
    omega
  have hindex : index < divisor + divisor := by
    dsimp [index]
    simp only [divisionSourceCount] at hupper
    omega
  let remainder := index / 2
  have hmodlt : index % 2 < 2 := Nat.mod_lt _ (by omega)
  have hdecomp : index % 2 + 2 * remainder = index := by
    simpa [remainder] using Nat.mod_add_div index 2
  have hremainder : remainder < divisor := by omega
  refine ⟨remainder, hremainder, ?_⟩
  have hmodcases : index % 2 = 0 ∨ index % 2 = 1 := by omega
  rcases hmodcases with hmod | hmod
  · left
    unfold divisionTransferEntry
    omega
  · right
    unfold divisionTransferWork divisionTransferEntry
    omega

/-- Every owned state of fixed division reaches one of its reserved exits,
for arbitrary target and temporary values. -/
theorem divideFixed_reaches_from_source
    {target temp : Register} (hne : target ≠ temp)
    {divisor : Nat} (hdivisor : 0 < divisor) (offset localState : Nat)
    (hlocal : localState < divisionSourceCount divisor)
    (registers : Registers) :
    ∃ remainder finishRegisters,
      remainder < divisor ∧
      StateTransition.Reaches
        (step ((divideFixedBlock target temp divisor).instantiate offset))
        ⟨offset + localState, registers⟩
        ⟨offset + divisionExit divisor remainder, finishRegisters⟩ := by
  by_cases hmain : localState < divisor
  · exact division_main_reaches_exit hne hdivisor offset localState hmain registers
  by_cases hgroup : localState = divisor
  · subst localState
    let middle := registers.increment temp
    have hfirst : step
        ((divideFixedBlock target temp divisor).instantiate offset)
        ⟨offset + divisor, registers⟩ = some ⟨offset, middle⟩ := by
      simpa [middle] using step_of_lookup_increment
        (lookup_divide_group
          (target := target) (temp := temp) (offset := offset) hdivisor)
    refine ⟨middle.get target % divisor, divideResult target temp divisor middle,
      Nat.mod_lt _ hdivisor, ?_⟩
    exact (Relation.ReflTransGen.single (by simpa using hfirst)).trans
      (divideFixed_reaches hne hdivisor offset middle)
  have hlower : divisor < localState := by omega
  rcases division_above_group_cases hdivisor hlower hlocal with
    ⟨remainder, hremainder, hentry | hwork⟩
  · subst localState
    exact ⟨remainder, transferResult temp target registers, hremainder,
      transfer_reaches_of_lookup
        (lookup_divide_transfer_entry
          (target := target) (temp := temp) (offset := offset) hremainder)
        (lookup_divide_transfer_work
          (target := target) (temp := temp) (offset := offset) hremainder)
        (Ne.symm hne) registers⟩
  · subst localState
    let middle := registers.increment target
    have hfirst : step
        ((divideFixedBlock target temp divisor).instantiate offset)
        ⟨offset + divisionTransferWork divisor remainder, registers⟩ =
          some ⟨offset + divisionTransferEntry divisor remainder, middle⟩ := by
      simpa [middle] using step_of_lookup_increment
        (lookup_divide_transfer_work
          (target := target) (temp := temp) (offset := offset) hremainder)
    refine ⟨remainder, transferResult temp target middle, hremainder,
      (Relation.ReflTransGen.single (by simpa using hfirst)).trans ?_⟩
    exact transfer_reaches_of_lookup
      (lookup_divide_transfer_entry
        (target := target) (temp := temp) (offset := offset) hremainder)
      (lookup_divide_transfer_work
        (target := target) (temp := temp) (offset := offset) hremainder)
      (Ne.symm hne) middle

end CounterArithmeticLiveness
end Hooper
end Kari
end LeanWang
