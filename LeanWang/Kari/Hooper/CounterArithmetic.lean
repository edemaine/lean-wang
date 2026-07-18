/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.CounterProgram

/-!
# Relocatable arithmetic programs for Hooper counters

This module implements the fixed-constant arithmetic used by the numeric
stack encoding.  Every macro is an explicit finite counter program.  Local
source states are natural numbers in a bounded interval, and relocation is
provided by `CounterProgram.Block.instantiate`.

The first macro adds a fixed natural-number constant.  The subsequent macros
multiply and divide by a fixed positive constant while using a distinct
temporary register.  Their correctness statements use
`StateTransition.Reaches`, so they can be spliced directly into the finite
counter program compiled from a source machine.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterArithmetic

open CounterMachine CounterProgram

/-! ## Dense finite blocks -/

/-- A finite program with one rule at every source state below `sourceCount`.
The target states in `instruction` need not lie in that interval. -/
def denseProgram (sourceCount : Nat) (instruction : State → Instruction) : Program :=
  (List.range sourceCount).map fun state => (state, instruction state)

@[simp]
theorem sourceStates_denseProgram (sourceCount : Nat)
    (instruction : State → Instruction) :
    sourceStates (denseProgram sourceCount instruction) = List.range sourceCount := by
  rw [denseProgram, sourceStates, List.map_map]
  change List.map (fun state => state) (List.range sourceCount) =
    List.range sourceCount
  induction List.range sourceCount with
  | nil => rfl
  | cons state states ih => simp only [List.map_cons, ih]

theorem denseProgram_deterministic (sourceCount : Nat)
    (instruction : State → Instruction) :
    Deterministic (denseProgram sourceCount instruction) := by
  rw [Deterministic, sourceStates_denseProgram]
  exact List.nodup_range

/-- A dense source prefix packaged with an independently chosen allocation
width.  Division uses a width larger than the source prefix to reserve its
several remainder exits. -/
def denseBlock (sourceCount width : Nat) (instruction : State → Instruction) :
    Block where
  width := width
  code := denseProgram sourceCount instruction

theorem denseBlock_wellFormed {sourceCount width : Nat}
    (hwidth : sourceCount ≤ width) (instruction : State → Instruction) :
    (denseBlock sourceCount width instruction).WellFormed := by
  constructor
  · exact denseProgram_deterministic sourceCount instruction
  · intro state hstate
    simp only [denseBlock, sourceStates_denseProgram, List.mem_range] at hstate
    exact lt_of_lt_of_le hstate hwidth

/-- Lookup at a relocated source of a dense block. -/
theorem lookup_denseBlock_instantiate
    {sourceCount width offset localState : Nat}
    {instruction : State → Instruction}
    (hlocal : localState < sourceCount) :
    lookupInstruction
        ((denseBlock sourceCount width instruction).instantiate offset)
        (offset + localState) =
      some (relocateInstruction offset (instruction localState)) := by
  apply (lookupInstruction_eq_some_iff_of_deterministic
    (deterministic_relocate
      (denseProgram_deterministic sourceCount instruction) offset)).2
  simp only [Block.instantiate, relocate, List.mem_map]
  refine ⟨(localState, instruction localState), ?_, ?_⟩
  · simp [denseProgram, hlocal]
  · rfl

/-! ## Adding a fixed constant -/

/-- Replace one register by its old value plus a fixed constant. -/
def addResult (register : Register) (amount : Nat)
    (registers : Registers) : Registers :=
  registers.set register (registers.get register + amount)

@[simp]
theorem addResult_zero (register : Register) (registers : Registers) :
    addResult register 0 registers = registers := by
  cases register <;> cases registers <;> simp [addResult, Registers.get, Registers.set]

theorem addResult_increment (register : Register) (amount : Nat)
    (registers : Registers) :
    addResult register amount (registers.increment register) =
      addResult register (amount + 1) registers := by
  cases register <;> cases registers <;>
    simp [addResult, Registers.increment, Registers.get, Registers.set] <;> omega

@[simp]
theorem addResult_get_same (register : Register) (amount : Nat)
    (registers : Registers) :
    (addResult register amount registers).get register =
      registers.get register + amount := by
  simp [addResult]

theorem addResult_get_other {register other : Register} (hne : other ≠ register)
    (amount : Nat) (registers : Registers) :
    (addResult register amount registers).get other = registers.get other := by
  simp [addResult, Registers.get_set_other registers hne]

/-- The local program at state `i` increments the chosen register and moves to
`i + 1`.  Thus state `amount` is the unique fall-through exit. -/
def addFixedInstruction (register : Register) (state : State) : Instruction :=
  .increment register (state + 1)

/-- Relocatable block that adds `amount` to `register`. -/
def addFixedBlock (register : Register) (amount : Nat) : Block :=
  denseBlock amount amount (addFixedInstruction register)

theorem addFixedBlock_wellFormed (register : Register) (amount : Nat) :
    (addFixedBlock register amount).WellFormed := by
  exact denseBlock_wellFormed (Nat.le_refl amount) _

@[simp]
theorem addFixedBlock_width (register : Register) (amount : Nat) :
    (addFixedBlock register amount).width = amount :=
  rfl

private theorem addFixed_reaches_aux
    (register : Register) (total offset : Nat)
    (i remaining : Nat) (htotal : i + remaining = total)
    (registers : Registers) :
    StateTransition.Reaches
      (step ((addFixedBlock register total).instantiate offset))
      ⟨offset + i, registers⟩
      ⟨offset + total, addResult register remaining registers⟩ := by
  induction remaining generalizing i registers with
  | zero =>
      rw [Nat.add_zero] at htotal
      subst total
      simp only [addResult_zero]
      exact Relation.ReflTransGen.refl
  | succ remaining ih =>
      have hi : i < total := by omega
      have hlookup :
          lookupInstruction
              ((addFixedBlock register total).instantiate offset)
              (offset + i) =
            some (.increment register (offset + (i + 1))) := by
        simpa [addFixedBlock, addFixedInstruction] using
          (lookup_denseBlock_instantiate
            (width := total) (offset := offset)
            (instruction := addFixedInstruction register) hi)
      have hstep :
          step ((addFixedBlock register total).instantiate offset)
              ⟨offset + i, registers⟩ =
            some ⟨offset + (i + 1), registers.increment register⟩ :=
        step_of_lookup_increment hlookup
      have htail := ih (i + 1) (by omega) (registers.increment register)
      rw [addResult_increment] at htail
      exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
        (by simpa using hstep) |>.trans htail

/-- Exact correctness of the relocated fixed-addition block. -/
theorem addFixed_reaches (register : Register) (amount offset : Nat)
    (registers : Registers) :
    StateTransition.Reaches
      (step ((addFixedBlock register amount).instantiate offset))
      ⟨offset, registers⟩
      ⟨offset + amount, addResult register amount registers⟩ := by
  simpa using
    addFixed_reaches_aux register amount offset 0 amount (by omega) registers

/-! ## A transfer loop inside a larger finite program -/

/-- The semantic transfer proof depends only on the two advertised lookup
entries.  This version lets multiplication and division embed a transfer loop
inside their larger dense programs. -/
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

/-! ## Multiplication by a fixed positive constant -/

/-- Local instruction table for multiplication by `factor`.

State `0` tests and decrements the value register.  States `1, ..., factor`
add `factor` to the temporary register and return to state `0`.  Once the
value is zero, states `factor + 1` and `factor + 2` transfer the accumulated
temporary value back; `factor + 3` is the fall-through exit. -/
def multiplyFixedInstruction (target temp : Register) (factor : Nat)
    (state : State) : Instruction :=
  if state = 0 then
    .decrement target (factor + 1) 1
  else if state ≤ factor then
    .increment temp (if state = factor then 0 else state + 1)
  else if state = factor + 1 then
    .decrement temp (factor + 3) (factor + 2)
  else
    .increment target (factor + 1)

/-- Relocatable multiplication block.  Its correctness theorem assumes a
positive factor and a distinct temporary register. -/
def multiplyFixedBlock (target temp : Register) (factor : Nat) : Block :=
  denseBlock (factor + 3) (factor + 3)
    (multiplyFixedInstruction target temp factor)

theorem multiplyFixedBlock_wellFormed
    (target temp : Register) (factor : Nat) :
    (multiplyFixedBlock target temp factor).WellFormed := by
  exact denseBlock_wellFormed (Nat.le_refl (factor + 3)) _

@[simp]
theorem multiplyFixedBlock_width
    (target temp : Register) (factor : Nat) :
    (multiplyFixedBlock target temp factor).width = factor + 3 :=
  rfl

/-- General multiplication result: a preexisting temporary value is added to
the product before the temporary register is cleared. -/
def multiplyResult (target temp : Register) (factor : Nat)
    (registers : Registers) : Registers :=
  (registers.set temp 0).set target
    (registers.get temp + factor * registers.get target)

/-- Clean multiplication result when the temporary register starts at zero. -/
def multiplyCleanResult (target temp : Register) (factor : Nat)
    (registers : Registers) : Registers :=
  (registers.set temp 0).set target (factor * registers.get target)

theorem multiplyResult_eq_clean_of_temp_zero
    {target temp : Register} {registers : Registers}
    (factor : Nat) (htemp : registers.get temp = 0) :
    multiplyResult target temp factor registers =
      multiplyCleanResult target temp factor registers := by
  simp [multiplyResult, multiplyCleanResult, htemp]

@[simp]
theorem multiplyCleanResult_get_target
    {target temp : Register} (hne : target ≠ temp)
    (factor : Nat) (registers : Registers) :
    (multiplyCleanResult target temp factor registers).get target =
      factor * registers.get target := by
  simp [multiplyCleanResult]

@[simp]
theorem multiplyCleanResult_get_temp
    {target temp : Register} (hne : target ≠ temp)
    (factor : Nat) (registers : Registers) :
    (multiplyCleanResult target temp factor registers).get temp = 0 := by
  simp [multiplyCleanResult, Registers.get_set_other _ (Ne.symm hne)]

private theorem transferResult_eq_multiplyResult_of_target_zero
    {target temp : Register} (hne : target ≠ temp)
    (factor : Nat) {registers : Registers}
    (hzero : registers.get target = 0) :
    transferResult temp target registers =
      multiplyResult target temp factor registers := by
  cases target <;> cases temp <;>
    simp_all [transferResult, multiplyResult, Registers.get, Registers.set]

private theorem factor_mul_pred_add (factor n : Nat) (hpositive : 0 < n) :
    factor + factor * (n - 1) = factor * n := by
  have hn : n = (n - 1) + 1 := by omega
  conv_rhs => rw [hn, Nat.mul_add]
  simp [Nat.add_comm]

private theorem multiplyResult_after_loop
    {target temp : Register} (hne : target ≠ temp)
    (factor : Nat) {registers : Registers}
    (hpositive : 0 < registers.get target) :
    multiplyResult target temp factor
        (addResult temp factor (registers.decrement target)) =
      multiplyResult target temp factor registers := by
  have hmul := factor_mul_pred_add factor (registers.get target) hpositive
  cases target <;> cases temp <;>
    simp_all [multiplyResult, addResult, Registers.get, Registers.set,
      Registers.decrement] <;> omega

theorem lookup_multiply_entry
    {target temp : Register} {factor offset : Nat} (hfactor : 0 < factor) :
    lookupInstruction
        ((multiplyFixedBlock target temp factor).instantiate offset) offset =
      some (.decrement target (offset + (factor + 1)) (offset + 1)) := by
  simpa [multiplyFixedBlock, multiplyFixedInstruction] using
    (lookup_denseBlock_instantiate
      (width := factor + 3) (offset := offset)
      (instruction := multiplyFixedInstruction target temp factor)
      (show 0 < factor + 3 by omega))

theorem lookup_multiply_add
    {target temp : Register} {factor offset i : Nat}
    (hi : i < factor) :
    lookupInstruction
        ((multiplyFixedBlock target temp factor).instantiate offset)
        (offset + (i + 1)) =
      some (.increment temp
        (offset + (if i + 1 = factor then 0 else i + 2))) := by
  have hlocal : i + 1 < factor + 3 := by omega
  have hnonzero : i + 1 ≠ 0 := by omega
  have hle : i + 1 ≤ factor := by omega
  simpa [multiplyFixedBlock, multiplyFixedInstruction,
    hnonzero, hle] using
    (lookup_denseBlock_instantiate
      (width := factor + 3) (offset := offset)
      (instruction := multiplyFixedInstruction target temp factor) hlocal)

theorem lookup_multiply_transfer_entry
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

theorem lookup_multiply_transfer_work
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

/-- Local state reached while adding one factor-sized group to the temporary
register. -/
private def multiplyAddState (offset i remaining : Nat) : State :=
  if remaining = 0 then offset else offset + (i + 1)

private theorem multiply_addLoop_reaches_aux
    (target temp : Register) (factor offset : Nat)
    (i remaining : Nat) (htotal : i + remaining = factor)
    (registers : Registers) :
    StateTransition.Reaches
      (step ((multiplyFixedBlock target temp factor).instantiate offset))
      ⟨multiplyAddState offset i remaining, registers⟩
      ⟨offset, addResult temp remaining registers⟩ := by
  induction remaining generalizing i registers with
  | zero =>
      rw [addResult_zero]
      simp only [multiplyAddState, ↓reduceIte]
      exact Relation.ReflTransGen.refl
  | succ remaining ih =>
      have hi : i < factor := by omega
      have htarget :
          offset + (if i + 1 = factor then 0 else i + 2) =
            multiplyAddState offset (i + 1) remaining := by
        cases remaining with
        | zero => simp [multiplyAddState]
                  omega
        | succ remaining => simp [multiplyAddState]
                            omega
      have hlookup := lookup_multiply_add
        (target := target) (temp := temp) (offset := offset) hi
      rw [htarget] at hlookup
      have hstep :
          step ((multiplyFixedBlock target temp factor).instantiate offset)
              ⟨multiplyAddState offset i (remaining + 1), registers⟩ =
            some ⟨multiplyAddState offset (i + 1) remaining,
              registers.increment temp⟩ := by
        have hstate : multiplyAddState offset i (remaining + 1) =
            offset + (i + 1) := by simp [multiplyAddState]
        rw [hstate]
        exact step_of_lookup_increment hlookup
      have htail := ih (i + 1) (by omega) (registers.increment temp)
      rw [addResult_increment] at htail
      exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
        (by simpa using hstep) |>.trans htail

private theorem multiply_addLoop_reaches
    (target temp : Register) (factor offset : Nat) (hfactor : 0 < factor)
    (registers : Registers) :
    StateTransition.Reaches
      (step ((multiplyFixedBlock target temp factor).instantiate offset))
      ⟨offset + 1, registers⟩
      ⟨offset, addResult temp factor registers⟩ := by
  have h := multiply_addLoop_reaches_aux target temp factor offset
    0 factor (by omega) registers
  simpa [multiplyAddState, hfactor.ne'] using h

/-- General correctness of fixed multiplication.  The theorem is slightly
stronger than the clean-stack interface: it permits a nonzero initial
temporary value and adds it to the product before clearing the temporary. -/
theorem multiplyFixed_reaches
    {target temp : Register} (hne : target ≠ temp)
    {factor : Nat} (hfactor : 0 < factor) (offset : Nat)
    (registers : Registers) :
    StateTransition.Reaches
      (step ((multiplyFixedBlock target temp factor).instantiate offset))
      ⟨offset, registers⟩
      ⟨offset + (factor + 3), multiplyResult target temp factor registers⟩ := by
  generalize hn : registers.get target = n
  induction n generalizing registers with
  | zero =>
      have hentry := lookup_multiply_entry
        (target := target) (temp := temp) (offset := offset) hfactor
      have hfirst :
          step ((multiplyFixedBlock target temp factor).instantiate offset)
              ⟨offset, registers⟩ =
            some ⟨offset + (factor + 1), registers⟩ :=
        step_of_lookup_decrement_zero hentry hn
      have htransfer := transfer_reaches_of_lookup
        (lookup_multiply_transfer_entry
          (target := target) (temp := temp) (factor := factor) (offset := offset))
        (lookup_multiply_transfer_work
          (target := target) (temp := temp) (factor := factor) (offset := offset))
        (Ne.symm hne) registers
      have hresult := transferResult_eq_multiplyResult_of_target_zero
        hne factor hn
      rw [hresult] at htransfer
      exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
        (by simpa using hfirst) |>.trans htransfer
  | succ n ih =>
      have hpositive : 0 < registers.get target := by omega
      let afterDecrement := registers.decrement target
      have hentry := lookup_multiply_entry
        (target := target) (temp := temp) (offset := offset) hfactor
      have hfirst :
          step ((multiplyFixedBlock target temp factor).instantiate offset)
              ⟨offset, registers⟩ =
            some ⟨offset + 1, afterDecrement⟩ := by
        simpa [afterDecrement] using
          step_of_lookup_decrement_positive hentry hpositive
      have hadd := multiply_addLoop_reaches target temp factor offset hfactor
        afterDecrement
      let afterLoop := addResult temp factor afterDecrement
      have htargetAfter : afterLoop.get target = n := by
        dsimp [afterLoop, afterDecrement]
        rw [addResult_get_other hne]
        simp [hn]
      have htail := ih afterLoop htargetAfter
      have hresult : multiplyResult target temp factor afterLoop =
          multiplyResult target temp factor registers := by
        exact multiplyResult_after_loop hne factor hpositive
      rw [hresult] at htail
      have hprefix : StateTransition.Reaches
          (step ((multiplyFixedBlock target temp factor).instantiate offset))
          ⟨offset, registers⟩ ⟨offset + 1, afterDecrement⟩ :=
        Relation.ReflTransGen.tail Relation.ReflTransGen.refl
          (by simpa using hfirst)
      have hadd' : StateTransition.Reaches
          (step ((multiplyFixedBlock target temp factor).instantiate offset))
          ⟨offset + 1, afterDecrement⟩ ⟨offset, afterLoop⟩ := by
        simpa [afterLoop] using hadd
      exact (hprefix.trans hadd').trans htail

/-- Clean fixed multiplication: with a zero temporary register, the target is
multiplied by `factor` and the temporary register is again zero at the exit. -/
theorem multiplyFixed_reaches_of_temp_zero
    {target temp : Register} (hne : target ≠ temp)
    {factor : Nat} (hfactor : 0 < factor) (offset : Nat)
    (registers : Registers) (htemp : registers.get temp = 0) :
    StateTransition.Reaches
      (step ((multiplyFixedBlock target temp factor).instantiate offset))
      ⟨offset, registers⟩
      ⟨offset + (factor + 3),
        multiplyCleanResult target temp factor registers⟩ := by
  have h := multiplyFixed_reaches hne hfactor offset registers
  rw [multiplyResult_eq_clean_of_temp_zero factor htemp] at h
  exact h

/-! ## Division by a fixed positive constant -/

/-- First local state of the transfer loop selected by remainder `remainder`. -/
def divisionTransferEntry (divisor remainder : Nat) : State :=
  divisor + 1 + remainder + remainder

/-- Work state of the transfer loop selected by `remainder`. -/
def divisionTransferWork (divisor remainder : Nat) : State :=
  divisionTransferEntry divisor remainder + 1

/-- Local exit encoding `remainder`.  These states have no source rules. -/
def divisionExit (divisor remainder : Nat) : State :=
  divisor + divisor + divisor + 1 + remainder

/-- Number of source states in the division program. -/
def divisionSourceCount (divisor : Nat) : Nat :=
  divisor + divisor + divisor + 1

/-- Allocation width, including the `divisor` reserved remainder exits. -/
def divisionWidth (divisor : Nat) : Nat :=
  divisor + divisor + divisor + divisor + 1

/-- Local instruction table for quotient/remainder division.

States below `divisor` tentatively subtract one digit.  State `divisor`
records a complete group in `temp` and repeats.  A failed tentative
subtraction chooses one of `divisor` two-state transfer loops, whose exit
state records how many decrements succeeded in the final incomplete group. -/
def divideFixedInstruction (target temp : Register) (divisor : Nat)
    (state : State) : Instruction :=
  if state < divisor then
    .decrement target (divisionTransferEntry divisor state) (state + 1)
  else if state = divisor then
    .increment temp 0
  else
    let index := state - (divisor + 1)
    let remainder := index / 2
    if index % 2 = 0 then
      .decrement temp (divisionExit divisor remainder) (state + 1)
    else
      .increment target (state - 1)

/-- Division block with several reserved exits.  Source rules occupy the
prefix `[0, 3 * divisor + 1)`; the remainder exits occupy the final
`divisor` states of its allocation. -/
def divideFixedBlock (target temp : Register) (divisor : Nat) : Block :=
  denseBlock (divisionSourceCount divisor) (divisionWidth divisor)
    (divideFixedInstruction target temp divisor)

theorem divideFixedBlock_wellFormed
    (target temp : Register) (divisor : Nat) :
    (divideFixedBlock target temp divisor).WellFormed := by
  apply denseBlock_wellFormed
  simp [divisionSourceCount, divisionWidth]

@[simp]
theorem divideFixedBlock_width
    (target temp : Register) (divisor : Nat) :
    (divideFixedBlock target temp divisor).width = divisionWidth divisor :=
  rfl

theorem divisionExit_lt_width {divisor remainder : Nat}
    (hremainder : remainder < divisor) :
    divisionExit divisor remainder < divisionWidth divisor := by
  have h := Nat.add_lt_add_left hremainder
    (divisor + divisor + divisor + 1)
  simpa [divisionExit, divisionWidth, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

theorem divisionSourceCount_le_exit (divisor remainder : Nat) :
    divisionSourceCount divisor ≤ divisionExit divisor remainder := by
  simp [divisionSourceCount, divisionExit]

theorem divisionExit_not_source {divisor remainder : Nat}
    {target temp : Register}
    (hremainder : remainder < divisor) :
    divisionExit divisor remainder ∉
      sourceStates ((divideFixedBlock target temp divisor).code) := by
  change divisionExit divisor remainder ∉
    sourceStates (denseProgram (divisionSourceCount divisor)
      (divideFixedInstruction target temp divisor))
  rw [sourceStates_denseProgram, List.mem_range]
  exact not_lt_of_ge (divisionSourceCount_le_exit divisor remainder)

/-- General division result.  A preexisting temporary value is added to the
quotient before the temporary is cleared. -/
def divideResult (target temp : Register) (divisor : Nat)
    (registers : Registers) : Registers :=
  (registers.set temp 0).set target
    (registers.get temp + registers.get target / divisor)

/-- Clean quotient result for a temporary register initially equal to zero. -/
def divideCleanResult (target temp : Register) (divisor : Nat)
    (registers : Registers) : Registers :=
  (registers.set temp 0).set target (registers.get target / divisor)

theorem divideResult_eq_clean_of_temp_zero
    {target temp : Register} {registers : Registers}
    (divisor : Nat) (htemp : registers.get temp = 0) :
    divideResult target temp divisor registers =
      divideCleanResult target temp divisor registers := by
  simp [divideResult, divideCleanResult, htemp]

@[simp]
theorem divideCleanResult_get_target
    {target temp : Register} (hne : target ≠ temp)
    (divisor : Nat) (registers : Registers) :
    (divideCleanResult target temp divisor registers).get target =
      registers.get target / divisor := by
  simp [divideCleanResult]

@[simp]
theorem divideCleanResult_get_temp
    {target temp : Register} (hne : target ≠ temp)
    (divisor : Nat) (registers : Registers) :
    (divideCleanResult target temp divisor registers).get temp = 0 := by
  simp [divideCleanResult, Registers.get_set_other _ (Ne.symm hne)]

theorem lookup_divide_main
    {target temp : Register} {divisor offset state : Nat}
    (hstate : state < divisor) :
    lookupInstruction
        ((divideFixedBlock target temp divisor).instantiate offset)
        (offset + state) =
      some (.decrement target
        (offset + divisionTransferEntry divisor state)
        (offset + (state + 1))) := by
  have hsource : state < divisionSourceCount divisor := by
    simp [divisionSourceCount]
    omega
  simpa [divideFixedBlock, divideFixedInstruction, hstate] using
    (lookup_denseBlock_instantiate
      (width := divisionWidth divisor) (offset := offset)
      (instruction := divideFixedInstruction target temp divisor) hsource)

theorem lookup_divide_group
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

theorem lookup_divide_transfer_entry
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

theorem lookup_divide_transfer_work
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

/-- Subtract a known-bounded amount from one register. -/
def subtractResult (register : Register) (amount : Nat)
    (registers : Registers) : Registers :=
  registers.set register (registers.get register - amount)

@[simp]
theorem subtractResult_zero (register : Register) (registers : Registers) :
    subtractResult register 0 registers = registers := by
  cases register <;> cases registers <;>
    simp [subtractResult, Registers.get, Registers.set]

@[simp]
theorem subtractResult_get_same (register : Register) (amount : Nat)
    (registers : Registers) :
    (subtractResult register amount registers).get register =
      registers.get register - amount := by
  simp [subtractResult]

theorem subtractResult_get_other {register other : Register}
    (hne : other ≠ register) (amount : Nat) (registers : Registers) :
    (subtractResult register amount registers).get other = registers.get other := by
  simp [subtractResult, Registers.get_set_other registers hne]

theorem subtractResult_decrement
    (register : Register) (amount : Nat) (registers : Registers)
    (hbound : amount + 1 ≤ registers.get register) :
    subtractResult register amount (registers.decrement register) =
      subtractResult register (amount + 1) registers := by
  cases register <;> cases registers <;>
    simp_all [subtractResult, Registers.get, Registers.set,
      Registers.decrement] <;> omega

private theorem division_decrement_reaches_aux
    (target temp : Register) (divisor offset : Nat)
    (start count : Nat) (hend : start + count ≤ divisor)
    (registers : Registers) (hcount : count ≤ registers.get target) :
    StateTransition.Reaches
      (step ((divideFixedBlock target temp divisor).instantiate offset))
      ⟨offset + start, registers⟩
      ⟨offset + (start + count), subtractResult target count registers⟩ := by
  induction count generalizing start registers with
  | zero =>
      rw [subtractResult_zero]
      simp only [Nat.add_zero]
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
      have hprefix : StateTransition.Reaches
          (step ((divideFixedBlock target temp divisor).instantiate offset))
          ⟨offset + start, registers⟩
          ⟨offset + (start + 1), afterDecrement⟩ :=
        Relation.ReflTransGen.tail Relation.ReflTransGen.refl
          (by simpa using hfirst)
      have hpath := hprefix.trans htail
      have hstate : offset + ((start + 1) + count) =
          offset + (start + (count + 1)) := by omega
      rw [← hstate]
      exact hpath

/-- Execute `count` successful tentative decrements from the division entry. -/
private theorem division_decrement_reaches
    (target temp : Register) (divisor offset count : Nat)
    (hcountDivisor : count ≤ divisor)
    (registers : Registers) (hcount : count ≤ registers.get target) :
    StateTransition.Reaches
      (step ((divideFixedBlock target temp divisor).instantiate offset))
      ⟨offset, registers⟩
      ⟨offset + count, subtractResult target count registers⟩ := by
  simpa using division_decrement_reaches_aux target temp divisor offset
    0 count (by omega) registers hcount

private theorem div_sub_add_one {n divisor : Nat}
    (hdivisor : 0 < divisor) (hle : divisor ≤ n) :
    (n - divisor) / divisor + 1 = n / divisor := by
  rw [← Nat.add_mul_div_left (n - divisor) 1 hdivisor]
  simp only [mul_one]
  rw [Nat.sub_add_cancel hle]

private theorem mod_sub {n divisor : Nat} (hle : divisor ≤ n) :
    (n - divisor) % divisor = n % divisor := by
  conv_rhs => rw [← Nat.sub_add_cancel hle]
  simpa using Nat.add_mul_mod_self_left (n - divisor) 1 divisor

private theorem transferResult_subtract_eq_divideResult_of_lt
    {target temp : Register} (hne : target ≠ temp)
    {divisor count : Nat} {registers : Registers}
    (hvalue : registers.get target = count) (hlt : count < divisor) :
    transferResult temp target (subtractResult target count registers) =
      divideResult target temp divisor registers := by
  have hdiv : count / divisor = 0 := Nat.div_eq_of_lt hlt
  cases target <;> cases temp <;>
    simp_all [transferResult, subtractResult, divideResult,
      Registers.get, Registers.set]

private theorem divideResult_after_group
    {target temp : Register} (hne : target ≠ temp)
    {divisor : Nat} (hdivisor : 0 < divisor)
    {registers : Registers} (hle : divisor ≤ registers.get target) :
    divideResult target temp divisor
        ((subtractResult target divisor registers).increment temp) =
      divideResult target temp divisor registers := by
  have hdiv := div_sub_add_one hdivisor hle
  cases target <;> cases temp <;>
    simp_all [divideResult, subtractResult, Registers.increment,
      Registers.get, Registers.set] <;> omega

/-- Exact quotient/remainder correctness of the relocated division block.
The quotient replaces `target`; a preexisting value of `temp` is added to it,
and `temp` is cleared.  The selected exit encodes the remainder. -/
theorem divideFixed_reaches
    {target temp : Register} (hne : target ≠ temp)
    {divisor : Nat} (hdivisor : 0 < divisor) (offset : Nat)
    (registers : Registers) :
    StateTransition.Reaches
      (step ((divideFixedBlock target temp divisor).instantiate offset))
      ⟨offset, registers⟩
      ⟨offset + divisionExit divisor (registers.get target % divisor),
        divideResult target temp divisor registers⟩ := by
  generalize hn : registers.get target = n
  induction n using Nat.strong_induction_on generalizing registers with
  | h n ih =>
      by_cases hsmall : n < divisor
      · have hdecrements := division_decrement_reaches
          target temp divisor offset n (Nat.le_of_lt hsmall) registers (by omega)
        let afterSubtract := subtractResult target n registers
        have hzero : afterSubtract.get target = 0 := by
          dsimp [afterSubtract]
          rw [subtractResult_get_same, hn]
          omega
        have hlookup := lookup_divide_main
          (target := target) (temp := temp) (offset := offset) hsmall
        have hfailure :
            step ((divideFixedBlock target temp divisor).instantiate offset)
                ⟨offset + n, afterSubtract⟩ =
              some ⟨offset + divisionTransferEntry divisor n,
                afterSubtract⟩ :=
          step_of_lookup_decrement_zero hlookup hzero
        have htransfer := transfer_reaches_of_lookup
          (lookup_divide_transfer_entry
            (target := target) (temp := temp) (offset := offset) hsmall)
          (lookup_divide_transfer_work
            (target := target) (temp := temp) (offset := offset) hsmall)
          (Ne.symm hne) afterSubtract
        have hresult : transferResult temp target afterSubtract =
            divideResult target temp divisor registers :=
          transferResult_subtract_eq_divideResult_of_lt hne hn hsmall
        rw [hresult] at htransfer
        have hmod : n % divisor = n := Nat.mod_eq_of_lt hsmall
        rw [hmod]
        have hdecrements' : StateTransition.Reaches
            (step ((divideFixedBlock target temp divisor).instantiate offset))
            ⟨offset, registers⟩ ⟨offset + n, afterSubtract⟩ := by
          simpa [afterSubtract] using hdecrements
        have hfailed : StateTransition.Reaches
            (step ((divideFixedBlock target temp divisor).instantiate offset))
            ⟨offset + n, afterSubtract⟩
            ⟨offset + divisionTransferEntry divisor n, afterSubtract⟩ :=
          Relation.ReflTransGen.tail Relation.ReflTransGen.refl
            (by simpa using hfailure)
        exact (hdecrements'.trans hfailed).trans htransfer
      · have hle : divisor ≤ n := Nat.le_of_not_gt hsmall
        have hdecrements := division_decrement_reaches
          target temp divisor offset divisor (Nat.le_refl divisor)
          registers (by omega)
        let afterSubtract := subtractResult target divisor registers
        let afterGroup := afterSubtract.increment temp
        have hgroupLookup := lookup_divide_group
          (target := target) (temp := temp) (offset := offset) hdivisor
        have hgroup :
            step ((divideFixedBlock target temp divisor).instantiate offset)
                ⟨offset + divisor, afterSubtract⟩ =
              some ⟨offset, afterGroup⟩ := by
          simpa [afterGroup] using step_of_lookup_increment hgroupLookup
        have htargetAfter : afterGroup.get target = n - divisor := by
          dsimp [afterGroup, afterSubtract]
          rw [Registers.get_increment_other _ hne,
            subtractResult_get_same, hn]
        have hsmaller : n - divisor < n := by omega
        have htail := ih (n - divisor) hsmaller afterGroup htargetAfter
        have hremainder : (n - divisor) % divisor = n % divisor :=
          mod_sub hle
        have hresult : divideResult target temp divisor afterGroup =
            divideResult target temp divisor registers :=
          divideResult_after_group hne hdivisor (by simpa [hn] using hle)
        rw [hremainder, hresult] at htail
        have hdecrements' : StateTransition.Reaches
            (step ((divideFixedBlock target temp divisor).instantiate offset))
            ⟨offset, registers⟩
            ⟨offset + divisor, afterSubtract⟩ := by
          simpa [afterSubtract] using hdecrements
        have hgroup' : StateTransition.Reaches
            (step ((divideFixedBlock target temp divisor).instantiate offset))
            ⟨offset + divisor, afterSubtract⟩ ⟨offset, afterGroup⟩ :=
          Relation.ReflTransGen.tail Relation.ReflTransGen.refl
            (by simpa using hgroup)
        exact (hdecrements'.trans hgroup').trans htail

/-- Clean division: if the temporary starts at zero, the target becomes the
quotient, the temporary is restored to zero, and the control-state exit is
the remainder. -/
theorem divideFixed_reaches_of_temp_zero
    {target temp : Register} (hne : target ≠ temp)
    {divisor : Nat} (hdivisor : 0 < divisor) (offset : Nat)
    (registers : Registers) (htemp : registers.get temp = 0) :
    StateTransition.Reaches
      (step ((divideFixedBlock target temp divisor).instantiate offset))
      ⟨offset, registers⟩
      ⟨offset + divisionExit divisor (registers.get target % divisor),
        divideCleanResult target temp divisor registers⟩ := by
  have h := divideFixed_reaches hne hdivisor offset registers
  rw [divideResult_eq_clean_of_temp_zero divisor htemp] at h
  exact h

/-- The remainder selected by division is always one of the reserved exits. -/
theorem divideFixed_remainder_lt
    {divisor : Nat} (hdivisor : 0 < divisor) (registers : Registers)
    (target : Register) :
    registers.get target % divisor < divisor :=
  Nat.mod_lt _ hdivisor

end CounterArithmetic
end Hooper
end Kari
end LeanWang
