/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Dynamics
import LeanWang.Kari.Hooper.CounterMachine
import LeanWang.Kari.Hooper.StackEncoding

/-!
# Deterministic counter programs and arithmetic blocks

This module is the executable program-building layer above `CounterMachine`.
It records the no-duplicate-source invariant needed to read association-list
membership as a transition theorem, supplies relocatable blocks whose local
states can be allocated in a fresh interval, and gives the first verified
arithmetic macro: transfer the contents of one register into another.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterProgram

open CounterMachine

/-- A counter program is deterministic when every control state occurs as a
source at most once. -/
def Deterministic (program : Program) : Prop :=
  (sourceStates program).Nodup

/-- Successful lookup always selects a rule that occurs in the program. -/
theorem rule_mem_of_lookupInstruction_eq_some
    {program : Program} {state : State} {instruction : Instruction}
    (h : lookupInstruction program state = some instruction) :
    (state, instruction) ∈ program := by
  induction program with
  | nil => simp at h
  | cons rule program ih =>
      rcases rule with ⟨source, headInstruction⟩
      by_cases hstate : state = source
      · subst source
        rw [lookupInstruction_cons_eq] at h
        cases Option.some.inj h
        simp
      · have htail :
            lookupInstruction program state = some instruction := by
          simpa [lookupInstruction, hstate] using h
        exact List.mem_cons_of_mem _ (ih htail)

/-- With unique source states, lookup is exactly rule membership. -/
theorem lookupInstruction_eq_some_iff_of_deterministic
    {program : Program} (hdet : Deterministic program)
    {state : State} {instruction : Instruction} :
    lookupInstruction program state = some instruction ↔
      (state, instruction) ∈ program := by
  constructor
  · exact rule_mem_of_lookupInstruction_eq_some
  · intro hmem
    induction program with
    | nil => simp at hmem
    | cons rule program ih =>
        rcases rule with ⟨source, headInstruction⟩
        simp only [Deterministic, sourceStates, List.map_cons,
          List.nodup_cons] at hdet
        rcases hdet with ⟨hsourceFresh, htailDet⟩
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htail
        · cases hhead
          exact lookupInstruction_cons_eq _ _ _
        · have hstate : state ≠ source := by
            intro heq
            apply hsourceFresh
            rw [← heq]
            exact List.mem_map.mpr ⟨(state, instruction), htail, rfl⟩
          rw [lookupInstruction_cons_ne hstate]
          exact ih htailDet htail

/-- Relocate the target-state part of the primitive-recursive instruction
code. -/
def relocateTargets (offset : State) :
    State ⊕ State × State → State ⊕ State × State
  | Sum.inl next => Sum.inl (offset + next)
  | Sum.inr (ifZero, ifPositive) =>
      Sum.inr (offset + ifZero, offset + ifPositive)

/-- Relocate every target of an instruction by a fixed state offset. -/
def relocateInstruction (offset : State) (instruction : Instruction) : Instruction :=
  Instruction.equivCode.symm
    ((Instruction.equivCode instruction).1,
      relocateTargets offset (Instruction.equivCode instruction).2)

theorem relocateTargets_primrec :
    Primrec fun input : State × (State ⊕ State × State) =>
      relocateTargets input.1 input.2 := by
  have hsum : Primrec fun input : State × (State ⊕ State × State) =>
      input.2 := Primrec.snd
  let onIncrement :
      State × (State ⊕ State × State) → State →
        State ⊕ State × State :=
    fun input next => Sum.inl (input.1 + next)
  let onDecrement :
      State × (State ⊕ State × State) → State × State →
        State ⊕ State × State :=
    fun input targets =>
      Sum.inr (input.1 + targets.1, input.1 + targets.2)
  have hincrement : Primrec₂ onIncrement := by
    exact (Primrec.sumInl (α := State) (β := State × State)).comp₂
      (Primrec.nat_add.comp₂
        (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
  have hdecrement : Primrec₂ onDecrement := by
    exact (Primrec.sumInr (α := State) (β := State × State)).comp₂
      (Primrec₂.pair.comp₂
        (Primrec.nat_add.comp₂
          (Primrec.fst.comp₂ Primrec₂.left)
          (Primrec.fst.comp₂ Primrec₂.right))
        (Primrec.nat_add.comp₂
          (Primrec.fst.comp₂ Primrec₂.left)
          (Primrec.snd.comp₂ Primrec₂.right)))
  have hcases := Primrec.sumCasesOn hsum hincrement hdecrement
  exact hcases.of_eq fun input => by
    rcases input with ⟨offset, next | targets⟩
    · rfl
    · rcases targets with ⟨ifZero, ifPositive⟩
      rfl

theorem relocateInstruction_primrec :
    Primrec fun input : State × Instruction =>
      relocateInstruction input.1 input.2 := by
  have hcode : Primrec fun input : State × Instruction =>
      Instruction.equivCode input.2 :=
    (Primrec.of_equiv (e := Instruction.equivCode)).comp Primrec.snd
  have htargets : Primrec fun input : State × Instruction =>
      relocateTargets input.1 (Instruction.equivCode input.2).2 :=
    relocateTargets_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.snd.comp hcode))
  have hresultCode : Primrec fun input : State × Instruction =>
      ((Instruction.equivCode input.2).1,
        relocateTargets input.1 (Instruction.equivCode input.2).2) :=
    Primrec.pair (Primrec.fst.comp hcode) htargets
  exact (Primrec.of_equiv_symm (e := Instruction.equivCode)).comp hresultCode

@[simp]
theorem relocateInstruction_increment (offset : State)
    (register : Register) (next : State) :
    relocateInstruction offset (.increment register next) =
      .increment register (offset + next) :=
  rfl

@[simp]
theorem relocateInstruction_decrement (offset : State)
    (register : Register) (ifZero ifPositive : State) :
    relocateInstruction offset (.decrement register ifZero ifPositive) =
      .decrement register (offset + ifZero) (offset + ifPositive) :=
  rfl

/-- Relocate a rule, including both its source and all of its targets. -/
def relocateRule (offset : State) (rule : Rule) : Rule :=
  (offset + rule.1, relocateInstruction offset rule.2)

theorem relocateRule_primrec :
    Primrec fun input : State × Rule =>
      relocateRule input.1 input.2 := by
  apply Primrec.pair
  · exact Primrec₂.comp Primrec.nat_add Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  · exact relocateInstruction_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))

/-- Relocate an entire program into the interval beginning at `offset`. -/
def relocate (offset : State) (program : Program) : Program :=
  program.map (relocateRule offset)

theorem relocate_primrec :
    Primrec fun input : State × Program => relocate input.1 input.2 := by
  have hrule : Primrec₂ fun input : State × Program =>
      fun rule : Rule => relocateRule input.1 rule :=
    (Primrec.to₂ relocateRule_primrec).comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  exact Primrec.list_map Primrec.snd hrule

theorem relocate_computable :
    Computable fun input : State × Program => relocate input.1 input.2 :=
  relocate_primrec.to_comp

@[simp]
theorem sourceStates_relocate (offset : State) (program : Program) :
    sourceStates (relocate offset program) =
      (sourceStates program).map (offset + ·) := by
  induction program with
  | nil => rfl
  | cons rule program ih =>
      simp [relocate, relocateRule, sourceStates, ih]

@[simp]
theorem sourceStates_append (first second : Program) :
    sourceStates (first ++ second) =
      sourceStates first ++ sourceStates second := by
  simp [sourceStates]

/-- Relocation preserves unique source states. -/
theorem deterministic_relocate {program : Program}
    (hdet : Deterministic program) (offset : State) :
    Deterministic (relocate offset program) := by
  rw [Deterministic, sourceStates_relocate]
  exact hdet.map fun _ _ h => Nat.add_left_cancel h

/-- Every relocated source is the offset plus a source of the local program. -/
theorem mem_sourceStates_relocate_iff
    {offset state : State} {program : Program} :
    state ∈ sourceStates (relocate offset program) ↔
      ∃ localState, localState ∈ sourceStates program ∧
        state = offset + localState := by
  rw [sourceStates_relocate, List.mem_map]
  constructor
  · rintro ⟨localState, hlocal, rfl⟩
    exact ⟨localState, hlocal, rfl⟩
  · rintro ⟨localState, hlocal, rfl⟩
    exact ⟨localState, hlocal, rfl⟩

/-- A block uses canonical local states: `0` is its entry, `width` is its
fall-through exit, and all owned source states should be below `width`. -/
structure Block where
  width : Nat
  code : Program

namespace Block

/-- The semantic well-formedness invariant for a local block. -/
def WellFormed (block : Block) : Prop :=
  Deterministic block.code ∧
    ∀ state ∈ sourceStates block.code, state < block.width

/-- Place a local block at a fresh global-state offset. -/
def instantiate (offset : State) (block : Block) : Program :=
  relocate offset block.code

/-- Sequential composition.  The second entry is relocated to the first
exit, and the combined exit is the sum of the two widths. -/
def append (first second : Block) : Block where
  width := first.width + second.width
  code := first.code ++ relocate first.width second.code

/-- The instantiated source states lie in the half-open fresh interval owned
by the block. -/
theorem source_mem_instantiate
    {block : Block} (hblock : block.WellFormed)
    {offset state : State}
    (hstate : state ∈ sourceStates (block.instantiate offset)) :
    offset ≤ state ∧ state < offset + block.width := by
  rcases (mem_sourceStates_relocate_iff.mp hstate) with
    ⟨localState, hlocal, rfl⟩
  constructor
  · exact Nat.le_add_right offset localState
  · exact Nat.add_lt_add_left (hblock.2 localState hlocal) offset

/-- Sequential composition preserves deterministic, interval-owned source
states. -/
theorem wellFormed_append {first second : Block}
    (hfirst : first.WellFormed) (hsecond : second.WellFormed) :
    (first.append second).WellFormed := by
  constructor
  · rw [Deterministic]
    simp only [append, sourceStates_append, sourceStates_relocate]
    have hsecondNodup :
        ((sourceStates second.code).map (first.width + ·)).Nodup :=
      hsecond.1.map fun _ _ h => Nat.add_left_cancel h
    apply List.Nodup.append hfirst.1 hsecondNodup
    rw [List.disjoint_iff_ne]
    intro left hleft right hright heq
    have hleftBound : left < first.width := hfirst.2 left hleft
    rcases List.mem_map.mp hright with ⟨localState, hlocal, rfl⟩
    exact (Nat.ne_of_lt (lt_of_lt_of_le hleftBound
      (Nat.le_add_right first.width localState))) heq
  · intro state hstate
    simp only [append, sourceStates_append, List.mem_append,
      sourceStates_relocate] at hstate
    change state < first.width + second.width
    rcases hstate with hfirstState | hsecondState
    · exact lt_of_lt_of_le (hfirst.2 state hfirstState)
        (Nat.le_add_right first.width second.width)
    · rcases List.mem_map.mp hsecondState with
        ⟨localState, hlocal, rfl⟩
      exact Nat.add_lt_add_left (hsecond.2 localState hlocal) first.width

/-- Concatenating the underlying finite rule lists is computable.  This is
the executable operation used by the block assembler after fresh-state
relocation. -/
theorem codeAppend_computable :
    Computable₂ ((· ++ ·) : Program → Program → Program) :=
  Computable.list_append

end Block

/-- The two-instruction loop that transfers `source` into `target`.

State `entry` tests/decrements the source.  On a positive source it visits
`work`, increments the target, and returns to `entry`; on zero it exits.
-/
def transferProgram (entry work exit : State)
    (source target : Register) : Program :=
  [ (entry, .decrement source exit work),
    (work, .increment target entry) ]

theorem transferProgram_deterministic
    {entry work exit : State} {source target : Register}
    (hentryWork : entry ≠ work) :
    Deterministic (transferProgram entry work exit source target) := by
  simp [Deterministic, transferProgram, sourceStates, hentryWork]

/-- Canonical local transfer block: entry `0`, work state `1`, exit `2`. -/
def transferBlock (source target : Register) : Block where
  width := 2
  code := transferProgram 0 1 2 source target

theorem transferBlock_wellFormed (source target : Register) :
    (transferBlock source target).WellFormed := by
  constructor
  · exact transferProgram_deterministic (by decide)
  · intro state hstate
    change state < 2
    simp [transferBlock, transferProgram, sourceStates] at hstate
    rcases hstate with rfl | rfl <;> decide

@[simp]
theorem transferBlock_instantiate (offset : State)
    (source target : Register) :
    (transferBlock source target).instantiate offset =
      transferProgram offset (offset + 1) (offset + 2) source target := by
  simp [transferBlock, Block.instantiate, relocate, relocateRule,
    transferProgram]

/-- Register tuple produced by a complete transfer. -/
def transferResult (source target : Register) (registers : Registers) : Registers :=
  (registers.set source 0).set target
    (registers.get target + registers.get source)

theorem transferResult_eq_self_of_source_zero
    {source target : Register} (hne : source ≠ target)
    {registers : Registers} (hzero : registers.get source = 0) :
    transferResult source target registers = registers := by
  cases registers
  cases source <;> cases target <;>
    simp_all [transferResult, Registers.get, Registers.set]

theorem transferResult_pair
    {source target : Register} (hne : source ≠ target)
    {registers : Registers} (hpositive : 0 < registers.get source) :
    transferResult source target
        ((registers.decrement source).increment target) =
      transferResult source target registers := by
  cases source <;> cases target <;>
    simp_all [transferResult, Registers.get, Registers.set,
      Registers.decrement, Registers.increment] <;> omega

/-- Exact register-level correctness of the transfer loop. -/
theorem transfer_reaches
    {entry work exit : State} {source target : Register}
    (hentryWork : entry ≠ work) (hsourceTarget : source ≠ target)
    (registers : Registers) :
    StateTransition.Reaches
      (step (transferProgram entry work exit source target))
      ⟨entry, registers⟩
      ⟨exit, transferResult source target registers⟩ := by
  generalize hn : registers.get source = n
  induction n generalizing registers with
  | zero =>
      have hresult : transferResult source target registers = registers :=
        transferResult_eq_self_of_source_zero hsourceTarget hn
      rw [hresult]
      apply Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      simp [transferProgram, step, lookupInstruction, hn]
  | succ n ih =>
      have hpositive : 0 < registers.get source := by omega
      let afterDecrement := registers.decrement source
      let afterPair := afterDecrement.increment target
      have hsourceAfter : afterPair.get source = n := by
        dsimp [afterPair, afterDecrement]
        rw [Registers.get_increment_other
          (registers.decrement source) hsourceTarget]
        simp [hn]
      have hfirst :
          step (transferProgram entry work exit source target)
              ⟨entry, registers⟩ =
            some ⟨work, afterDecrement⟩ := by
        simp [transferProgram, step, lookupInstruction, hpositive.ne',
          afterDecrement]
      have hsecond :
          step (transferProgram entry work exit source target)
              ⟨work, afterDecrement⟩ =
            some ⟨entry, afterPair⟩ := by
        simp [transferProgram, step, lookupInstruction, hentryWork,
          Ne.symm hentryWork,
          afterPair]
      have hprefix :
          StateTransition.Reaches
            (step (transferProgram entry work exit source target))
            ⟨entry, registers⟩ ⟨entry, afterPair⟩ :=
        Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
            (by simpa using hfirst))
          (by simpa using hsecond)
      have htail := ih afterPair hsourceAfter
      have hresult :
          transferResult source target afterPair =
            transferResult source target registers := by
        exact transferResult_pair hsourceTarget hpositive
      rw [hresult] at htail
      exact hprefix.trans htail

/-- When the exit is not one of the two owned states, the standalone transfer
program halts immediately after reaching its advertised result. -/
theorem transfer_exit_halts
    {entry work exit : State} {source target : Register}
    (hexitEntry : exit ≠ entry) (hexitWork : exit ≠ work)
    (registers : Registers) :
    step (transferProgram entry work exit source target)
      ⟨exit, transferResult source target registers⟩ = none := by
  simp [transferProgram, step, lookupInstruction, hexitEntry, hexitWork]

end CounterProgram
end Hooper
end Kari
end LeanWang
