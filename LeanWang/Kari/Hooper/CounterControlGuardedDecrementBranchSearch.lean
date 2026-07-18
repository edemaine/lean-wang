/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedDecrementEntry
import LeanWang.Kari.Hooper.CounterControlGenuineCoordinates

/-!
# Search entries selected by a guarded decrement branch

The two direct branch rules of a conditional decrement both return to the
tested boundary and enter a generated search whose target is already under
the head.  Thus both new searches have exact distance zero.  The positive
branch additionally has a blank immediately behind its entry and is a
`GuardedSearch`; the zero branch has the preceding boundary there and is
necessarily only a `GenuineSearch`.

This module packages those exact entries while retaining the original
guarded route trace.  That trace is the additional geometry needed to compare
the original guarded gap with the logical core reconstructed after the
positive shift or zero-recovery route.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedDecrementBranchSearch

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlGuardedDecrementEntry
open CounterControlParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## First generated commands -/

/-- Continuation of the first positive-decrement marker shift. -/
def positiveFirstSuccess (growth : Turing.Dir) (source : Nat)
    (register : Register) : ControlRef :=
  match register with
  | .clock => directRef growth source finishDirectSlot
  | _ => searchRef growth source (secondarySearchBase + 1)

/-- First marker-shift command selected by the positive decrement branch. -/
def positiveFirstRaw (growth : Turing.Dir) (source : Nat)
    (register : Register) : RawCommand :=
  .markerShift ⟨growth, source, secondarySearchBase⟩
    (MarkerSchedule.decrementStartBoundary register) .right .left
    (positiveFirstSuccess growth source register) (some .right) none

/-- The explicit positive command is the head of the generated decrement
shift schedule. -/
theorem positiveFirstRaw_mem_decrementShiftCommands
    (growth : Turing.Dir) (source : Nat) (register : Register) :
    positiveFirstRaw growth source register ∈
      decrementShiftCommands growth source register := by
  cases register <;>
    simp [positiveFirstRaw, positiveFirstSuccess, decrementShiftCommands,
      decrementShiftCommandsAux, MarkerShift.decrementOrder,
      MarkerSchedule.decrementStartBoundary]

/-- Continuation of the first zero-recovery navigation command. -/
def zeroFirstSuccess (growth : Turing.Dir) (source ifZero : Nat)
    (register : Register) : ControlRef :=
  match register with
  | .clock => .logical growth ifZero
  | _ => directRef growth source zeroDirectBase

/-- First preserving navigation command selected by the zero branch. -/
def zeroFirstRaw (growth : Turing.Dir) (source : Nat)
    (register : Register) (ifZero : Nat) : RawCommand :=
  .boundaryNavigation ⟨growth, source, zeroSearchBase⟩
    (MarkerSchedule.decrementStartBoundary register) .right
    (zeroFirstSuccess growth source ifZero register) .preserve

/-- The explicit zero command is the head of its nonempty generated recovery
route. -/
theorem zeroFirstRaw_mem_routeCommandsAux
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero : Nat) :
    zeroFirstRaw growth source register ifZero ∈
      routeCommandsAux growth source zeroSearchBase zeroDirectBase
        (.logical growth ifZero)
        (AnchoredCounterGeometry.routeFromZero register) := by
  cases register <;> exact List.mem_cons_self

/-! ## Packaged branch search entries -/

/-- The positive branch enters the first shift as a guarded distance-zero
search.  `route` retains the original decrement-entry route geometry. -/
structure PositiveSearchHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  route : TestHandoff current growth source register ifZero ifPositive
  branch_read : (branchTape route.route).read = blankSymbol
  next : GuardedSearch base c
  selectedRaw_eq : next.selectedRaw =
    positiveFirstRaw growth source register
  outer_eq : next.current.outer =
    (branchTape route.route).move (orient growth .right)
  distance_eq : next.current.distance = 0
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current) next.current.cfg

/-- The zero branch enters the first recovery navigation as a genuine
distance-zero search.  Its preceding cell is the expected labelled boundary,
so no false guardedness claim is made. -/
structure ZeroSearchHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  route : TestHandoff current growth source register ifZero ifPositive
  branch_read : (branchTape route.route).read = boundarySymbol
    (AnchoredCounterGeometry.registerGap register).castSucc
  next : GenuineSearch base c
  selectedRaw_eq : next.selectedRaw =
    zeroFirstRaw growth source register ifZero
  outer_eq : next.outer =
    (branchTape route.route).move (orient growth .right)
  distance_eq : next.distance = 0
  preceding_boundary :
    (next.outer.move (NestingMachine.opposite next.direction)).read =
      boundarySymbol (AnchoredCounterGeometry.registerGap register).castSucc
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current) next.cfg

/-- Exact generated-search entry selected by either decrement branch. -/
inductive SearchOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  | positive (handoff : PositiveSearchHandoff current growth source register
      ifZero ifPositive)
  | zero (handoff : ZeroSearchHandoff current growth source register
      ifZero ifPositive)

private theorem positiveFirstRaw_mem_rawCommands
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program) :
    positiveFirstRaw growth source register ∈ rawCommands := by
  apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
    growth hrule
  simp [commandsForRule, decrementCommands,
    positiveFirstRaw_mem_decrementShiftCommands]

private theorem zeroFirstRaw_mem_rawCommands
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program) :
    zeroFirstRaw growth source register ifZero ∈ rawCommands := by
  apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
    growth hrule
  simp [commandsForRule, decrementCommands,
    zeroFirstRaw_mem_routeCommandsAux]

/-- Package the exact distance-zero search selected by an already executed
guarded decrement branch. -/
theorem searchOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (outcome : BranchOutcome current growth source register
      ifZero ifPositive) :
    Nonempty (SearchOutcome current growth source register
      ifZero ifPositive) := by
  cases outcome with
  | positive route hblank hreach =>
      let raw := positiveFirstRaw growth source register
      have hraw : raw ∈ rawCommands :=
        positiveFirstRaw_mem_rawCommands growth source register ifZero
          ifPositive route.rule_mem
      let search : Search := CounterControlCommandAt.rawTag raw hraw
      let outer := (branchTape route.route).move (orient growth .right)
      let genuine : GenuineSearch base c := {
        search := search
        outer := outer
        distance := 0
        gap := by
          change SearchGap (fun symbol => symbol = blankSymbol)
            (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
            outer
            (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection
            0
          rw [SearchGap.zero, CounterControlCommandAt.compileRawCommand_spec]
          have hfinish := decrementEntry_finish_read route.route
          cases growth <;> cases register <;>
            simpa [raw, outer, positiveFirstRaw, positiveFirstSuccess,
              CounterControlCommandAt.compileRawAtTag, Command.target,
              Target.Matches, branchTape,
              CounterControlDecrementEntry.branchTape, FullTM0.Tape.read,
              FullTM0.Tape.move] using hfinish }
      let next : GuardedSearch base c := {
        current := genuine
        guard := by
          change (outer.move (NestingMachine.opposite
            (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection)).read =
              blankSymbol
          rw [CounterControlCommandAt.compileRawCommand_searchDirection]
          cases growth <;> cases register <;>
            simpa [raw, outer, positiveFirstRaw, positiveFirstSuccess,
              RawCommand.physicalSearchDirection,
              RawCommand.logicalSearchDirection, RawCommand.address,
              NestingMachine.opposite, branchTape,
              CounterControlDecrementEntry.branchTape, FullTM0.Tape.read,
              FullTM0.Tape.move] using hblank }
      refine ⟨SearchOutcome.positive ⟨route, hblank, next, ?_, rfl, rfl,
        ?_⟩⟩
      · change rawCommands.get search = raw
        exact CounterControlCommandAt.rawCommands_get_rawTag raw hraw
      · change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          (foundCfg current.current)
          ((searchSystem base c).startCfg search outer)
        have hget : rawCommands.get search = raw :=
          CounterControlCommandAt.rawCommands_get_rawTag raw hraw
        change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          (foundCfg current.current)
          ⟨searchState base c (rawCommands.get search).address, outer⟩
        rw [hget]
        simpa [raw, outer, positiveFirstRaw, RawCommand.address] using hreach
  | zero route hboundary hreach =>
      let raw := zeroFirstRaw growth source register ifZero
      have hraw : raw ∈ rawCommands :=
        zeroFirstRaw_mem_rawCommands growth source register ifZero
          ifPositive route.rule_mem
      let search : Search := CounterControlCommandAt.rawTag raw hraw
      let outer := (branchTape route.route).move (orient growth .right)
      let next : GenuineSearch base c := {
        search := search
        outer := outer
        distance := 0
        gap := by
          change SearchGap (fun symbol => symbol = blankSymbol)
            (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
            outer
            (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection
            0
          rw [SearchGap.zero, CounterControlCommandAt.compileRawCommand_spec]
          have hfinish := decrementEntry_finish_read route.route
          cases growth <;> cases register <;>
            simpa [raw, outer, zeroFirstRaw, zeroFirstSuccess,
              CounterControlCommandAt.compileRawAtTag, Command.target,
              Target.Matches, branchTape,
              CounterControlDecrementEntry.branchTape, FullTM0.Tape.read,
              FullTM0.Tape.move] using hfinish }
      refine ⟨SearchOutcome.zero ⟨route, hboundary, next, ?_, rfl, rfl,
        ?_, ?_⟩⟩
      · change rawCommands.get search = raw
        exact CounterControlCommandAt.rawCommands_get_rawTag raw hraw
      · change (outer.move (NestingMachine.opposite
          (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection)).read =
            boundarySymbol
              (AnchoredCounterGeometry.registerGap register).castSucc
        rw [CounterControlCommandAt.compileRawCommand_searchDirection]
        cases growth <;> cases register <;>
          simpa [raw, outer, zeroFirstRaw, zeroFirstSuccess,
            RawCommand.physicalSearchDirection,
            RawCommand.logicalSearchDirection, RawCommand.address,
            NestingMachine.opposite, branchTape,
            CounterControlDecrementEntry.branchTape, FullTM0.Tape.read,
            FullTM0.Tape.move] using hboundary
      · change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          (foundCfg current.current)
          ((searchSystem base c).startCfg search outer)
        have hget : rawCommands.get search = raw :=
          CounterControlCommandAt.rawCommands_get_rawTag raw hraw
        change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          (foundCfg current.current)
          ⟨searchState base c (rawCommands.get search).address, outer⟩
        rw [hget]
        simpa [raw, outer, zeroFirstRaw, RawCommand.address] using hreach

/-- Complete a selected guarded decrement-entry caller through the exact
distance-zero generated search chosen by its branch. -/
theorem searchOutcome_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register)) :
    Nonempty (SearchOutcome current growth source register
      ifZero ifPositive) := by
  rcases branchOutcome_of_rule base c hmortal current himmortal growth source
      register ifZero ifPositive hrule hcommand with ⟨branch⟩
  exact searchOutcome base c branch

/-! ## Consumer-facing consequences -/

/-- The positive branch package selects a command in the complete generated
decrement-shift schedule. -/
theorem positive_command_mem
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : PositiveSearchHandoff current growth source register
      ifZero ifPositive) :
    handoff.next.selectedRaw ∈
      decrementShiftCommands growth source register := by
  rw [handoff.selectedRaw_eq]
  exact positiveFirstRaw_mem_decrementShiftCommands growth source register

/-- The zero branch package selects a command in the complete generated
zero-recovery route. -/
theorem zero_command_mem
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : ZeroSearchHandoff current growth source register
      ifZero ifPositive) :
    handoff.next.selectedRaw ∈
      routeCommandsAux growth source zeroSearchBase zeroDirectBase
        (.logical growth ifZero)
        (AnchoredCounterGeometry.routeFromZero register) := by
  rw [handoff.selectedRaw_eq]
  exact zeroFirstRaw_mem_routeCommandsAux growth source register ifZero

/-- Immortality at the original guarded found state transfers to the exact
positive generated-search entry. -/
theorem positive_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : PositiveSearchHandoff current growth source register
      ifZero ifPositive)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      handoff.next.current.cfg :=
  FullTM0.ImmortalFrom.of_reaches himmortal handoff.reaches

/-- Immortality at the original guarded found state transfers to the exact
zero generated-search entry. -/
theorem zero_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : ZeroSearchHandoff current growth source register
      ifZero ifPositive)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      handoff.next.cfg :=
  FullTM0.ImmortalFrom.of_reaches himmortal handoff.reaches

/-- The original guarded found state reaches the positive search's exact
found configuration. -/
theorem positive_reaches_found
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : PositiveSearchHandoff current growth source register
      ifZero ifPositive)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current) (foundCfg handoff.next.current) := by
  exact handoff.reaches.trans
    (reaches_foundCfg_of_immortal handoff.next.current
      (positive_immortalFrom base c handoff himmortal))

/-- The original guarded found state reaches the zero search's exact found
configuration. -/
theorem zero_reaches_found
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : ZeroSearchHandoff current growth source register
      ifZero ifPositive)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current) (foundCfg handoff.next) := by
  exact handoff.reaches.trans
    (reaches_foundCfg_of_immortal handoff.next
      (zero_immortalFrom base c handoff himmortal))

end

end CounterControlGuardedDecrementBranchSearch
end Hooper
end Kari
end LeanWang
