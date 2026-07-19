/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlIncrementInstructionSemantics

/-!
# Conditional-decrement instruction semantics

This module develops the zero and positive branches of a compiled conditional
decrement, including the complete positive-decrement schedule.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlInstructionSemantics

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCommandAt CounterControlBridge
open CounterControlScheduleSemantics CounterControlCleanupSemantics
  CounterControlFrameBacking CounterControlCoreRoutes

noncomputable section
/-! ## Conditional-decrement routing and branching -/

/-- Navigate from boundary `4` to the boundary which tests the selected
register.  Clock needs no navigation. -/
theorem machine_reaches_decrementToTest_solved
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c
          (bodyEntry spec.growth source
            (.decrement register ifZero ifPositive)),
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c (directRef spec.growth source testDirectSlot),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let route := AnchoredCounterGeometry.routeToDecrementStart register
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux spec.growth source bodySearchBase
          (bodyDirectBase + 1) (directRef spec.growth source testDirectSlot)
          route → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, decrementCommands, route, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules spec.growth source
            (directRef spec.growth source bodyDirectBase) 4 bodySearchBase
            route ++
          routeContinuationRules spec.growth source bodySearchBase
            (bodyDirectBase + 1) route →
        raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    have hraw' : raw ∈
        routeEntryRules spec.growth source
            (directRef spec.growth source bodyDirectBase) 4 bodySearchBase
            (AnchoredCounterGeometry.routeToDecrementStart register) ++
          routeContinuationRules spec.growth source bodySearchBase
            (bodyDirectBase + 1)
            (AnchoredCounterGeometry.routeToDecrementStart register) := by
      simpa [route] using hraw
    rcases List.mem_append.mp hraw' with hentry | hcontinuation
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hentry))
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hcontinuation))
  cases register with
  | clock => exact Relation.ReflTransGen.refl
  | temp =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .temp)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 3)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .temp)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry spec.growth source
              (.decrement .temp ifZero ifPositive)),
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth T (boundaryOffset spec.registers 3)⟩ at hrun
      exact hrun
  | right =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .right)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 2)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .right)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry spec.growth source
              (.decrement .right ifZero ifPositive)),
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth T (boundaryOffset spec.registers 2)⟩ at hrun
      exact hrun
  | left =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .left)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 1)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .left)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry spec.growth source
              (.decrement .left ifZero ifPositive)),
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth T (boundaryOffset spec.registers 1)⟩ at hrun
      exact hrun

/-- The test rule moves left from the selected right boundary into the tested
gap. -/
theorem machine_reaches_decrementTest
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} (T : FullTM0.Tape (Symbol numTags))
    (hread : (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))).read =
      boundarySymbol (MarkerSchedule.decrementStartBoundary register)) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source testDirectSlot),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨resolve base c (directRef spec.growth source branchDirectSlot),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register) - 1)⟩ := by
  let raw : RawDirectRule :=
    ⟨spec.growth, directRef spec.growth source testDirectSlot,
      .boundary (MarkerSchedule.decrementStartBoundary register),
      directRef spec.growth source branchDirectSlot, .left⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [raw, decrementRules]
  have hmatch : raw.read.Matches
      (atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register))).read := by
    simpa [raw, RawRead.Matches] using hread
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))) hmatch
  have hpositive : 0 < boundaryOffset spec.registers
      (MarkerSchedule.decrementStartBoundary register) := by
    simp [boundaryOffset]
  have hmove : (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))).move
        (orient spec.growth .left) =
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register) - 1) := by
    rw [show boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) =
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register) - 1) + 1 by
      omega]
    rw [orient_eq_orientDirection, atLogical_move_left]
    congr 1
  rw [hmove] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef spec.growth source testDirectSlot),
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register))⟩
    ⟨resolve base c (directRef spec.growth source branchDirectSlot),
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register) - 1)⟩ at hrun
  exact hrun

/-- A zero tested gap is exactly the adjacent preceding boundary. -/
theorem decrement_zero_predecessor_read
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (register : Register)
    (hzero : spec.registers.get register = 0) :
    (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).read =
      boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc := by
  have hcoord : boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1 =
      boundaryOffset spec.registers
        (AnchoredCounterGeometry.registerGap register).castSucc :=
    AnchoredCounterGeometry.zeroTest_predecessor
      spec.registers register hzero
  rw [hcoord, atLogical_read]
  exact h.boundary _

/-- From the predecessor boundary of an empty tested gap, the generated zero
route returns to boundary `4` and enters the zero successor. -/
theorem machine_reaches_decrementZeroRecovery_solved
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hzero : spec.registers.get register = 0)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source branchDirectSlot),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register) - 1)⟩
      ⟨logicalState base c spec.growth ifZero,
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  let route := AnchoredCounterGeometry.routeFromZero register
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux spec.growth source zeroSearchBase zeroDirectBase
          (.logical spec.growth ifZero) route → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, decrementCommands, route, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules spec.growth source
            (directRef spec.growth source branchDirectSlot)
            (AnchoredCounterGeometry.registerGap register).castSucc
            zeroSearchBase route ++
          routeContinuationRules spec.growth source zeroSearchBase
            zeroDirectBase route → raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    rcases List.mem_append.mp hraw with hentry | hcontinuation
    · have hentryOriginal : raw ∈ routeEntryRules spec.growth source
          (directRef spec.growth source branchDirectSlot)
          (AnchoredCounterGeometry.registerGap register).castSucc
          zeroSearchBase
          (AnchoredCounterGeometry.routeFromZero register) := by
        simpa [route] using hentry
      have hentryRules : routeEntryRules spec.growth source
          (directRef spec.growth source branchDirectSlot)
          (AnchoredCounterGeometry.registerGap register).castSucc
          zeroSearchBase
          (AnchoredCounterGeometry.routeFromZero register) =
          [⟨spec.growth, directRef spec.growth source branchDirectSlot,
            .boundary
              (AnchoredCounterGeometry.registerGap register).castSucc,
            searchRef spec.growth source zeroSearchBase, .right⟩] := by
        cases register <;> rfl
      rw [hentryRules] at hentryOriginal
      have heq : raw =
          ⟨spec.growth, directRef spec.growth source branchDirectSlot,
            .boundary
              (AnchoredCounterGeometry.registerGap register).castSucc,
            searchRef spec.growth source zeroSearchBase, .right⟩ := by
        simpa using hentryOriginal
      have hfour : raw ∈
          [⟨spec.growth, directRef spec.growth source testDirectSlot,
              .boundary (MarkerSchedule.decrementStartBoundary register),
              directRef spec.growth source branchDirectSlot, .left⟩,
            ⟨spec.growth, directRef spec.growth source branchDirectSlot,
              .blank, searchRef spec.growth source secondarySearchBase,
              .right⟩,
            ⟨spec.growth, directRef spec.growth source branchDirectSlot,
              .boundary
                (AnchoredCounterGeometry.registerGap register).castSucc,
              searchRef spec.growth source zeroSearchBase, .right⟩,
            ⟨spec.growth, directRef spec.growth source finishDirectSlot,
              .blank, .logical spec.growth ifPositive, .left⟩] := by
        simp only [List.mem_cons, List.mem_singleton]
        exact Or.inr (Or.inr (Or.inl heq))
      simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inr hfour)
    · simp only [decrementRules, List.mem_append]
      exact Or.inr (by simpa [route] using hcontinuation)
  have hsourcePosition : boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1 =
      boundaryOffset spec.registers
        (AnchoredCounterGeometry.registerGap register).castSucc :=
    AnchoredCounterGeometry.zeroTest_predecessor
      spec.registers register hzero
  have hrun := route_reaches_solved_at_of_ne_nil base c
    spec.outerDistance hshort spec.growth source zeroSearchBase zeroDirectBase
    (directRef spec.growth source branchDirectSlot)
    (.logical spec.growth ifZero)
    (AnchoredCounterGeometry.registerGap register).castSucc route
    (by simpa [route] using
      AnchoredCounterGeometry.routeFromZero_ne_nil register) T
    (boundaryOffset spec.registers
      (AnchoredCounterGeometry.registerGap register).castSucc)
    (layoutEnd spec.registers)
    (by rw [atLogical_read]; exact h.boundary _)
    (routeFromZero_executesWithin h register)
    (by intro raw hraw; exact hcommands raw hraw)
    (by intro raw hraw; exact hrules raw hraw)
  rw [hsourcePosition]
  simpa [route, logicalState, CounterControlPlan.resolve] using hrun

/-- Exact zero branch of one compiled conditional decrement. -/
theorem machine_reaches_decrementZeroInstruction_solved
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hzero : spec.registers.get register = 0)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c spec.growth source,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨logicalState base c spec.growth ifZero,
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_solved base c spec.growth
    source (.decrement register ifZero ifPositive) hrule h rfl hshort
  have hroute := machine_reaches_decrementToTest_solved base c source ifZero
    ifPositive register hrule h hshort
  have htest := machine_reaches_decrementTest base c source ifZero ifPositive
    register hrule T (by
      rw [atLogical_read]
      exact h.boundary _)
  have hzeroRoute := machine_reaches_decrementZeroRecovery_solved base c
    source ifZero ifPositive register hrule h hzero hshort
  have hvalidation' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c spec.growth source,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c
          (bodyEntry spec.growth source
            (.decrement register ifZero ifPositive)),
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := hvalidation
  have hpred := decrement_zero_predecessor_read h register hzero
  have hzeroRoute' := hzeroRoute
  exact hvalidation'.trans (hroute.trans (htest.trans (by
    -- The zero-route entry rule reads the predecessor boundary established
    -- by the represented empty gap.
    exact hzeroRoute')))

/-! ## Positive conditional-decrement branch -/

/-- The cell immediately left of the tested boundary is blank when the
selected register is positive. -/
theorem decrement_positive_predecessor_blank
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (register : Register)
    (hpositive : 0 < spec.registers.get register) :
    (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).read =
      blankSymbol :=
  (show CounterControlCoreFrame.CoreRepresents
      spec.registers spec.growth T from ⟨h.core⟩)
    |>.positive_predecessor_blank register hpositive

/-- Clearing a source cell which the next canonical core covers preserves
the same exact outer backing. -/
theorem install_clear_inside_backedBy
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer) (next : Registers)
    (hnextCore : layoutEnd next < spec.outerDistance) (source : Nat)
    (hsourcePositive : 0 < source) (hsourceCore : source ≤ layoutEnd next)
    (hle : layoutEnd spec.registers ≤ layoutEnd next) :
    BackedBy (updateSpec spec next hnextCore)
      (install next spec.growth spec.returnTag
        (writeLogical spec.growth T source blankSymbol)) outer := by
  constructor
  · rw [install_clear_inside next spec.growth spec.returnTag T source
      hsourcePositive hsourceCore]
    rw [hback.installed]
    exact install_over_install spec.registers next spec.growth
      spec.returnTag outer hle
  · simpa [updateSpec] using hback.searchGap

/-- First positive-decrement shift: the head already sits on the tested
boundary, so its solved search has distance zero. -/
theorem machine_reaches_decrementFirst_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (counterState searchSlot : Nat)
    (success : ControlRef) (hlimit : 0 < limit)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers i.succ ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers i.succ - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (boundaryOffset spec.registers i.succ)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers i.succ) blankSymbol))
            (boundaryOffset spec.registers i.succ)⟩ ∨
      Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (boundaryOffset spec.registers i.succ)⟩ := by
  have hsourcePositive : 1 < boundaryOffset spec.registers i.succ := by
    simp [boundaryOffset]
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches
      (atLogical spec.growth T (boundaryOffset spec.registers i.succ))
      (OrientedMarkerTape.orientDirection spec.growth .right) 0 := by
    rw [SearchGap.zero]
    change (atLogical spec.growth T
      (boundaryOffset spec.registers i.succ)).read = boundarySymbol i.succ
    rw [atLogical_read]
    exact h.boundary i.succ
  have hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers i.succ - 1 : Nat) : Int) =
        blankSymbol := by
    have hb := h.gap_blank i (RegisterLayout.values spec.registers i - 1)
      (by omega)
    have hcoord : (firstGapOffset spec.registers i : Int) +
        (RegisterLayout.values spec.registers i - 1 : Nat) =
        (boundaryOffset spec.registers i.succ - 1 : Nat) := by
      simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
      omega
    rw [hcoord] at hb
    exact hb
  apply machine_reaches_decrementCanonical_with base c limit Failure runner
    counterState searchSlot success none h next i.succ
    (boundaryOffset spec.registers i.succ) 0 hsourcePositive
    (by simp) hlimit hgap hblank hnextCore hlower hupper hsource hdestination
      hshrink hmove hraw

theorem machine_reaches_decrementFirst_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) (counterState searchSlot : Nat)
    (success : ControlRef) (hlimit : 0 < limit)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers i.succ ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers i.succ - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
        atLogical spec.growth T (boundaryOffset spec.registers i.succ)⟩
      ⟨resolve base c success,
        atLogical spec.growth
          (install next spec.growth spec.returnTag
            (writeLogical spec.growth T
              (boundaryOffset spec.registers i.succ) blankSymbol))
          (boundaryOffset spec.registers i.succ)⟩ := by
  rcases machine_reaches_decrementFirst_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) counterState searchSlot success hlimit h next i hpositive hnextCore
      hlower hupper hsource hdestination hshrink hmove hraw with hrun | failure
  · exact hrun
  · exact failure.elim

/-- Every later positive-decrement shift searches right across one represented
gap before moving its right boundary left. -/
theorem machine_reaches_decrementFollowing_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (counterState searchSlot : Nat)
    (success : ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hdistance : RegisterLayout.values spec.registers i < limit)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers i.succ ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers i.succ - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (firstGapOffset spec.registers i)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers i.succ) blankSymbol))
            (boundaryOffset spec.registers i.succ)⟩ ∨
      Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (firstGapOffset spec.registers i)⟩ := by
  have hsourcePositive : 1 < boundaryOffset spec.registers i.succ := by
    simp [boundaryOffset]
  have horigin : firstGapOffset spec.registers i +
      RegisterLayout.values spec.registers i =
      boundaryOffset spec.registers i.succ := by
    simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
    omega
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches
      (atLogical spec.growth T (firstGapOffset spec.registers i))
      (OrientedMarkerTape.orientDirection spec.growth .right)
      (RegisterLayout.values spec.registers i) := by
    change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ) _ _ _
    exact h.searchGap_adjacent_right i
  have hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers i.succ - 1 : Nat) : Int) =
        blankSymbol := by
    have hb := h.gap_blank i (RegisterLayout.values spec.registers i - 1)
      (by omega)
    have hcoord : (firstGapOffset spec.registers i : Int) +
        (RegisterLayout.values spec.registers i - 1 : Nat) =
        (boundaryOffset spec.registers i.succ - 1 : Nat) := by
      simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
      omega
    rw [hcoord] at hb
    exact hb
  exact machine_reaches_decrementCanonical_with base c limit Failure runner
    counterState searchSlot success none h next i.succ
    (firstGapOffset spec.registers i)
    (RegisterLayout.values spec.registers i) hsourcePositive horigin
    hdistance hgap hblank hnextCore hlower hupper hsource hdestination
    hshrink hmove hraw

theorem machine_reaches_decrementFollowing_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) (counterState searchSlot : Nat)
    (success : ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hdistance : RegisterLayout.values spec.registers i < limit)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers i.succ ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers i.succ - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
        atLogical spec.growth T (firstGapOffset spec.registers i)⟩
      ⟨resolve base c success,
        atLogical spec.growth
          (install next spec.growth spec.returnTag
            (writeLogical spec.growth T
              (boundaryOffset spec.registers i.succ) blankSymbol))
          (boundaryOffset spec.registers i.succ)⟩ := by
  rcases machine_reaches_decrementFollowing_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) counterState searchSlot success h next i hpositive hdistance hnextCore
      hlower hupper hsource hdestination hshrink hmove hraw with hrun | failure
  · exact hrun
  · exact failure.elim

/-- The positive branch reads a blank predecessor cell and moves right onto
the first boundary shifted by the decrement schedule. -/
theorem machine_reaches_decrementPositiveHandoff
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hpositive : 0 < spec.registers.get register) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source branchDirectSlot),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register) - 1)⟩
      ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let raw : RawDirectRule :=
    ⟨spec.growth, directRef spec.growth source branchDirectSlot, .blank,
      searchRef spec.growth source secondarySearchBase, .right⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    simp only [decrementRules, List.mem_append]
    apply Or.inl
    apply Or.inr
    simp [raw]
  have hblank : raw.read.Matches
      (atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register) - 1)).read := by
    change (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).read =
      blankSymbol
    exact decrement_positive_predecessor_blank h register hpositive
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1)) hblank
  have hp : 0 < boundaryOffset spec.registers
      (MarkerSchedule.decrementStartBoundary register) := by
    simp [boundaryOffset]
  have hmove : (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).move
        (orient spec.growth .right) =
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register)) := by
    rw [show boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) =
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register) - 1) + 1 by
      omega]
    rw [orient_eq_orientDirection, atLogical_move_right]
    congr 1
  rw [hmove] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef spec.growth source branchDirectSlot),
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register) - 1)⟩
    ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register))⟩ at hrun
  exact hrun

theorem boundaryOffset_le_layoutEnd (registers : Registers)
    (label : Fin 5) : boundaryOffset registers label ≤ layoutEnd registers := by
  change CounterLayout.boundaryPos (RegisterLayout.values registers) label + 1 ≤
    CounterLayout.boundaryPos (RegisterLayout.values registers) 4 + 1
  apply Nat.add_le_add_right
  exact CounterLayout.boundaryPos_mono _ (by omega)

/-- Complete positive-decrement suffix schedule, including exact preservation
of the suspended outer backing. -/
structure DecrementScheduleRunner
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop) where
  pullback : ∀ {start current},
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start current →
      Failure current → Failure start
  first : ∀ (limit : Nat), Short limit →
    ∀ (counterState searchSlot : Nat) (success : ControlRef), 0 < limit →
    ∀ {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)},
      Represents spec T → ∀ (next : Registers) (i : Fin 4),
      0 < RegisterLayout.values spec.registers i →
      layoutEnd next < spec.outerDistance →
      layoutEnd next ≤ layoutEnd spec.registers →
      layoutEnd spec.registers ≤ layoutEnd next + 1 →
      boundaryOffset spec.registers i.succ ≤ layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ - 1 ≤ layoutEnd next →
      (layoutEnd next < layoutEnd spec.registers →
        boundaryOffset spec.registers i.succ = layoutEnd spec.registers) →
      MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
        MarkerTape.canonicalTape next →
      RawCommand.markerShift
        ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
        (some .right) none ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (boundaryOffset spec.registers i.succ)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers i.succ) blankSymbol))
            (boundaryOffset spec.registers i.succ)⟩
  following : ∀ (limit : Nat), Short limit →
    ∀ (counterState searchSlot : Nat) (success : ControlRef),
    ∀ {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)},
      Represents spec T → ∀ (next : Registers) (i : Fin 4),
      0 < RegisterLayout.values spec.registers i →
      RegisterLayout.values spec.registers i < limit →
      layoutEnd next < spec.outerDistance →
      layoutEnd next ≤ layoutEnd spec.registers →
      layoutEnd spec.registers ≤ layoutEnd next + 1 →
      boundaryOffset spec.registers i.succ ≤ layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ - 1 ≤ layoutEnd next →
      (layoutEnd next < layoutEnd spec.registers →
        boundaryOffset spec.registers i.succ = layoutEnd spec.registers) →
      MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
        MarkerTape.canonicalTape next →
      RawCommand.markerShift
        ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
        (some .right) none ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (firstGapOffset spec.registers i)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers i.succ) blankSymbol))
            (boundaryOffset spec.registers i.succ)⟩

/-- Register-independent positive-decrement scheduling, parameterized by the
outcome of each constituent bounded search. -/
theorem machine_reaches_decrementSchedule_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : DecrementScheduleRunner base c Short Failure)
    (source : Nat)
    (register : Register)
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hpositive : 0 < spec.registers.get register)
    (hshort : Short spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩
        ⟨resolve base c (directRef spec.growth source finishDirectSlot),
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd spec.registers)⟩ ∧
      BackedBy (decrementSpec spec register hpositive)
        (decrementTape spec register T) outer) ∨
      Failure
        ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩ := by
  have h := hback.represents
  have hlimit : 0 < spec.outerDistance := by
    exact Nat.zero_lt_of_lt spec.core_before_target
  have hdesired := decrementTape_backedBy hback register hpositive
  cases register with
  | clock =>
      have hp : 0 < spec.registers.clock := by
        simpa [Registers.get] using hpositive
      let next := spec.registers.decrement .clock
      have hnextCore : layoutEnd next < spec.outerDistance :=
        (layoutEnd_decrement_lt spec.registers .clock hpositive).trans
          spec.core_before_target
      have hend : layoutEnd next + 1 = layoutEnd spec.registers :=
        layoutEnd_decrement_add_one spec.registers .clock hpositive
      have hmove : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers 4) 4 =
        MarkerTape.canonicalTape next := by
        have hm := MarkerSchedule.moveClockBoundary_after_increment next
        have hinv := MarkerSchedule.increment_decrement_registers
          spec.registers .clock hpositive
        rw [hinv] at hm
        exact hm
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 4 .right .left
          (directRef spec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have hrun := runner.first spec.outerDistance hshort source secondarySearchBase
        (directRef spec.growth source finishDirectSlot) hlimit h next
        (3 : Fin 4) (by simpa [RegisterLayout.values] using hp)
        hnextCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 4)
        (by
          change layoutEnd spec.registers - 1 ≤ layoutEnd next
          omega)
        (by intro _; rfl) hmove hraw
      apply FullTM0.CompletesOr.and_right ?_ hdesired
      simpa [next, decrementTape, clearOldLayoutEnd,
        MarkerSchedule.decrementStartBoundary,
        boundaryOffset_four] using hrun
  | temp =>
      have hp : 0 < spec.registers.temp := by
        simpa [Registers.get] using hpositive
      let final := spec.registers.decrement .temp
      have hinv : final.increment .temp = spec.registers := by
        exact MarkerSchedule.increment_decrement_registers
          spec.registers .temp hpositive
      let clockRegs := final.increment .clock
      have hclockEnd : layoutEnd clockRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [clockRegs, layoutEnd_increment]
      have hclockCore : layoutEnd clockRegs < spec.outerDistance := by
        rw [hclockEnd]
        exact spec.core_before_target
      have hmoveThree : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers 3) 3 =
        MarkerTape.canonicalTape clockRegs := by
        have hm := MarkerSchedule.moveTempBoundary_before_clock final
        rw [hinv] at hm
        exact hm
      have hrawThree : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 3 .right .left
          (searchRef spec.growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have hthree := runner.first spec.outerDistance hshort source secondarySearchBase
        (searchRef spec.growth source (secondarySearchBase + 1)) hlimit h
        clockRegs (2 : Fin 4) (by simpa [RegisterLayout.values] using hp)
        hclockCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 3)
        (by
          change boundaryOffset spec.registers 3 - 1 ≤ layoutEnd clockRegs
          rw [hclockEnd]
          have hbound := boundaryOffset_le_layoutEnd spec.registers (3 : Fin 5)
          omega)
        (by
          intro hlt
          rw [hclockEnd] at hlt
          omega)
        hmoveThree hrawThree
      let Uclock := install clockRegs spec.growth spec.returnTag
        (writeLogical spec.growth T (boundaryOffset spec.registers 3)
          blankSymbol)
      let clockSpec := updateSpec spec clockRegs hclockCore
      have hclockBack : BackedBy clockSpec Uclock outer := by
        exact install_clear_inside_backedBy hback clockRegs hclockCore
          (boundaryOffset spec.registers 3) (by simp [boundaryOffset])
          (by rw [hclockEnd]; exact boundaryOffset_le_layoutEnd _ 3)
          (by omega)
      have hclockRep := hclockBack.represents
      have hfinalCore : layoutEnd final < clockSpec.outerDistance := by
        have hlt := layoutEnd_decrement_lt spec.registers .temp hpositive
        simpa [clockSpec, updateSpec, final] using
          hlt.trans spec.core_before_target
      have hfinalEnd : layoutEnd final + 1 = layoutEnd clockRegs := by
        rw [hclockEnd]
        exact layoutEnd_decrement_add_one spec.registers .temp hpositive
      have hmoveFour : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape clockSpec.registers)
          (MarkerTape.boundaryPosition clockSpec.registers 4) 4 =
        MarkerTape.canonicalTape final := by
        simpa [clockSpec, updateSpec, clockRegs] using
          MarkerSchedule.moveClockBoundary_after_increment final
      have hrawFour : RawCommand.markerShift
          ⟨clockSpec.growth, source, secondarySearchBase + 1⟩ 4 .right .left
          (directRef clockSpec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        simpa [clockSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 1⟩ 4 .right .left
            (directRef spec.growth source finishDirectSlot) (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hfour := runner.following spec.outerDistance (by simpa [clockSpec, updateSpec] using hshort)
        source (secondarySearchBase + 1)
        (directRef clockSpec.growth source finishDirectSlot) hclockRep final
        (3 : Fin 4)
        (by simp [clockSpec, updateSpec, clockRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [clockSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        hfinalCore
        (by
          dsimp only [clockSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by
          dsimp only [clockSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (boundaryOffset_le_layoutEnd clockSpec.registers 4)
        (by
          change layoutEnd clockSpec.registers - 1 ≤ layoutEnd final
          dsimp only [clockSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by intro _; rfl) hmoveFour hrawFour
      have hhead : boundaryOffset spec.registers (Fin.succ (2 : Fin 4)) =
          firstGapOffset clockSpec.registers 3 := by
        change boundaryOffset spec.registers 3 =
          firstGapOffset clockSpec.registers 3
        simp [clockSpec, updateSpec, clockRegs, final, firstGapOffset,
          boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hfourBack := decrementTape_backedBy hclockBack .clock (by
        simp [clockSpec, updateSpec, clockRegs, final, Registers.get,
          Registers.increment, Registers.decrement, Registers.set])
      have hfinalRegs : (decrementSpec clockSpec .clock (by
          simp [clockSpec, updateSpec, clockRegs, final, Registers.get,
            Registers.increment, Registers.decrement, Registers.set])).registers =
          (decrementSpec spec .temp hpositive).registers := by
        simp [decrementSpec, updateSpec, clockSpec, clockRegs, final,
          Registers.increment, Registers.decrement, Registers.set,
          Registers.get]
      have hfinalTape : decrementTape clockSpec .clock Uclock =
          decrementTape spec .temp T := by
        calc
          decrementTape clockSpec .clock Uclock =
              install (decrementSpec clockSpec .clock (by
                simp [clockSpec, updateSpec, clockRegs, final, Registers.get,
                  Registers.increment, Registers.decrement,
                  Registers.set])).registers spec.growth spec.returnTag outer :=
            hfourBack.installed
          _ = install (decrementSpec spec .temp hpositive).registers
              spec.growth spec.returnTag outer := by rw [hfinalRegs]
          _ = decrementTape spec .temp T := hdesired.installed.symm
      have hclockDecrement : clockSpec.registers.decrement .clock = final := by
        simp [clockSpec, updateSpec, clockRegs, final, Registers.decrement,
          Registers.increment, Registers.set, Registers.get]
      have hresultTape :
          install final clockSpec.growth clockSpec.returnTag
              (writeLogical clockSpec.growth Uclock
                (boundaryOffset clockSpec.registers (Fin.succ (3 : Fin 4)))
                blankSymbol) =
            decrementTape clockSpec .clock Uclock := by
        rw [decrementTape, clearOldLayoutEnd, hclockDecrement]
        rw [show boundaryOffset clockSpec.registers
          (Fin.succ (3 : Fin 4)) = layoutEnd clockSpec.registers by rfl]
      rw [hhead] at hthree
      rw [hresultTape, hfinalTape] at hfour
      simp only [clockSpec, updateSpec] at hthree hfour
      have hhead' : boundaryOffset spec.registers (3 : Fin 5) =
          firstGapOffset clockRegs 3 := by
        simpa [clockSpec, updateSpec] using hhead
      have hUclock :
          install clockRegs spec.growth spec.returnTag
              (writeLogical spec.growth T (firstGapOffset clockRegs 3)
                blankSymbol) = Uclock := by
        dsimp only [Uclock]
        rw [← hhead']
      rw [hUclock] at hthree
      rw [show boundaryOffset clockRegs (Fin.succ (3 : Fin 4)) =
        layoutEnd clockRegs by rfl, hclockEnd] at hfour
      simp only [searchRef, CounterControlPlan.resolve] at hthree
      apply FullTM0.CompletesOr.and_right ?_ hdesired
      simpa only [MarkerSchedule.decrementStartBoundary, hhead'] using
        FullTM0.CompletesOr.trans runner.pullback hthree hfour
  | right =>
      have hp : 0 < spec.registers.right := by
        simpa [Registers.get] using hpositive
      let final := spec.registers.decrement .right
      have hinv : final.increment .right = spec.registers :=
        MarkerSchedule.increment_decrement_registers spec.registers .right
          hpositive
      let tempRegs := final.increment .temp
      let clockRegs := final.increment .clock
      have htempEnd : layoutEnd tempRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [tempRegs, layoutEnd_increment]
      have hclockEnd : layoutEnd clockRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [clockRegs, layoutEnd_increment]
      have htempCore : layoutEnd tempRegs < spec.outerDistance := by
        rw [htempEnd]
        exact spec.core_before_target
      have hmoveTwo := MarkerSchedule.moveRightBoundary_before_temp final
      rw [hinv] at hmoveTwo
      have hrawTwo : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 2 .right .left
          (searchRef spec.growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have htwo := runner.first spec.outerDistance hshort source secondarySearchBase
        (searchRef spec.growth source (secondarySearchBase + 1)) hlimit h
        tempRegs (1 : Fin 4)
        (by simpa [RegisterLayout.values, Registers.get] using hpositive)
        htempCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 2)
        (by
          change boundaryOffset spec.registers 2 - 1 ≤ layoutEnd tempRegs
          rw [htempEnd]
          have hbound := boundaryOffset_le_layoutEnd spec.registers (2 : Fin 5)
          omega)
        (by
          intro hlt
          rw [htempEnd] at hlt
          omega)
        hmoveTwo hrawTwo
      let Utemp := install tempRegs spec.growth spec.returnTag
        (writeLogical spec.growth T (boundaryOffset spec.registers 2)
          blankSymbol)
      let tempSpec := updateSpec spec tempRegs htempCore
      have htempBack : BackedBy tempSpec Utemp outer :=
        install_clear_inside_backedBy hback tempRegs htempCore
          (boundaryOffset spec.registers 2) (by simp [boundaryOffset])
          (by rw [htempEnd]; exact boundaryOffset_le_layoutEnd _ 2)
          (by omega)
      have hclockCore : layoutEnd clockRegs < tempSpec.outerDistance := by
        simpa [tempSpec, updateSpec, hclockEnd] using spec.core_before_target
      have hmoveThree : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape tempSpec.registers)
          (MarkerTape.boundaryPosition tempSpec.registers 3) 3 =
        MarkerTape.canonicalTape clockRegs := by
        simpa [tempSpec, updateSpec, tempRegs, clockRegs] using
          MarkerSchedule.moveTempBoundary_before_clock final
      have hrawThree : RawCommand.markerShift
          ⟨tempSpec.growth, source, secondarySearchBase + 1⟩ 3 .right .left
          (searchRef tempSpec.growth source (secondarySearchBase + 2))
          (some .right) none ∈ rawCommands := by
        simpa [tempSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 1⟩ 3 .right .left
            (searchRef spec.growth source (secondarySearchBase + 2))
            (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hthree := runner.following spec.outerDistance (by simpa [tempSpec, updateSpec] using hshort)
        source (secondarySearchBase + 1)
        (searchRef tempSpec.growth source (secondarySearchBase + 2))
        htempBack.represents clockRegs (2 : Fin 4)
        (by simp [tempSpec, updateSpec, tempRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [tempSpec, updateSpec] using
          registerValue_lt_outerDistance htempBack.represents (2 : Fin 4))
        hclockCore
        (by
          dsimp only [tempSpec, updateSpec]
          rw [hclockEnd, htempEnd])
        (by
          dsimp only [tempSpec, updateSpec]
          rw [hclockEnd, htempEnd]
          omega)
        (boundaryOffset_le_layoutEnd tempSpec.registers 3)
        (by
          dsimp only [tempSpec, updateSpec]
          have hbound := boundaryOffset_le_layoutEnd tempRegs
            (Fin.succ (2 : Fin 4))
          rw [htempEnd] at hbound
          omega)
        (by
          dsimp only [tempSpec, updateSpec]
          intro hlt
          rw [hclockEnd, htempEnd] at hlt
          omega)
        hmoveThree hrawThree
      let Uclock := install clockRegs tempSpec.growth tempSpec.returnTag
        (writeLogical tempSpec.growth Utemp
          (boundaryOffset tempSpec.registers 3) blankSymbol)
      let clockSpec := updateSpec tempSpec clockRegs hclockCore
      have hclockBack : BackedBy clockSpec Uclock outer :=
        install_clear_inside_backedBy htempBack clockRegs hclockCore
          (boundaryOffset tempSpec.registers 3) (by simp [boundaryOffset])
          (by
            dsimp only [tempSpec, updateSpec]
            have hbound := boundaryOffset_le_layoutEnd tempRegs (3 : Fin 5)
            rw [htempEnd] at hbound
            rw [hclockEnd]
            exact hbound)
          (by
            dsimp only [tempSpec, updateSpec]
            rw [hclockEnd, htempEnd])
      have hfinalCore : layoutEnd final < clockSpec.outerDistance := by
        have hlt := layoutEnd_decrement_lt spec.registers .right hpositive
        simpa [clockSpec, tempSpec, updateSpec, final] using
          hlt.trans spec.core_before_target
      have hfinalEnd : layoutEnd final + 1 = layoutEnd spec.registers := by
        exact layoutEnd_decrement_add_one spec.registers .right hpositive
      have hmoveFour : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape clockSpec.registers)
          (MarkerTape.boundaryPosition clockSpec.registers 4) 4 =
        MarkerTape.canonicalTape final := by
        simpa [clockSpec, tempSpec, updateSpec, clockRegs] using
          MarkerSchedule.moveClockBoundary_after_increment final
      have hrawFour : RawCommand.markerShift
          ⟨clockSpec.growth, source, secondarySearchBase + 2⟩ 4 .right .left
          (directRef clockSpec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        simpa [clockSpec, tempSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 2⟩ 4 .right .left
            (directRef spec.growth source finishDirectSlot) (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hfour := runner.following spec.outerDistance (by simpa [clockSpec, tempSpec, updateSpec] using hshort)
        source (secondarySearchBase + 2)
        (directRef clockSpec.growth source finishDirectSlot)
        hclockBack.represents final (3 : Fin 4)
        (by simp [clockSpec, tempSpec, updateSpec, clockRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [clockSpec, tempSpec, updateSpec] using
          registerValue_lt_outerDistance hclockBack.represents (3 : Fin 4))
        hfinalCore
        (by
          dsimp only [clockSpec, tempSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by
          dsimp only [clockSpec, tempSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (boundaryOffset_le_layoutEnd clockSpec.registers 4)
        (by
          change layoutEnd clockSpec.registers - 1 ≤ layoutEnd final
          dsimp only [clockSpec, tempSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by intro _; rfl) hmoveFour hrawFour
      have hheadTwo :
          boundaryOffset spec.registers (Fin.succ (1 : Fin 4)) =
          firstGapOffset tempSpec.registers 2 := by
        change boundaryOffset spec.registers 2 =
          firstGapOffset tempSpec.registers 2
        rw [← hinv]
        simp [tempSpec, updateSpec, tempRegs, final, firstGapOffset,
          boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hheadThree :
          boundaryOffset tempSpec.registers (Fin.succ (2 : Fin 4)) =
          firstGapOffset clockSpec.registers 3 := by
        change boundaryOffset tempSpec.registers 3 =
          firstGapOffset clockSpec.registers 3
        simp [clockSpec, tempSpec, updateSpec, clockRegs, tempRegs, final,
          firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hfourBack := decrementTape_backedBy hclockBack .clock (by
        simp [clockSpec, tempSpec, updateSpec, clockRegs, final,
          Registers.get, Registers.increment, Registers.decrement,
          Registers.set])
      have hfinalTape : decrementTape clockSpec .clock Uclock =
          decrementTape spec .right T := by
        calc
          _ = install final spec.growth spec.returnTag outer := by
            simpa [clockSpec, tempSpec, updateSpec, clockRegs, final,
              decrementSpec, Registers.increment, Registers.decrement,
              Registers.set, Registers.get] using hfourBack.installed
          _ = _ := by
            simpa [final, decrementSpec, updateSpec] using hdesired.installed.symm
      have hclockDecrement : clockSpec.registers.decrement .clock = final := by
        simp [clockSpec, tempSpec, updateSpec, clockRegs, final,
          Registers.decrement, Registers.increment, Registers.set,
          Registers.get]
      have hresultTape :
          install final clockSpec.growth clockSpec.returnTag
              (writeLogical clockSpec.growth Uclock
                (boundaryOffset clockSpec.registers (Fin.succ (3 : Fin 4)))
                blankSymbol) =
            decrementTape clockSpec .clock Uclock := by
        rw [decrementTape, clearOldLayoutEnd, hclockDecrement]
        rw [show boundaryOffset clockSpec.registers
          (Fin.succ (3 : Fin 4)) = layoutEnd clockSpec.registers by rfl]
      rw [hresultTape, hfinalTape] at hfour
      have hheadTwo' : boundaryOffset spec.registers (2 : Fin 5) =
          firstGapOffset tempRegs 2 := by
        simpa [tempSpec, updateSpec] using hheadTwo
      have hheadThree' : boundaryOffset tempRegs (3 : Fin 5) =
          firstGapOffset clockRegs 3 := by
        simpa [clockSpec, tempSpec, updateSpec] using hheadThree
      rw [hheadTwo] at htwo
      rw [hheadThree] at hthree
      simp only [tempSpec, clockSpec, updateSpec] at htwo hthree hfour
      have hUtemp :
          install tempRegs spec.growth spec.returnTag
              (writeLogical spec.growth T (firstGapOffset tempRegs 2)
                blankSymbol) = Utemp := by
        dsimp only [Utemp]
        rw [← hheadTwo']
      have hUclock :
          install clockRegs spec.growth spec.returnTag
              (writeLogical spec.growth Utemp (firstGapOffset clockRegs 3)
                blankSymbol) = Uclock := by
        dsimp only [Uclock, tempSpec, updateSpec]
        rw [← hheadThree']
      rw [hUtemp] at htwo
      rw [hUclock] at hthree
      rw [show boundaryOffset clockRegs (Fin.succ (3 : Fin 4)) =
        layoutEnd clockRegs by rfl, hclockEnd] at hfour
      simp only [searchRef, CounterControlPlan.resolve] at htwo hthree
      apply FullTM0.CompletesOr.and_right ?_ hdesired
      simpa only [MarkerSchedule.decrementStartBoundary, hheadTwo'] using
        FullTM0.CompletesOr.trans runner.pullback htwo (FullTM0.CompletesOr.trans runner.pullback hthree hfour)
  | left =>
      have hp : 0 < spec.registers.left := by
        simpa [Registers.get] using hpositive
      let final := spec.registers.decrement .left
      have hinv : final.increment .left = spec.registers :=
        MarkerSchedule.increment_decrement_registers spec.registers .left
          hpositive
      let rightRegs := final.increment .right
      let tempRegs := final.increment .temp
      let clockRegs := final.increment .clock
      have hrightEnd : layoutEnd rightRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [rightRegs, layoutEnd_increment]
      have htempEnd : layoutEnd tempRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [tempRegs, layoutEnd_increment]
      have hclockEnd : layoutEnd clockRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [clockRegs, layoutEnd_increment]
      have hrightCore : layoutEnd rightRegs < spec.outerDistance := by
        rw [hrightEnd]
        exact spec.core_before_target
      have hmoveOne := MarkerSchedule.moveLeftBoundary_before_right final
      rw [hinv] at hmoveOne
      have hrawOne : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 1 .right .left
          (searchRef spec.growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have hone := runner.first spec.outerDistance hshort source secondarySearchBase
        (searchRef spec.growth source (secondarySearchBase + 1)) hlimit h
        rightRegs (0 : Fin 4)
        (by simpa [RegisterLayout.values, Registers.get] using hpositive)
        hrightCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 1)
        (by
          change boundaryOffset spec.registers 1 - 1 ≤ layoutEnd rightRegs
          rw [hrightEnd]
          have hbound := boundaryOffset_le_layoutEnd spec.registers (1 : Fin 5)
          omega)
        (by
          intro hlt
          rw [hrightEnd] at hlt
          omega)
        hmoveOne hrawOne
      let Uright := install rightRegs spec.growth spec.returnTag
        (writeLogical spec.growth T (boundaryOffset spec.registers 1)
          blankSymbol)
      let rightSpec := updateSpec spec rightRegs hrightCore
      have hrightBack : BackedBy rightSpec Uright outer :=
        install_clear_inside_backedBy hback rightRegs hrightCore
          (boundaryOffset spec.registers 1) (by simp [boundaryOffset])
          (by rw [hrightEnd]; exact boundaryOffset_le_layoutEnd _ 1)
          (by omega)
      have htempCore : layoutEnd tempRegs < rightSpec.outerDistance := by
        simpa [rightSpec, updateSpec, htempEnd] using spec.core_before_target
      have hmoveTwo : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape rightSpec.registers)
          (MarkerTape.boundaryPosition rightSpec.registers 2) 2 =
        MarkerTape.canonicalTape tempRegs := by
        simpa [rightSpec, updateSpec, rightRegs, tempRegs] using
          MarkerSchedule.moveRightBoundary_before_temp final
      have hrawTwo : RawCommand.markerShift
          ⟨rightSpec.growth, source, secondarySearchBase + 1⟩ 2 .right .left
          (searchRef rightSpec.growth source (secondarySearchBase + 2))
          (some .right) none ∈ rawCommands := by
        simpa [rightSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 1⟩ 2 .right .left
            (searchRef spec.growth source (secondarySearchBase + 2))
            (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have htwo := runner.following spec.outerDistance (by simpa [rightSpec, updateSpec] using hshort)
        source (secondarySearchBase + 1)
        (searchRef rightSpec.growth source (secondarySearchBase + 2))
        hrightBack.represents tempRegs (1 : Fin 4)
        (by simp [rightSpec, updateSpec, rightRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [rightSpec, updateSpec] using
          registerValue_lt_outerDistance hrightBack.represents (1 : Fin 4))
        htempCore
        (by
          dsimp only [rightSpec, updateSpec]
          rw [htempEnd, hrightEnd])
        (by
          dsimp only [rightSpec, updateSpec]
          rw [htempEnd, hrightEnd]
          omega)
        (boundaryOffset_le_layoutEnd rightSpec.registers 2)
        (by
          dsimp only [rightSpec, updateSpec]
          have hbound := boundaryOffset_le_layoutEnd rightRegs
            (Fin.succ (1 : Fin 4))
          rw [hrightEnd] at hbound
          omega)
        (by
          dsimp only [rightSpec, updateSpec]
          intro hlt
          rw [htempEnd, hrightEnd] at hlt
          omega)
        hmoveTwo hrawTwo
      let Utemp := install tempRegs rightSpec.growth rightSpec.returnTag
        (writeLogical rightSpec.growth Uright
          (boundaryOffset rightSpec.registers 2) blankSymbol)
      let tempSpec := updateSpec rightSpec tempRegs htempCore
      have htempBack : BackedBy tempSpec Utemp outer :=
        install_clear_inside_backedBy hrightBack tempRegs htempCore
          (boundaryOffset rightSpec.registers 2) (by simp [boundaryOffset])
          (by
            dsimp only [rightSpec, updateSpec]
            have hbound := boundaryOffset_le_layoutEnd rightRegs (2 : Fin 5)
            rw [hrightEnd] at hbound
            rw [htempEnd]
            exact hbound)
          (by
            dsimp only [rightSpec, updateSpec]
            rw [htempEnd, hrightEnd])
      have hclockCore : layoutEnd clockRegs < tempSpec.outerDistance := by
        simpa [tempSpec, rightSpec, updateSpec, hclockEnd] using
          spec.core_before_target
      have hmoveThree : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape tempSpec.registers)
          (MarkerTape.boundaryPosition tempSpec.registers 3) 3 =
        MarkerTape.canonicalTape clockRegs := by
        simpa [tempSpec, rightSpec, updateSpec, tempRegs, clockRegs] using
          MarkerSchedule.moveTempBoundary_before_clock final
      have hrawThree : RawCommand.markerShift
          ⟨tempSpec.growth, source, secondarySearchBase + 2⟩ 3 .right .left
          (searchRef tempSpec.growth source (secondarySearchBase + 3))
          (some .right) none ∈ rawCommands := by
        simpa [tempSpec, rightSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 2⟩ 3 .right .left
            (searchRef spec.growth source (secondarySearchBase + 3))
            (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hthree := runner.following spec.outerDistance (by simpa [tempSpec, rightSpec, updateSpec] using hshort)
        source (secondarySearchBase + 2)
        (searchRef tempSpec.growth source (secondarySearchBase + 3))
        htempBack.represents clockRegs (2 : Fin 4)
        (by simp [tempSpec, rightSpec, updateSpec, tempRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [tempSpec, rightSpec, updateSpec] using
          registerValue_lt_outerDistance htempBack.represents (2 : Fin 4))
        hclockCore
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          rw [hclockEnd, htempEnd])
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          rw [hclockEnd, htempEnd]
          omega)
        (boundaryOffset_le_layoutEnd tempSpec.registers 3)
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          have hbound := boundaryOffset_le_layoutEnd tempRegs
            (Fin.succ (2 : Fin 4))
          rw [htempEnd] at hbound
          omega)
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          intro hlt
          rw [hclockEnd, htempEnd] at hlt
          omega)
        hmoveThree hrawThree
      let Uclock := install clockRegs tempSpec.growth tempSpec.returnTag
        (writeLogical tempSpec.growth Utemp
          (boundaryOffset tempSpec.registers 3) blankSymbol)
      let clockSpec := updateSpec tempSpec clockRegs hclockCore
      have hclockBack : BackedBy clockSpec Uclock outer :=
        install_clear_inside_backedBy htempBack clockRegs hclockCore
          (boundaryOffset tempSpec.registers 3) (by simp [boundaryOffset])
          (by
            dsimp only [tempSpec, rightSpec, updateSpec]
            have hbound := boundaryOffset_le_layoutEnd tempRegs (3 : Fin 5)
            rw [htempEnd] at hbound
            rw [hclockEnd]
            exact hbound)
          (by
            dsimp only [tempSpec, rightSpec, updateSpec]
            rw [hclockEnd, htempEnd])
      have hfinalCore : layoutEnd final < clockSpec.outerDistance := by
        have hlt := layoutEnd_decrement_lt spec.registers .left hpositive
        simpa [clockSpec, tempSpec, rightSpec, updateSpec, final] using
          hlt.trans spec.core_before_target
      have hfinalEnd : layoutEnd final + 1 = layoutEnd spec.registers := by
        exact layoutEnd_decrement_add_one spec.registers .left hpositive
      have hmoveFour : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape clockSpec.registers)
          (MarkerTape.boundaryPosition clockSpec.registers 4) 4 =
        MarkerTape.canonicalTape final := by
        simpa [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs] using
          MarkerSchedule.moveClockBoundary_after_increment final
      have hrawFour : RawCommand.markerShift
          ⟨clockSpec.growth, source, secondarySearchBase + 3⟩ 4 .right .left
          (directRef clockSpec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        simpa [clockSpec, tempSpec, rightSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 3⟩ 4 .right .left
            (directRef spec.growth source finishDirectSlot) (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hfour := runner.following spec.outerDistance (by simpa [clockSpec, tempSpec, rightSpec, updateSpec] using hshort)
        source (secondarySearchBase + 3)
        (directRef clockSpec.growth source finishDirectSlot)
        hclockBack.represents final (3 : Fin 4)
        (by simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [clockSpec, tempSpec, rightSpec, updateSpec] using
          registerValue_lt_outerDistance hclockBack.represents (3 : Fin 4))
        hfinalCore
        (by
          dsimp only [clockSpec, tempSpec, rightSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by
          dsimp only [clockSpec, tempSpec, rightSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (boundaryOffset_le_layoutEnd clockSpec.registers 4)
        (by
          change layoutEnd clockSpec.registers - 1 ≤ layoutEnd final
          dsimp only [clockSpec, tempSpec, rightSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by intro _; rfl) hmoveFour hrawFour
      have hheadOne :
          boundaryOffset spec.registers (Fin.succ (0 : Fin 4)) =
          firstGapOffset rightSpec.registers 1 := by
        change boundaryOffset spec.registers 1 =
          firstGapOffset rightSpec.registers 1
        rw [← hinv]
        simp [rightSpec, updateSpec, rightRegs, final, firstGapOffset,
          boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
          Registers.increment, Registers.decrement, Registers.set,
          Registers.get]
      have hheadTwo :
          boundaryOffset rightSpec.registers (Fin.succ (1 : Fin 4)) =
          firstGapOffset tempSpec.registers 2 := by
        change boundaryOffset rightSpec.registers 2 =
          firstGapOffset tempSpec.registers 2
        simp [tempSpec, rightSpec, updateSpec, tempRegs, rightRegs, final,
          firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hheadThree :
          boundaryOffset tempSpec.registers (Fin.succ (2 : Fin 4)) =
          firstGapOffset clockSpec.registers 3 := by
        change boundaryOffset tempSpec.registers 3 =
          firstGapOffset clockSpec.registers 3
        simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, tempRegs,
          final, firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hfourBack := decrementTape_backedBy hclockBack .clock (by
        simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, final,
          Registers.get, Registers.increment, Registers.decrement,
          Registers.set])
      have hfinalTape : decrementTape clockSpec .clock Uclock =
          decrementTape spec .left T := by
        calc
          _ = install final spec.growth spec.returnTag outer := by
            simpa [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs,
              final, decrementSpec, Registers.increment, Registers.decrement,
              Registers.set, Registers.get] using hfourBack.installed
          _ = _ := by
            simpa [final, decrementSpec, updateSpec] using hdesired.installed.symm
      have hclockDecrement : clockSpec.registers.decrement .clock = final := by
        simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, final,
          Registers.decrement, Registers.increment, Registers.set,
          Registers.get]
      have hresultTape :
          install final clockSpec.growth clockSpec.returnTag
              (writeLogical clockSpec.growth Uclock
                (boundaryOffset clockSpec.registers (Fin.succ (3 : Fin 4)))
                blankSymbol) =
            decrementTape clockSpec .clock Uclock := by
        rw [decrementTape, clearOldLayoutEnd, hclockDecrement]
        rw [show boundaryOffset clockSpec.registers
          (Fin.succ (3 : Fin 4)) = layoutEnd clockSpec.registers by rfl]
      rw [hresultTape, hfinalTape] at hfour
      have hheadOne' : boundaryOffset spec.registers (1 : Fin 5) =
          firstGapOffset rightRegs 1 := by
        simpa [rightSpec, updateSpec] using hheadOne
      have hheadTwo' : boundaryOffset rightRegs (2 : Fin 5) =
          firstGapOffset tempRegs 2 := by
        simpa [tempSpec, rightSpec, updateSpec] using hheadTwo
      have hheadThree' : boundaryOffset tempRegs (3 : Fin 5) =
          firstGapOffset clockRegs 3 := by
        simpa [clockSpec, tempSpec, rightSpec, updateSpec] using hheadThree
      rw [hheadOne] at hone
      rw [hheadTwo] at htwo
      rw [hheadThree] at hthree
      simp only [rightSpec, tempSpec, clockSpec, updateSpec] at hone htwo hthree hfour
      have hUright :
          install rightRegs spec.growth spec.returnTag
              (writeLogical spec.growth T (firstGapOffset rightRegs 1)
                blankSymbol) = Uright := by
        dsimp only [Uright]
        rw [← hheadOne']
      have hUtemp :
          install tempRegs spec.growth spec.returnTag
              (writeLogical spec.growth Uright (firstGapOffset tempRegs 2)
                blankSymbol) = Utemp := by
        dsimp only [Utemp, rightSpec, updateSpec]
        rw [← hheadTwo']
      have hUclock :
          install clockRegs spec.growth spec.returnTag
              (writeLogical spec.growth Utemp (firstGapOffset clockRegs 3)
                blankSymbol) = Uclock := by
        dsimp only [Uclock, tempSpec, rightSpec, updateSpec]
        rw [← hheadThree']
      rw [hUright] at hone
      rw [hUtemp] at htwo
      rw [hUclock] at hthree
      rw [show boundaryOffset clockRegs (Fin.succ (3 : Fin 4)) =
        layoutEnd clockRegs by rfl, hclockEnd] at hfour
      simp only [searchRef, CounterControlPlan.resolve] at hone htwo hthree
      apply FullTM0.CompletesOr.and_right ?_ hdesired
      simpa only [MarkerSchedule.decrementStartBoundary, hheadOne'] using
        FullTM0.CompletesOr.trans runner.pullback hone
          (FullTM0.CompletesOr.trans runner.pullback htwo
            (FullTM0.CompletesOr.trans runner.pullback hthree hfour))



/-- Complete positive-decrement suffix schedule, including exact preservation
of the suspended outer backing. -/
theorem machine_reaches_decrementSchedule_solved
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hpositive : 0 < spec.registers.get register)
    (hshort : ShortSearches base c spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩
        ⟨resolve base c (directRef spec.growth source finishDirectSlot),
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd spec.registers)⟩ ∧
      BackedBy (decrementSpec spec register hpositive)
        (decrementTape spec register T) outer := by
  let runner : DecrementScheduleRunner base c (ShortSearches base c)
      (fun _ => False) := {
    pullback := by
      intro _ _ _ failure
      exact failure.elim
    first := by
      intro limit hshort counterState searchSlot success hlimit spec T h next i
        hpositive hnextCore hlower hupper hsource hdestination hshrink hmove
        hraw
      exact Or.inl (machine_reaches_decrementFirst_solved base c limit hshort
        counterState searchSlot success hlimit h next i hpositive hnextCore
        hlower hupper hsource hdestination hshrink hmove hraw)
    following := by
      intro limit hshort counterState searchSlot success spec T h next i
        hpositive hdistance hnextCore hlower hupper hsource hdestination
        hshrink hmove hraw
      exact Or.inl (machine_reaches_decrementFollowing_solved base c limit
        hshort counterState searchSlot success h next i hpositive hdistance
        hnextCore hlower hupper hsource hdestination hshrink hmove hraw) }
  rcases machine_reaches_decrementSchedule_with base c (ShortSearches base c)
      (fun _ => False) runner source register hback hpositive hshort hcommands
      with result | failure
  · exact result
  · exact failure.elim

theorem machine_reaches_decrementPositiveFinish
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} (T : FullTM0.Tape (Symbol numTags))
    (hpositive : 0 < spec.registers.get register) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source finishDirectSlot),
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth ifPositive,
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd (spec.registers.decrement register))⟩ := by
  let raw : RawDirectRule :=
    ⟨spec.growth, directRef spec.growth source finishDirectSlot, .blank,
      .logical spec.growth ifPositive, .left⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [raw, decrementRules]
  have hmatch : raw.read.Matches
      (atLogical spec.growth (decrementTape spec register T)
        (layoutEnd spec.registers)).read := by
    change (atLogical spec.growth (decrementTape spec register T)
      (layoutEnd spec.registers)).read = blankSymbol
    rw [atLogical_read]
    exact decrementTape_old_layoutEnd_blank spec register T hpositive
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical spec.growth (decrementTape spec register T)
      (layoutEnd spec.registers)) hmatch
  have hend := layoutEnd_decrement_add_one spec.registers register hpositive
  have hmove : (atLogical spec.growth (decrementTape spec register T)
      (layoutEnd spec.registers)).move (orient spec.growth .left) =
      atLogical spec.growth (decrementTape spec register T)
        (layoutEnd (spec.registers.decrement register)) := by
    rw [← hend, orient_eq_orientDirection, atLogical_move_left]
  rw [hmove] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef spec.growth source finishDirectSlot),
      atLogical spec.growth (decrementTape spec register T)
        (layoutEnd spec.registers)⟩
    ⟨logicalState base c spec.growth ifPositive,
      atLogical spec.growth (decrementTape spec register T)
        (layoutEnd (spec.registers.decrement register))⟩ at hrun
  exact hrun

/-- Exact successful semantics of the positive branch of one compiled
conditional decrement, with the updated frame still backed by the same
suspended outer tape. -/
theorem machine_reaches_decrementPositiveInstruction_solved
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hpositive : 0 < spec.registers.get register)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth ifPositive,
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd (spec.registers.decrement register))⟩ ∧
      BackedBy (decrementSpec spec register hpositive)
        (decrementTape spec register T) outer := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_solved base c spec.growth
    source (.decrement register ifZero ifPositive) hrule h rfl hshort
  have hroute := machine_reaches_decrementToTest_solved base c source ifZero
    ifPositive register hrule h hshort
  have htest := machine_reaches_decrementTest base c source ifZero ifPositive
    register hrule T (by
      rw [atLogical_read]
      exact h.boundary _)
  have hhandoff := machine_reaches_decrementPositiveHandoff base c source
    ifZero ifPositive register hrule h hpositive
  have hcommands : ∀ raw,
      raw ∈ decrementShiftCommands spec.growth source register →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, decrementCommands, hraw]
  have hschedule := machine_reaches_decrementSchedule_solved base c source
    register hback hpositive hshort hcommands
  have hfinish := machine_reaches_decrementPositiveFinish base c source
    ifZero ifPositive register hrule T hpositive
  constructor
  · exact hvalidation.trans
      (hroute.trans
        (htest.trans
          (hhandoff.trans (hschedule.1.trans hfinish))))
  · exact hschedule.2

end

end CounterControlInstructionSemantics
end Hooper
end Kari
end LeanWang
