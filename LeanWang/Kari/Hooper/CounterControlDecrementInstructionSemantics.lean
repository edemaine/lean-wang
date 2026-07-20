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
            (bodyEntry spec.growth source
              (.decrement register ifZero ifPositive)) 4 bodySearchBase
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
      simp only [bodyEntry] at hraw
      cases hlegs : AnchoredCounterGeometry.routeToDecrementStart register with
      | nil =>
          simp [route, hlegs, routeEntryRules, routeContinuationRules] at hraw
      | cons first rest => simpa [route, hlegs] using hraw
    rcases List.mem_append.mp hraw' with hentry | hcontinuation
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hentry))
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hcontinuation))
  exact route_reaches_solved_at_maybe_empty base c spec.outerDistance hshort
    spec.growth source bodySearchBase (bodyDirectBase + 1)
    (bodyEntry spec.growth source (.decrement register ifZero ifPositive))
    (directRef spec.growth source testDirectSlot) 4 route
    (by
      intro hnil
      simp [route, bodyEntry, hnil])
    T (layoutEnd spec.registers)
    (boundaryOffset spec.registers
      (MarkerSchedule.decrementStartBoundary register))
    h.read_boundary_four (routeToDecrementStart_executesWithin h register)
    hcommands hrules

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

/-- Execute one noninitial stage and preserve exact outer backing. -/
private theorem decrementIntermediateStage_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : DecrementScheduleRunner base c Short Failure)
    (source searchSlot : Nat) (success : ControlRef)
    (final : Registers) {stage next : Register}
    (hstage : DecrementStageNext stage next)
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hregisters : spec.registers = decrementStageRegisters final stage)
    (hshort : Short spec.outerDistance)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, source, searchSlot⟩ (decrementStageIndex stage).succ
      .right .left success (some .right) none ∈ rawCommands) :
    let nextRegisters := decrementStageRegisters final next
    let nextCore : layoutEnd nextRegisters < spec.outerDistance := by
      rw [decrementStage_layoutEnd, ← decrementStage_layoutEnd final stage,
        ← hregisters]
      exact spec.core_before_target
    let U := install nextRegisters spec.growth spec.returnTag
      (writeLogical spec.growth T
        (boundaryOffset spec.registers (decrementStageIndex stage).succ)
        blankSymbol)
    let nextSpec := updateSpec spec nextRegisters nextCore
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨spec.growth, source, searchSlot⟩,
          atLogical spec.growth T
            (firstGapOffset spec.registers (decrementStageIndex stage))⟩
        ⟨resolve base c success,
          atLogical spec.growth U
            (boundaryOffset spec.registers
              (decrementStageIndex stage).succ)⟩ ∧
      BackedBy nextSpec U outer := by
  dsimp only
  have h := hback.represents
  let nextRegisters := decrementStageRegisters final next
  have hnextCore : layoutEnd nextRegisters < spec.outerDistance := by
    rw [decrementStage_layoutEnd, ← decrementStage_layoutEnd final stage,
      ← hregisters]
    exact spec.core_before_target
  have hlayout : layoutEnd nextRegisters = layoutEnd spec.registers := by
    rw [hregisters, decrementStage_layoutEnd,
      decrementStage_layoutEnd]
  have hrun := runner.following spec.outerDistance hshort source searchSlot
    success h nextRegisters (decrementStageIndex stage)
    (by rw [hregisters]; exact decrementStage_positive final stage)
    (registerValue_lt_outerDistance h (decrementStageIndex stage))
    hnextCore (by omega) (by omega)
    (boundaryOffset_le_layoutEnd spec.registers _)
    (by
      have hbound := boundaryOffset_le_layoutEnd spec.registers
        (decrementStageIndex stage).succ
      omega)
    (by intro hlt; omega)
    (by simpa [hregisters, nextRegisters] using
      decrementStage_move (final := final) hstage)
    hraw
  let U := install nextRegisters spec.growth spec.returnTag
    (writeLogical spec.growth T
      (boundaryOffset spec.registers (decrementStageIndex stage).succ)
      blankSymbol)
  let nextSpec := updateSpec spec nextRegisters hnextCore
  have hnextBack : BackedBy nextSpec U outer := by
    exact install_clear_inside_backedBy hback nextRegisters hnextCore
      (boundaryOffset spec.registers (decrementStageIndex stage).succ)
      (by simp [boundaryOffset])
      (by
        have hbound := boundaryOffset_le_layoutEnd spec.registers
          (decrementStageIndex stage).succ
        rw [hlayout]
        exact hbound)
      (by omega)
  exact ⟨hrun, hnextBack⟩

/-- Execute the zero-distance first stage and preserve exact outer backing. -/
private theorem decrementFirstIntermediateStage_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : DecrementScheduleRunner base c Short Failure)
    (source searchSlot : Nat) (success : ControlRef)
    (final : Registers) {stage next : Register}
    (hstage : DecrementStageNext stage next)
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hregisters : spec.registers = decrementStageRegisters final stage)
    (hshort : Short spec.outerDistance)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, source, searchSlot⟩ (decrementStageIndex stage).succ
      .right .left success (some .right) none ∈ rawCommands) :
    let nextRegisters := decrementStageRegisters final next
    let nextCore : layoutEnd nextRegisters < spec.outerDistance := by
      rw [decrementStage_layoutEnd, ← decrementStage_layoutEnd final stage,
        ← hregisters]
      exact spec.core_before_target
    let U := install nextRegisters spec.growth spec.returnTag
      (writeLogical spec.growth T
        (boundaryOffset spec.registers (decrementStageIndex stage).succ)
        blankSymbol)
    let nextSpec := updateSpec spec nextRegisters nextCore
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨spec.growth, source, searchSlot⟩,
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (decrementStageIndex stage).succ)⟩
        ⟨resolve base c success,
          atLogical spec.growth U
            (boundaryOffset spec.registers
              (decrementStageIndex stage).succ)⟩ ∧
      BackedBy nextSpec U outer := by
  dsimp only
  have h := hback.represents
  let nextRegisters := decrementStageRegisters final next
  have hnextCore : layoutEnd nextRegisters < spec.outerDistance := by
    rw [decrementStage_layoutEnd, ← decrementStage_layoutEnd final stage,
      ← hregisters]
    exact spec.core_before_target
  have hlayout : layoutEnd nextRegisters = layoutEnd spec.registers := by
    rw [hregisters, decrementStage_layoutEnd,
      decrementStage_layoutEnd]
  have hlimit : 0 < spec.outerDistance :=
    Nat.zero_lt_of_lt spec.core_before_target
  have hrun := runner.first spec.outerDistance hshort source searchSlot
    success hlimit h nextRegisters (decrementStageIndex stage)
    (by rw [hregisters]; exact decrementStage_positive final stage)
    hnextCore (by omega) (by omega)
    (boundaryOffset_le_layoutEnd spec.registers _)
    (by
      have hbound := boundaryOffset_le_layoutEnd spec.registers
        (decrementStageIndex stage).succ
      omega)
    (by intro hlt; omega)
    (by simpa [hregisters, nextRegisters] using
      decrementStage_move (final := final) hstage)
    hraw
  let U := install nextRegisters spec.growth spec.returnTag
    (writeLogical spec.growth T
      (boundaryOffset spec.registers (decrementStageIndex stage).succ)
      blankSymbol)
  let nextSpec := updateSpec spec nextRegisters hnextCore
  have hnextBack : BackedBy nextSpec U outer := by
    exact install_clear_inside_backedBy hback nextRegisters hnextCore
      (boundaryOffset spec.registers (decrementStageIndex stage).succ)
      (by simp [boundaryOffset])
      (by
        have hbound := boundaryOffset_le_layoutEnd spec.registers
          (decrementStageIndex stage).succ
        rw [hlayout]
        exact hbound)
      (by omega)
  exact ⟨hrun, hnextBack⟩

/-- Finish a noninitial stage chain by shifting boundary `4`. -/
private theorem decrementFinalFollowing_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : DecrementScheduleRunner base c Short Failure)
    (source searchSlot : Nat)
    (final : Registers)
    {spec : Spec numTags} {T outer desiredTape :
      FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hregisters : spec.registers =
      decrementStageRegisters final .clock)
    (hshort : Short spec.outerDistance)
    (hfinalCore : layoutEnd final < spec.outerDistance)
    (hdesired : BackedBy (updateSpec spec final hfinalCore)
      desiredTape outer)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, source, searchSlot⟩ 4 .right .left
      (directRef spec.growth source finishDirectSlot) (some .right) none ∈
        rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨spec.growth, source, searchSlot⟩,
        atLogical spec.growth T
          (firstGapOffset spec.registers (3 : Fin 4))⟩
      ⟨resolve base c (directRef spec.growth source finishDirectSlot),
        atLogical spec.growth desiredTape (layoutEnd final + 1)⟩ := by
  have h := hback.represents
  have hp : 0 < RegisterLayout.values spec.registers (3 : Fin 4) := by
    rw [hregisters]
    exact decrementStage_positive final .clock
  have hcurrentEnd : layoutEnd spec.registers = layoutEnd final + 1 := by
    rw [hregisters, decrementStage_layoutEnd]
  have hmove : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape spec.registers)
      (MarkerTape.boundaryPosition spec.registers 4) 4 =
      MarkerTape.canonicalTape final := by
    rw [hregisters]
    exact MarkerSchedule.moveClockBoundary_after_increment final
  have hrun := runner.following spec.outerDistance hshort source searchSlot
    (directRef spec.growth source finishDirectSlot) h final (3 : Fin 4)
    hp (registerValue_lt_outerDistance h (3 : Fin 4)) hfinalCore
    (by omega) (by omega) (boundaryOffset_le_layoutEnd spec.registers 4)
    (by simp [boundaryOffset_four, hcurrentEnd])
    (by
      intro _
      simp [boundaryOffset_four])
    hmove hraw
  have hclockPositive : 0 < spec.registers.get .clock := by
    change 0 < spec.registers.clock
    simpa [RegisterLayout.values] using hp
  have hfinalRegisters : spec.registers.decrement .clock = final := by
    rw [hregisters]
    simp [decrementStageRegisters, Registers.increment, Registers.decrement,
      Registers.set, Registers.get]
  have hfinalBack := decrementTape_backedBy hback .clock hclockPositive
  have hfinalTape : decrementTape spec .clock T = desiredTape := by
    rw [hfinalBack.installed, hdesired.installed]
    simp [decrementSpec, updateSpec, hfinalRegisters]
  have hrun' : FullTM0.CompletesOr
      (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨spec.growth, source, searchSlot⟩,
        atLogical spec.growth T
          (firstGapOffset spec.registers (3 : Fin 4))⟩
      ⟨resolve base c (directRef spec.growth source finishDirectSlot),
        atLogical spec.growth (decrementTape spec .clock T)
          (layoutEnd spec.registers)⟩ := by
    simpa [decrementTape, clearOldLayoutEnd, hfinalRegisters,
      boundaryOffset_four] using hrun
  simpa [hcurrentEnd, hfinalTape] using hrun'

/-- Finish the one-stage clock schedule directly from its tested boundary. -/
private theorem decrementFinalFirst_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : DecrementScheduleRunner base c Short Failure)
    (source searchSlot : Nat)
    (final : Registers)
    {spec : Spec numTags} {T outer desiredTape :
      FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hregisters : spec.registers =
      decrementStageRegisters final .clock)
    (hshort : Short spec.outerDistance)
    (hfinalCore : layoutEnd final < spec.outerDistance)
    (hdesired : BackedBy (updateSpec spec final hfinalCore)
      desiredTape outer)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, source, searchSlot⟩ 4 .right .left
      (directRef spec.growth source finishDirectSlot) (some .right) none ∈
        rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨spec.growth, source, searchSlot⟩,
        atLogical spec.growth T (boundaryOffset spec.registers 4)⟩
      ⟨resolve base c (directRef spec.growth source finishDirectSlot),
        atLogical spec.growth desiredTape (layoutEnd final + 1)⟩ := by
  have h := hback.represents
  have hp : 0 < RegisterLayout.values spec.registers (3 : Fin 4) := by
    rw [hregisters]
    exact decrementStage_positive final .clock
  have hcurrentEnd : layoutEnd spec.registers = layoutEnd final + 1 := by
    rw [hregisters, decrementStage_layoutEnd]
  have hmove : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape spec.registers)
      (MarkerTape.boundaryPosition spec.registers 4) 4 =
      MarkerTape.canonicalTape final := by
    rw [hregisters]
    exact MarkerSchedule.moveClockBoundary_after_increment final
  have hrun := runner.first spec.outerDistance hshort source searchSlot
    (directRef spec.growth source finishDirectSlot)
    (Nat.zero_lt_of_lt spec.core_before_target) h final (3 : Fin 4) hp
    hfinalCore (by omega) (by omega)
    (boundaryOffset_le_layoutEnd spec.registers 4)
    (by simp [boundaryOffset_four, hcurrentEnd])
    (by intro _; simp [boundaryOffset_four]) hmove hraw
  have hclockPositive : 0 < spec.registers.get .clock := by
    change 0 < spec.registers.clock
    simpa [RegisterLayout.values] using hp
  have hfinalRegisters : spec.registers.decrement .clock = final := by
    rw [hregisters]
    simp [decrementStageRegisters, Registers.increment, Registers.decrement,
      Registers.set, Registers.get]
  have hfinalBack := decrementTape_backedBy hback .clock hclockPositive
  have hfinalTape : decrementTape spec .clock T = desiredTape := by
    rw [hfinalBack.installed, hdesired.installed]
    simp [decrementSpec, updateSpec, hfinalRegisters]
  have hrun' : FullTM0.CompletesOr
      (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨spec.growth, source, searchSlot⟩,
        atLogical spec.growth T (boundaryOffset spec.registers 4)⟩
      ⟨resolve base c (directRef spec.growth source finishDirectSlot),
        atLogical spec.growth (decrementTape spec .clock T)
          (layoutEnd spec.registers)⟩ := by
    simpa [decrementTape, clearOldLayoutEnd, hfinalRegisters,
      boundaryOffset_four] using hrun
  simpa [hcurrentEnd, hfinalTape] using hrun'

/-- Fold all noninitial stages of a decrement suffix. -/
private theorem decrementFollowingChain_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : DecrementScheduleRunner base c Short Failure)
    (source searchSlot : Nat) (final : Registers)
    {stage : Register} {stages : List Register}
    (hchain : DecrementStageChain stage stages)
    {spec : Spec numTags} {T outer desiredTape :
      FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hregisters : spec.registers = decrementStageRegisters final stage)
    (hshort : Short spec.outerDistance)
    (hfinalCore : layoutEnd final < spec.outerDistance)
    (hdesired : BackedBy (updateSpec spec final hfinalCore)
      desiredTape outer)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommandsAux spec.growth source searchSlot
        (stages.map
          (fun current => (decrementStageIndex current).succ)) →
      raw ∈ rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨spec.growth, source, searchSlot⟩,
        atLogical spec.growth T
          (firstGapOffset spec.registers (decrementStageIndex stage))⟩
      ⟨resolve base c (directRef spec.growth source finishDirectSlot),
        atLogical spec.growth desiredTape (layoutEnd final + 1)⟩ := by
  induction hchain generalizing spec T searchSlot with
  | clock =>
      apply decrementFinalFollowing_with base c Short Failure runner source
        searchSlot final hback hregisters hshort hfinalCore hdesired
      apply hcommands
      simp [decrementShiftCommandsAux, decrementStageIndex]
  | @cons stage next tail hstage hrest ih =>
      let nextRegisters := decrementStageRegisters final next
      have hnextCore : layoutEnd nextRegisters < spec.outerDistance := by
        rw [decrementStage_layoutEnd, ← decrementStage_layoutEnd final stage,
          ← hregisters]
        exact spec.core_before_target
      let U := install nextRegisters spec.growth spec.returnTag
        (writeLogical spec.growth T
          (boundaryOffset spec.registers (decrementStageIndex stage).succ)
          blankSymbol)
      let nextSpec := updateSpec spec nextRegisters hnextCore
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, searchSlot⟩
          (decrementStageIndex stage).succ .right .left
          (searchRef spec.growth source (searchSlot + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommandsAux]
      have hfirst := decrementIntermediateStage_with base c Short Failure
        runner source searchSlot
        (searchRef spec.growth source (searchSlot + 1)) final hstage hback
        hregisters hshort hraw
      have hfirst' : FullTM0.CompletesOr
          (CounterControlNestingBridge.machine base c) Failure
          ⟨searchState base c ⟨spec.growth, source, searchSlot⟩,
            atLogical spec.growth T
              (firstGapOffset spec.registers
                (decrementStageIndex stage))⟩
          ⟨searchState base c ⟨nextSpec.growth, source, searchSlot + 1⟩,
            atLogical nextSpec.growth U
              (firstGapOffset nextSpec.registers
                (decrementStageIndex next))⟩ := by
        have hhead : boundaryOffset spec.registers
              (decrementStageIndex stage).succ =
            firstGapOffset nextRegisters (decrementStageIndex next) := by
          rw [hregisters]
          exact decrementStage_head (final := final) hstage
        simpa [nextSpec, nextRegisters, U, hhead, searchRef,
          CounterControlPlan.resolve] using hfirst.1
      have hnextBack : BackedBy nextSpec U outer := by
        simpa [nextSpec, nextRegisters, U] using hfirst.2
      have hnextShort : Short nextSpec.outerDistance := by
        simpa [nextSpec, updateSpec] using hshort
      have hnextFinalCore : layoutEnd final < nextSpec.outerDistance := by
        simpa [nextSpec, updateSpec] using hfinalCore
      have hnextDesired : BackedBy
          (updateSpec nextSpec final hnextFinalCore) desiredTape outer := by
        simpa [nextSpec, updateSpec] using hdesired
      have hnextCommands : ∀ raw,
          raw ∈ decrementShiftCommandsAux nextSpec.growth source
            (searchSlot + 1)
            ((next :: tail).map
              (fun current => (decrementStageIndex current).succ)) →
          raw ∈ rawCommands := by
        intro raw hraw'
        apply hcommands raw
        simpa [nextSpec, updateSpec, decrementShiftCommandsAux] using
          List.mem_cons_of_mem _ hraw'
      have hrestRun := ih (searchSlot := searchSlot + 1)
        (spec := nextSpec) (T := U) hnextBack rfl hnextShort
        hnextFinalCore hnextDesired hnextCommands
      exact FullTM0.CompletesOr.trans runner.pullback hfirst' hrestRun

/-- Interpret a complete register suffix, using the first-stage runner once
and the following-stage runner for its tail. -/
private theorem decrementChain_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : DecrementScheduleRunner base c Short Failure)
    (source : Nat) (final : Registers)
    {stage : Register} {stages : List Register}
    (hchain : DecrementStageChain stage stages)
    {spec : Spec numTags} {T outer desiredTape :
      FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hregisters : spec.registers = decrementStageRegisters final stage)
    (hshort : Short spec.outerDistance)
    (hfinalCore : layoutEnd final < spec.outerDistance)
    (hdesired : BackedBy (updateSpec spec final hfinalCore)
      desiredTape outer)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommandsAux spec.growth source secondarySearchBase
        (stages.map
          (fun current => (decrementStageIndex current).succ)) →
      raw ∈ rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
        atLogical spec.growth T
          (boundaryOffset spec.registers (decrementStageIndex stage).succ)⟩
      ⟨resolve base c (directRef spec.growth source finishDirectSlot),
        atLogical spec.growth desiredTape (layoutEnd final + 1)⟩ := by
  cases hchain with
  | clock =>
      apply decrementFinalFirst_with base c Short Failure runner source
        secondarySearchBase final hback hregisters hshort hfinalCore hdesired
      apply hcommands
      simp [decrementShiftCommandsAux, decrementStageIndex]
  | @cons stage next tail hstage hrest =>
      let nextRegisters := decrementStageRegisters final next
      have hnextCore : layoutEnd nextRegisters < spec.outerDistance := by
        rw [decrementStage_layoutEnd, ← decrementStage_layoutEnd final stage,
          ← hregisters]
        exact spec.core_before_target
      let U := install nextRegisters spec.growth spec.returnTag
        (writeLogical spec.growth T
          (boundaryOffset spec.registers (decrementStageIndex stage).succ)
          blankSymbol)
      let nextSpec := updateSpec spec nextRegisters hnextCore
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩
          (decrementStageIndex stage).succ .right .left
          (searchRef spec.growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommandsAux]
      have hfirst := decrementFirstIntermediateStage_with base c Short Failure
        runner source secondarySearchBase
        (searchRef spec.growth source (secondarySearchBase + 1)) final hstage
        hback hregisters hshort hraw
      have hfirst' : FullTM0.CompletesOr
          (CounterControlNestingBridge.machine base c) Failure
          ⟨searchState base c
              ⟨spec.growth, source, secondarySearchBase⟩,
            atLogical spec.growth T
              (boundaryOffset spec.registers
                (decrementStageIndex stage).succ)⟩
          ⟨searchState base c
              ⟨nextSpec.growth, source, secondarySearchBase + 1⟩,
            atLogical nextSpec.growth U
              (firstGapOffset nextSpec.registers
                (decrementStageIndex next))⟩ := by
        have hhead : boundaryOffset spec.registers
              (decrementStageIndex stage).succ =
            firstGapOffset nextRegisters (decrementStageIndex next) := by
          rw [hregisters]
          exact decrementStage_head (final := final) hstage
        simpa [nextSpec, nextRegisters, U, hhead, searchRef,
          CounterControlPlan.resolve] using hfirst.1
      have hnextBack : BackedBy nextSpec U outer := by
        simpa [nextSpec, nextRegisters, U] using hfirst.2
      have hnextShort : Short nextSpec.outerDistance := by
        simpa [nextSpec, updateSpec] using hshort
      have hnextFinalCore : layoutEnd final < nextSpec.outerDistance := by
        simpa [nextSpec, updateSpec] using hfinalCore
      have hnextDesired : BackedBy
          (updateSpec nextSpec final hnextFinalCore) desiredTape outer := by
        simpa [nextSpec, updateSpec] using hdesired
      have hnextCommands : ∀ raw,
          raw ∈ decrementShiftCommandsAux nextSpec.growth source
            (secondarySearchBase + 1)
            ((next :: tail).map
              (fun current => (decrementStageIndex current).succ)) →
          raw ∈ rawCommands := by
        intro raw hraw'
        apply hcommands raw
        simpa [nextSpec, updateSpec, decrementShiftCommandsAux] using
          List.mem_cons_of_mem _ hraw'
      have hrestRun := decrementFollowingChain_with base c Short Failure
        runner source (secondarySearchBase + 1) final hrest hnextBack rfl
        hnextShort hnextFinalCore hnextDesired hnextCommands
      exact FullTM0.CompletesOr.trans runner.pullback hfirst' hrestRun

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
  let final := spec.registers.decrement register
  have hregisters : spec.registers =
      decrementStageRegisters final register := by
    symm
    exact MarkerSchedule.increment_decrement_registers
      spec.registers register hpositive
  have hfinalCore : layoutEnd final < spec.outerDistance :=
    (layoutEnd_decrement_lt spec.registers register hpositive).trans
      spec.core_before_target
  have hdesired := decrementTape_backedBy hback register hpositive
  have hdesired' : BackedBy (updateSpec spec final hfinalCore)
      (decrementTape spec register T) outer := by
    simpa [decrementSpec, final] using hdesired
  have hcommandList :
      (decrementStages register).map
          (fun current => (decrementStageIndex current).succ) =
        MarkerShift.decrementOrder register :=
    decrementStages_labels register
  have hrun := decrementChain_with base c Short Failure runner source final
    (decrementStages_chain register) hback hregisters hshort hfinalCore
    hdesired' (by
      intro raw hraw
      apply hcommands raw
      simpa [decrementShiftCommands, hcommandList] using hraw)
  have hend : layoutEnd final + 1 = layoutEnd spec.registers :=
    layoutEnd_decrement_add_one spec.registers register hpositive
  have hstart : (decrementStageIndex register).succ =
      MarkerSchedule.decrementStartBoundary register := by
    cases register <;> rfl
  apply FullTM0.CompletesOr.and_right ?_ hdesired
  simpa [final, hend, hstart] using hrun
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
