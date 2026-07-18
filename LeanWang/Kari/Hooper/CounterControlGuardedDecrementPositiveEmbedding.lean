/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedDecrementBranchCompletion
import LeanWang.Kari.Hooper.CounterControlGuardedInwardRouteMargin

/-!
# Embedding the guarded decrement positive branch

The original guarded caller searches left along the decrement-entry route,
while the positive branch later shifts the same boundaries from left to
right.  The roundtrip below pairs those two finite traces.  After the shift
of the original caller's target, the shifted tape agrees with the original
tape strictly to its right.  The next shift must therefore lie beyond the
caller's erased one-cell guard.  The completed shift geometry bounds that
next gap inside the reconstructed core.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedDecrementPositiveEmbedding

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlCoreFrame CounterControlGlobalUnnesting
open CounterControlGuardedSearch
open CounterControlGuardedSearch.GuardedSearch
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlGuardedDecrementBranchSearch
open CounterControlGuardedDecrementBranchCompletion
open CounterControlGuardedInwardRouteMargin
open CounterControlGuardedShiftCompletion
open CounterControlGuardedShiftEmbedding
open CounterControlResumedShiftCoordinates
open CounterControlRouteSuffixMortality

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## The finite outward suffix -/

/-- Boundary labels shifted strictly after `source`, through boundary `4`. -/
def shiftAfter : Fin 5 → List (Fin 5)
  | 0 => [1, 2, 3, 4]
  | 1 => [2, 3, 4]
  | 2 => [3, 4]
  | 3 => [4]
  | 4 => []

@[simp] theorem shiftAfter_castSucc (i : Fin 4) :
    shiftAfter i.castSucc = i.succ :: shiftAfter i.succ := by
  fin_cases i <;> rfl

theorem shiftAfter_label_ne_zero (source label : Fin 5)
    (hlabel : label ∈ shiftAfter source) : label ≠ 0 := by
  fin_cases source <;> fin_cases label <;> simp_all [shiftAfter]

private theorem toBoundary_source_ne_zero
    {source target : Fin 5} {route : List MarkerValidation.Leg}
    (hroute : ToBoundary source target route) (htarget : target ≠ 0) :
    source ≠ 0 := by
  induction hroute with
  | here => exact htarget
  | step i _ _ => exact Fin.succ_ne_zero i

/-! ## Tape agreement after matching route and shift steps -/

/-- A shifted boundary tape agrees with the corresponding pre-shift tape
strictly ahead of the old boundary. -/
structure ShiftedAgainst (direction : Turing.Dir) (source : Fin 5)
    (shifted original : FullTM0.Tape (Symbol numTags)) : Prop where
  blank : shifted.read = blankSymbol
  destination : (shifted.move
    (NestingMachine.opposite direction)).read = boundarySymbol source
  ahead : ∀ k, 0 < k →
    (shifted.moveN direction k).read =
      (original.moveN direction k).read

/-- A marker shift changes only the found cell and its predecessor, so all
strictly forward cells agree with the tape centered on the old target. -/
private theorem shiftStepTape_ahead
    (direction : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (expected : Fin 5) (k : Nat) (hk : 0 < k) :
    ((shiftStepTape direction outer distance expected).moveN
      direction k).read =
    ((outer.moveN direction distance).moveN direction k).read := by
  have hkzero : k ≠ 0 := Nat.ne_of_gt hk
  have hkInt : (0 : Int) < (k : Int) := by exact_mod_cast hk
  cases direction with
  | left =>
      have hoffset : -(k : Int) - 1 ≠ 0 := by omega
      simp [shiftStepTape, FullTM0.Tape.read, FullTM0.Tape.move,
        FullTM0.Tape.moveN, FullTM0.Tape.offset, FullTM0.Tape.write,
        NestingMachine.opposite, hoffset, hkzero]
  | right =>
      have hoffset : (k : Int) + 1 ≠ 0 := by omega
      simp [shiftStepTape, FullTM0.Tape.read, FullTM0.Tape.move,
        FullTM0.Tape.moveN, FullTM0.Tape.offset, FullTM0.Tape.write,
        NestingMachine.opposite, hoffset, hkzero]

private theorem shiftStepTape_read_blank
    (direction : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (expected : Fin 5) :
    (shiftStepTape direction outer distance expected).read = blankSymbol := by
  cases direction <;>
    simp [shiftStepTape, FullTM0.Tape.read, FullTM0.Tape.move,
      FullTM0.Tape.write, NestingMachine.opposite]

/-- Moving to a found target through a leftward gap and then back through
that gap plus the initial departure restores the source-centered tape. -/
private theorem inwardFound_moveN_right
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (distance : Nat) :
    (((T.move (orient growth .left)).moveN
      (orient growth .left) distance).moveN
        (orient growth .right) (distance + 1)) = T := by
  funext position
  cases growth <;>
    simp [orient, FullTM0.Tape.move, FullTM0.Tape.moveN,
      FullTM0.Tape.offset] <;>
    congr 1 <;> omega

/-- A labelled boundary cannot occur at two different first-blank distances
from one tape. -/
private theorem boundaryGap_distance_unique
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {first second : Nat} {target : Fin 5}
    (hfirst : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches T direction first)
    (hsecond : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches T direction second) :
    first = second := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hblank := hsecond.blank hlt
    have hmarked := hfirst.marked
    rw [show T (FullTM0.Tape.offset direction first) =
        boundarySymbol target by simpa [Target.Matches] using hmarked]
      at hblank
    exact blankSymbol_ne_boundarySymbol target hblank.symm
  · have hblank := hfirst.blank hlt
    have hmarked := hsecond.marked
    rw [show T (FullTM0.Tape.offset direction second) =
        boundarySymbol target by simpa [Target.Matches] using hmarked]
      at hblank
    exact blankSymbol_ne_boundarySymbol target hblank.symm

/-- One paired inward-route leg and outward marker shift advances tape
agreement to the next boundary. -/
private theorem ShiftedAgainst.advance
    {growth : Turing.Dir} {lower : Fin 4}
    {lowerShifted upper : FullTM0.Tape (Symbol numTags)}
    {routeDistance shiftDistance : Nat}
    (agreement : ShiftedAgainst (orient growth .right) lower.castSucc
      lowerShifted
      ((upper.move (orient growth .left)).moveN
        (orient growth .left) routeDistance))
    (upperRead : upper.read = boundarySymbol lower.succ)
    (routeGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary lower.castSucc).Matches
      (upper.move (orient growth .left))
      (orient growth .left) routeDistance)
    (shiftGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary lower.succ).Matches lowerShifted
      (orient growth .right) shiftDistance)
    (shiftPositive : 0 < shiftDistance) :
    ShiftedAgainst (orient growth .right) lower.succ
      (shiftStepTape (orient growth .right) lowerShifted shiftDistance
        lower.succ) upper := by
  have hdistance : shiftDistance = routeDistance + 1 := by
    apply boundaryGap_distance_unique shiftGap
    constructor
    · intro k hk
      by_cases hkzero : k = 0
      · subst k
        simpa [FullTM0.Tape.read_moveN] using agreement.blank
      · have hpositive : 0 < k := by omega
        have hahead := agreement.ahead k hpositive
        have hroute :=
          show (((upper.move (orient growth .left)).moveN
              (orient growth .left) routeDistance).moveN
                (orient growth .right) k).read = blankSymbol by
            have hkle : k ≤ routeDistance := by omega
            have hindex : routeDistance - k < routeDistance := by omega
            have hblank := routeGap.blank hindex
            have hcast : ((routeDistance - k : Nat) : Int) =
                (routeDistance : Int) - (k : Int) := by omega
            cases growth <;>
              simp [orient, FullTM0.Tape.move, FullTM0.Tape.moveN,
                FullTM0.Tape.offset, hcast] at hblank ⊢ <;>
              convert hblank using 1 <;> ring_nf
        simpa [FullTM0.Tape.read_moveN] using hahead.trans hroute
    · have hread : (lowerShifted.moveN (orient growth .right)
          (routeDistance + 1)).read = boundarySymbol lower.succ := by
        rw [agreement.ahead (routeDistance + 1) (by omega),
          inwardFound_moveN_right, upperRead]
      simpa [Target.Matches, FullTM0.Tape.read_moveN] using hread
  subst shiftDistance
  refine ⟨shiftStepTape_read_blank _ _ _ _, ?_, ?_⟩
  · exact shiftStepTape_destination _ _ _ _
  · intro k hk
    rw [shiftStepTape_ahead _ _ _ _ k hk]
    calc
      ((lowerShifted.moveN (orient growth .right)
          (routeDistance + 1)).moveN
            (orient growth .right) k).read =
          (lowerShifted.moveN (orient growth .right)
            (routeDistance + 1 + k)).read := by
              rw [FullTM0.Tape.moveN_add]
      _ = (((upper.move (orient growth .left)).moveN
            (orient growth .left) routeDistance).moveN
              (orient growth .right) (routeDistance + 1 + k)).read :=
        agreement.ahead _ (by omega)
      _ = ((upper.moveN (orient growth .right) k)).read := by
        rw [show routeDistance + 1 + k = (routeDistance + 1) + k by omega,
          ← FullTM0.Tape.moveN_add, inwardFound_moveN_right]

/-- Pair an entire retained inward route with the reverse marker-shift
suffix.  The shifted tape at the source boundary then agrees strictly
outward with the tape at which that inward route began. -/
private theorem alignInwardRoute
    {growth : Turing.Dir} {source target : Fin 5}
    {route : List MarkerValidation.Leg}
    (hroute : ToBoundary source target route)
    {originalStart routeFinish shiftedStart shiftFinish :
      FullTM0.Tape (Symbol numTags)}
    (originalRead : originalStart.read = boundarySymbol source)
    (routeTrace : RouteTailGaps growth route originalStart routeFinish)
    (initial : ShiftedAgainst (orient growth .right) target
      shiftedStart routeFinish)
    (shiftTrace : ShiftTailGaps (orient growth .right)
      (shiftAfter target) shiftedStart shiftFinish) :
    ∃ shifted,
      ShiftedAgainst (orient growth .right) source shifted originalStart ∧
      ShiftTailGaps (orient growth .right) (shiftAfter source)
        shifted shiftFinish := by
  induction hroute generalizing originalStart routeFinish shiftedStart with
  | here target =>
      cases routeTrace
      exact ⟨shiftedStart, initial, shiftTrace⟩
  | step i tail ih =>
      cases routeTrace with
      | cons _ _ originalStart routeFinish trace =>
          rcases routeGaps_uncons growth ⟨i.castSucc, .left⟩ _ _ _ trace with
            ⟨routeDistance, routeGap, remainingRoute⟩
          let found :=
            ((originalStart.move (orient growth .left)).moveN
              (orient growth .left) routeDistance)
          have foundRead : found.read = boundarySymbol i.castSucc := by
            change (Target.boundary i.castSucc).Matches found.read
            simpa [found, FullTM0.Tape.read_moveN] using routeGap.marked
          rcases ih foundRead remainingRoute initial shiftTrace with
            ⟨lowerShifted, lowerAgreement, lowerTrace⟩
          rw [shiftAfter_castSucc i] at lowerTrace
          cases lowerTrace with
          | cons _ _ _ shiftDistance shiftGap shiftPositive _ tailTrace =>
              exact ⟨shiftStepTape (orient growth .right) lowerShifted
                shiftDistance i.succ,
                lowerAgreement.advance originalRead routeGap shiftGap
                  shiftPositive,
                tailTrace⟩

/-- Expose the first gap of a nonempty exact marker-shift trace. -/
private theorem shiftTailGaps_uncons
    {direction : Turing.Dir} {expected : Fin 5}
    {remaining : List (Fin 5)}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : ShiftTailGaps direction (expected :: remaining) start finish) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary expected).Matches start direction distance ∧
      0 < distance ∧
      ShiftTailGaps direction remaining
        (shiftStepTape direction start distance expected) finish := by
  cases trace with
  | cons _ _ _ distance gap positive _ tail =>
      exact ⟨distance, gap, positive, tail⟩

/-- The branch handoff selects the first command of the decrement-shift
schedule, so the retained suffix consists exactly of the labels after the
tested boundary. -/
private theorem positivePosition_eq
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (entry : PositiveSearchHandoff current growth source register
      ifZero ifPositive)
    (suffix : DecrementShiftSuffixReached entry.next growth source register) :
    suffix.position.current =
        MarkerSchedule.decrementStartBoundary register ∧
      suffix.position.remaining = shiftAfter
        (MarkerSchedule.decrementStartBoundary register) := by
  have hraw := entry.selectedRaw_eq.symm.trans suffix.position.raw_eq
  have hlength : suffix.position.before.length = 0 := by
    have hslot := congrArg (fun raw : RawCommand => raw.address.slot) hraw
    simp [positiveFirstRaw, RawCommand.address] at hslot
    exact List.length_eq_zero_iff.mpr hslot
  have hbefore : suffix.position.before = [] :=
    List.length_eq_zero_iff.mp hlength
  have hlabels := suffix.position.labels_eq
  rw [hbefore] at hlabels
  simp only [List.nil_append] at hlabels
  cases register with
  | left =>
      simp [MarkerShift.decrementOrder] at hlabels
      exact ⟨hlabels.1.symm, by
        simpa [MarkerSchedule.decrementStartBoundary, shiftAfter] using
          hlabels.2.symm⟩
  | right =>
      simp [MarkerShift.decrementOrder] at hlabels
      exact ⟨hlabels.1.symm, by
        simpa [MarkerSchedule.decrementStartBoundary, shiftAfter] using
          hlabels.2.symm⟩
  | temp =>
      simp [MarkerShift.decrementOrder] at hlabels
      exact ⟨hlabels.1.symm, by
        simpa [MarkerSchedule.decrementStartBoundary, shiftAfter] using
          hlabels.2.symm⟩
  | clock =>
      simp [MarkerShift.decrementOrder] at hlabels
      exact ⟨hlabels.1.symm, by
        simpa [MarkerSchedule.decrementStartBoundary, shiftAfter] using
          hlabels.2⟩

/-- The first positive marker shift is based one cell inward from the
completed decrement-entry route.  Its successful tape is therefore the
initial shifted-against witness at the tested boundary. -/
private theorem positiveInitialAgreement
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (entry : PositiveSearchHandoff current growth source register
      ifZero ifPositive)
    (suffix : DecrementShiftSuffixReached entry.next growth source register)
    (hcurrent : suffix.position.current =
      MarkerSchedule.decrementStartBoundary register) :
    ShiftedAgainst (orient growth .right)
      (MarkerSchedule.decrementStartBoundary register)
      (entry.next.shiftedParentBacking suffix.position.current)
      entry.route.route.suffix.finish := by
  have hdirection : entry.next.direction = orient growth .right := by
    have hdirection := entry.next.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [entry.selectedRaw_eq] at hdirection
    exact hdirection.symm
  have hrestore : entry.next.parentOuter.moveN
      (orient growth .right) 1 = entry.route.route.suffix.finish := by
    have hmove := entry.next.parentOuter_moveN_one
    rw [hdirection, entry.outer_eq] at hmove
    cases growth <;>
      simpa [CounterControlGuardedDecrementEntry.branchTape, orient,
        FullTM0.Tape.move] using hmove
  refine ⟨suffix.handoff.source_blank, ?_, ?_⟩
  · have hdestination := suffix.handoff.destination_boundary
    rw [hdirection] at hdestination
    simpa only [hcurrent] using hdestination
  · intro k hk
    rw [hcurrent]
    unfold GuardedSearch.shiftedParentBacking
    rw [hdirection, entry.distance_eq]
    simp only [Nat.zero_add]
    rw [shiftStepTape_ahead _ _ _ _ k hk, hrestore]

/-- Looking back from a guarded found target through any positive part of
its recovered parent gap still reads blank. -/
private theorem foundTape_opposite_moveN_read_blank
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) (k : Nat)
    (hk : 0 < k) (hle : k ≤ current.current.distance + 1) :
    (current.foundTape.moveN
      (NestingMachine.opposite current.direction) k).read = blankSymbol := by
  let parentDistance := current.current.distance + 1
  have hindex : parentDistance - k < parentDistance := by
    dsimp [parentDistance]
    omega
  have hblank := current.parentGap.blank hindex
  have hcast : ((parentDistance - k : Nat) : Int) =
      (parentDistance : Int) - (k : Int) := by
    dsimp [parentDistance] at ⊢
    omega
  rw [current.foundTape_eq_parentMoveN]
  cases hdirection : current.direction <;>
    simp [hdirection, NestingMachine.opposite, FullTM0.Tape.moveN,
      FullTM0.Tape.offset, parentDistance, hcast]
      at hblank ⊢ <;>
    convert hblank using 1 <;> ring_nf

/-- Any completed outward shift suffix beginning at a nonzero boundary stays
strictly short of canonical boundary `0`. -/
private theorem alignedShift_travel_lt_layoutEnd_sub_one
    {growth : Turing.Dir} {source : Fin 5} {labels : List (Fin 5)}
    {start finish coreTape : FullTM0.Tape (Symbol numTags)}
    (startBoundary :
      (start.move
        (NestingMachine.opposite (orient growth .right))).read =
          boundarySymbol source)
    (sourceNe : source ≠ 0)
    (labelsNe : ∀ label ∈ labels, label ≠ (0 : Fin 5))
    (geometry : ShiftTailBackwardGeometry (orient growth .right)
      labels start finish)
    (registers : Registers)
    (hcore : CoreRepresents registers growth coreTape)
    (hcenter : finish.move (orient growth .left) =
      atLogical growth coreTape (layoutEnd registers)) :
    geometry.travel < layoutEnd registers - 1 := by
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  have hstartAvoid :
      (start.move
        (NestingMachine.opposite (orient growth .right))).read ≠
          boundarySymbol 0 := by
    rw [startBoundary]
    intro heq
    exact sourceNe ((boundarySymbol_injective source 0).mp heq)
  have hfinishEq : finish.move
        (NestingMachine.opposite (orient growth .right)) =
      atLogical growth coreTape (layoutEnd registers) := by
    rw [hopposite]
    exact hcenter
  have hendPositive : 1 < layoutEnd registers := by
    simp [layoutEnd, RegisterLayout.clockBoundary_eq]
  have hboundaryZero :
      ((finish.move
          (NestingMachine.opposite (orient growth .right))).moveN
            (NestingMachine.opposite (orient growth .right))
            (layoutEnd registers - 1)).read = boundarySymbol 0 := by
    rw [hfinishEq, hopposite]
    have hend : layoutEnd registers =
        1 + (layoutEnd registers - 1) := by omega
    conv_lhs =>
      enter [1, 1]
      rw [hend]
    simp only [orient_eq_orientDirection]
    rw [atLogical_moveN_left, atLogical_read]
    simpa using hcore.boundary (0 : Fin 5)
  by_contra hnot
  have hle : layoutEnd registers - 1 ≤ geometry.travel :=
    Nat.le_of_not_gt hnot
  have havoid := geometry.avoids (0 : Fin 5) hstartAvoid labelsNe
    (layoutEnd registers - 1) hle
  exact havoid hboundaryZero

/-! ## Comparing the original caller with the reconstructed endpoint -/

/-- The completed positive branch contains the original decrement-entry
caller, not merely the distance-zero shift search produced by the branch. -/
theorem positiveOriginal_distance_lt_layoutEnd
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : PositiveLogicalHandoff current growth source register
      ifZero ifPositive)
    (endpoint : DecrementPositiveCenteredEnd handoff.entry.next growth source
      register ifZero ifPositive handoff.direct) :
    current.current.distance < layoutEnd endpoint.core.registers := by
  rcases positivePosition_eq handoff.entry handoff.direct.suffix with
    ⟨hshiftCurrent, hshiftRemaining⟩
  rcases (routeToDecrementStart_toBoundary register).position
      handoff.entry.route.route.suffix.route_eq with
    ⟨i, hrouteCurrent, hrouteTail⟩
  have hrouteRead : current.foundTape.read =
      boundarySymbol i.castSucc := by
    have hread := handoff.entry.route.route.current_read
    rw [hrouteCurrent] at hread
    exact hread
  have hinitial := positiveInitialAgreement handoff.entry
    handoff.direct.suffix hshiftCurrent
  have hshiftTrace := handoff.direct.suffix.tailGaps
  rw [hshiftRemaining] at hshiftTrace
  rcases alignInwardRoute hrouteTail hrouteRead
      handoff.entry.route.route.suffix.tailGaps hinitial hshiftTrace with
    ⟨aligned, agreement, alignedTrace⟩
  rw [shiftAfter_castSucc i] at alignedTrace
  rcases shiftTailGaps_uncons alignedTrace with
    ⟨shiftDistance, shiftGap, shiftPositive, tailTrace⟩
  have hdirection : current.direction = orient growth .left := by
    have hdirection := current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [handoff.entry.route.route.suffix.raw_eq, hrouteCurrent]
      at hdirection
    exact hdirection.symm
  have hopposite : NestingMachine.opposite (orient growth .left) =
      orient growth .right := by
    cases growth <;> rfl
  have hdistance : current.current.distance + 1 < shiftDistance := by
    by_contra hnot
    have hle : shiftDistance ≤ current.current.distance + 1 :=
      Nat.le_of_not_gt hnot
    have hblank := foundTape_opposite_moveN_read_blank current shiftDistance
      shiftPositive hle
    rw [hdirection, hopposite] at hblank
    have hmarked : (aligned.moveN (orient growth .right)
        shiftDistance).read = boundarySymbol i.succ := by
      simpa [Target.Matches, FullTM0.Tape.read_moveN] using shiftGap.marked
    have hfoundMarked :=
      (agreement.ahead shiftDistance shiftPositive).symm.trans hmarked
    exact blankSymbol_ne_boundarySymbol i.succ
      (hblank.symm.trans hfoundMarked)
  have hsourceNe : i.castSucc ≠ (0 : Fin 5) := by
    apply toBoundary_source_ne_zero hrouteTail
    cases register <;> decide
  rcases shiftTailGaps_backwardGeometry tailTrace with ⟨tailGeometry⟩
  let geometry := tailGeometry.prepend shiftGap shiftPositive
  have hlabelsNe : ∀ label ∈ i.succ :: shiftAfter i.succ,
      label ≠ (0 : Fin 5) := by
    intro label hlabel
    simp only [List.mem_cons] at hlabel
    rcases hlabel with rfl | hlabel
    · exact Fin.succ_ne_zero i
    · exact shiftAfter_label_ne_zero i.succ label hlabel
  have hcenter : handoff.direct.suffix.finish.move
        (orient growth .left) =
      atLogical growth endpoint.core.tape
        (layoutEnd endpoint.core.registers) := by
    simpa [decrementPositiveTape] using endpoint.center
  have htravel := alignedShift_travel_lt_layoutEnd_sub_one
    agreement.destination hsourceNe hlabelsNe geometry endpoint.core.registers
    endpoint.core_represents hcenter
  have htravelEq : geometry.travel =
      tailGeometry.travel + shiftDistance := rfl
  omega

end

end CounterControlGuardedDecrementPositiveEmbedding
end Hooper
end Kari
end LeanWang
