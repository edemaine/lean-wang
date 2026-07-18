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
              simp [orient, FullTM0.Tape.read_moveN,
                FullTM0.Tape.move, FullTM0.Tape.moveN,
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

end

end CounterControlGuardedDecrementPositiveEmbedding
end Hooper
end Kari
end LeanWang
