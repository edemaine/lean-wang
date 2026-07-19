/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCoreFrame
import LeanWang.Kari.Hooper.OrientedMarkerTape

/-!
# Shared route geometry on a represented counter core

This module isolates the tape geometry of compiled marker routes from both
finite outer frames and target-free open-frame resolution.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCoreRoutes

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlCoreFrame

noncomputable section

variable {numTags : Nat}

/-! ## Routes on a native tagged frame -/

/-- Exact execution geometry of one marker-route leg on a fixed tagged tape.
The two cases retain natural logical coordinates, avoiding any assertion
about cells outside the finite represented frame. -/
def LegExecutesAt {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (leg : MarkerValidation.Leg) (source finish : Nat) : Prop :=
  match leg.direction with
  | .right =>
      ∃ distance,
        SearchGap (fun symbol => symbol = blankSymbol)
          (Target.boundary leg.target).Matches
          (atLogical growth T (source + 1))
          (OrientedMarkerTape.orientDirection growth .right) distance ∧
        finish = source + distance + 1
  | .left =>
      ∃ distance,
        source = finish + distance + 1 ∧
        SearchGap (fun symbol => symbol = blankSymbol)
          (Target.boundary leg.target).Matches
          (atLogical growth T (finish + distance))
          (OrientedMarkerTape.orientDirection growth .left) distance

/-- Sequential route geometry on one unchanged tagged tape. -/
inductive RouteExecutesAt {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) :
    List MarkerValidation.Leg → Nat → Nat → Prop
  | nil (position) : RouteExecutesAt growth T [] position position
  | cons (leg legs source middle finish)
      (first : LegExecutesAt growth T leg source middle)
      (rest : RouteExecutesAt growth T legs middle finish) :
      RouteExecutesAt growth T (leg :: legs) source finish

/-- A native tagged route whose every boundary position lies strictly before
the active frame's suspended outer target. -/
inductive RouteExecutesWithin {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (limit : Nat) :
    List MarkerValidation.Leg → Nat → Nat → Prop
  | nil (position) (hposition : position < limit) :
      RouteExecutesWithin growth T limit [] position position
  | cons (leg legs source middle finish)
      (hsource : source < limit)
      (first : LegExecutesAt growth T leg source middle)
      (rest : RouteExecutesWithin growth T limit legs middle finish) :
      RouteExecutesWithin growth T limit (leg :: legs) source finish

namespace RouteExecutesWithin

theorem start_lt {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)} {limit : Nat}
    {legs : List MarkerValidation.Leg} {source finish : Nat}
    (h : RouteExecutesWithin growth T limit legs source finish) :
    source < limit := by
  cases h with
  | nil _ hposition => exact hposition
  | cons _ _ _ _ _ hsource _ _ => exact hsource

theorem toExecutesAt {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)} {limit : Nat}
    {legs : List MarkerValidation.Leg} {source finish : Nat}
    (h : RouteExecutesWithin growth T limit legs source finish) :
    RouteExecutesAt growth T legs source finish := by
  induction h with
  | nil position _ => exact RouteExecutesAt.nil position
  | cons leg legs source middle finish _ first _ ih =>
      exact RouteExecutesAt.cons leg legs source middle finish first ih

theorem mono {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)} {limit larger : Nat}
    {legs : List MarkerValidation.Leg} {source finish : Nat}
    (hlimit : limit ≤ larger)
    (h : RouteExecutesWithin growth T limit legs source finish) :
    RouteExecutesWithin growth T larger legs source finish := by
  induction h with
  | nil position hposition =>
      exact .nil position (hposition.trans_le hlimit)
  | cons leg legs source middle finish hsource first rest ih =>
      exact .cons leg legs source middle finish
        (hsource.trans_le hlimit) first ih

end RouteExecutesWithin

namespace RouteExecutesAt

/-- Every finite route admits a numerical bound containing all of its
boundary positions. -/
theorem exists_executesWithin {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    {legs : List MarkerValidation.Leg} {source finish : Nat}
    (h : RouteExecutesAt growth T legs source finish) :
    ∃ limit, RouteExecutesWithin growth T limit legs source finish := by
  induction h with
  | nil position =>
      exact ⟨position + 1, .nil position (by omega)⟩
  | cons leg legs source middle finish first rest ih =>
      rcases ih with ⟨limit, ih⟩
      let larger := max (source + 1) limit
      have hsource : source < larger := by
        dsimp [larger]
        omega
      have hlimit : limit ≤ larger := by
        simp [larger]
      exact ⟨larger, .cons leg legs source middle finish hsource first
        (RouteExecutesWithin.mono hlimit ih)⟩

end RouteExecutesAt


/-! ## Canonical routes on a represented core -/


/-- One leftward route leg between adjacent represented boundaries. -/
theorem leftLeg_executesAt_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T) (i : Fin 4) :
    LegExecutesAt growth T ⟨i.castSucc, .left⟩
      (boundaryOffset registers i.succ)
      (boundaryOffset registers i.castSucc) := by
  rw [LegExecutesAt]
  refine ⟨RegisterLayout.values registers i, ?_, ?_⟩
  · simp only [boundaryOffset, Fin.val_succ, Fin.val_castSucc,
      CounterLayout.boundaryPos_succ]
    omega
  · change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.castSucc)
      (atLogical growth T
        (boundaryOffset registers i.castSucc +
          RegisterLayout.values registers i))
      (OrientedMarkerTape.orientDirection growth .left)
      (RegisterLayout.values registers i)
    simpa only [boundaryOffset, lastGapOffset, Fin.val_castSucc,
      CounterLayout.boundaryPos_succ, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h.searchGap_adjacent_left i

/-- One rightward route leg between adjacent represented boundaries. -/
theorem rightLeg_executesAt_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T) (i : Fin 4) :
    LegExecutesAt growth T ⟨i.succ, .right⟩
      (boundaryOffset registers i.castSucc)
      (boundaryOffset registers i.succ) := by
  rw [LegExecutesAt]
  refine ⟨RegisterLayout.values registers i, ?_, ?_⟩
  · change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ)
      (atLogical growth T
        (boundaryOffset registers i.castSucc + 1))
      (OrientedMarkerTape.orientDirection growth .right)
      (RegisterLayout.values registers i)
    simpa only [boundaryOffset, firstGapOffset, Fin.val_castSucc,
      Nat.add_assoc, one_add_one_eq_two] using
        h.searchGap_adjacent_right i
  · simp only [boundaryOffset, Fin.val_succ, Fin.val_castSucc,
      CounterLayout.boundaryPos_succ]
    omega

/-- Every represented boundary coordinate lies before any limit strictly
beyond boundary `4`. -/
theorem boundaryOffset_lt_limit_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (_h : CoreRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit)
    (label : Fin 5) :
    boundaryOffset registers label < limit := by
  apply lt_of_le_of_lt _ hlimit
  simp only [boundaryOffset, layoutEnd]
  apply Nat.add_le_add_right
  exact CounterLayout.boundaryPos_mono
    (RegisterLayout.values registers) (by omega)

/-- The eight-leg validation sweep uses only the represented five-boundary
core.  The arbitrary `limit` is bookkeeping for the resolving search API;
it is not the position of an actual target. -/
theorem validation_executesWithin_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit) :
    RouteExecutesWithin growth T limit MarkerValidation.sweep
      (layoutEnd registers) (layoutEnd registers) := by
  change RouteExecutesWithin growth T limit _
    (boundaryOffset registers 4) (boundaryOffset registers 4)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 3) _
    (boundaryOffset_lt_limit_of_core h hlimit 4)
    (leftLeg_executesAt_of_core h 3)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 2) _
    (boundaryOffset_lt_limit_of_core h hlimit 3)
    (leftLeg_executesAt_of_core h 2)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 1) _
    (boundaryOffset_lt_limit_of_core h hlimit 2)
    (leftLeg_executesAt_of_core h 1)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 0) _
    (boundaryOffset_lt_limit_of_core h hlimit 1)
    (leftLeg_executesAt_of_core h 0)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 1) _
    (boundaryOffset_lt_limit_of_core h hlimit 0)
    (rightLeg_executesAt_of_core h 0)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 2) _
    (boundaryOffset_lt_limit_of_core h hlimit 1)
    (rightLeg_executesAt_of_core h 1)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 3) _
    (boundaryOffset_lt_limit_of_core h hlimit 2)
    (rightLeg_executesAt_of_core h 2)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 4) _
    (boundaryOffset_lt_limit_of_core h hlimit 3)
    (rightLeg_executesAt_of_core h 3)
  exact RouteExecutesWithin.nil _
    (boundaryOffset_lt_limit_of_core h hlimit 4)

/-- Navigation from boundary `4` to the predecessor of the selected register
gap uses only adjacent boundaries of the core. -/
theorem routeToDecrementStart_executesWithin_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit)
    (register : Register) :
    RouteExecutesWithin growth T limit
      (AnchoredCounterGeometry.routeToDecrementStart register)
      (layoutEnd registers)
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register)) := by
  change RouteExecutesWithin growth T limit _
    (boundaryOffset registers 4) _
  cases register with
  | left =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
        (leftLeg_executesAt_of_core h 3)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 2) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (leftLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 1) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (leftLeg_executesAt_of_core h 1)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 1)
  | right =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
        (leftLeg_executesAt_of_core h 3)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 2) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (leftLeg_executesAt_of_core h 2)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
  | temp =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
        (leftLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
  | clock =>
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)

/-- Navigation from the shifted boundary back to boundary `4` after an
increment uses only adjacent boundaries of the updated core. -/
theorem routeFromIncrement_executesWithin_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit)
    (register : Register) :
    RouteExecutesWithin growth T limit
      (AnchoredCounterGeometry.routeFromIncrement register)
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register))
      (layoutEnd registers) := by
  change RouteExecutesWithin growth T limit _ _
    (boundaryOffset registers 4)
  cases register with
  | left =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 2) _
        (boundaryOffset_lt_limit_of_core h hlimit 1)
        (rightLeg_executesAt_of_core h 1)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (rightLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | right =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (rightLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | temp =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | clock =>
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)

/-- The zero-test recovery route returns from the empty selected gap to
boundary `4`, again using only represented adjacent-boundary searches. -/
theorem routeFromZero_executesWithin_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit)
    (register : Register) :
    RouteExecutesWithin growth T limit
      (AnchoredCounterGeometry.routeFromZero register)
      (boundaryOffset registers
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (layoutEnd registers) := by
  change RouteExecutesWithin growth T limit _ _
    (boundaryOffset registers 4)
  cases register with
  | left =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 1) _
        (boundaryOffset_lt_limit_of_core h hlimit 0)
        (rightLeg_executesAt_of_core h 0)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 2) _
        (boundaryOffset_lt_limit_of_core h hlimit 1)
        (rightLeg_executesAt_of_core h 1)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (rightLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | right =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 2) _
        (boundaryOffset_lt_limit_of_core h hlimit 1)
        (rightLeg_executesAt_of_core h 1)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (rightLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | temp =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (rightLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | clock =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)


end

end CounterControlCoreRoutes
end Hooper
end Kari
end LeanWang
