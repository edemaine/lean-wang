/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlRouteSuffixMortality

/-!
# Exact roundtrips across preserving boundary gaps

An outward preserving route and its inward reverse see the same blank gap.
Consequently their first-target distances agree, and the reverse found tape
is exactly the original source-centered tape.  This tape-only fact is shared
by instruction continuations which meet an earlier validation boundary on a
later inward route.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlRouteRoundtrip

open Turing
open BoundedMarkerProgram CounterControlPlan

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

theorem move_move_opposite
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir) :
    (T.move direction).move (NestingMachine.opposite direction) = T := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.move]

@[simp] theorem opposite_orient_left (growth : Turing.Dir) :
    NestingMachine.opposite (orient growth .left) = orient growth .right := by
  cases growth <;> rfl

@[simp] theorem opposite_orient_right (growth : Turing.Dir) :
    NestingMachine.opposite (orient growth .right) = orient growth .left := by
  cases growth <;> rfl

/-- Moving back across a reversed search gap returns to the cell immediately
behind the original search head. -/
theorem reverseGap_finish
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir)
    (distance : Nat) :
    (((T.moveN direction distance).move
        (NestingMachine.opposite direction)).moveN
      (NestingMachine.opposite direction) distance) =
        T.move (NestingMachine.opposite direction) := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.moveN,
      FullTM0.Tape.offset, FullTM0.Tape.move] <;>
    congr 1 <;> ring

/-- A departure, an arbitrary preserving search, its reversed search, and a
second departure end one cell beyond the original boundary. -/
theorem reverseGap_continue
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir)
    (distance : Nat) :
    (((((T.move direction).moveN direction distance).move
        (NestingMachine.opposite direction)).moveN
      (NestingMachine.opposite direction) distance).move
        (NestingMachine.opposite direction)) =
      T.move (NestingMachine.opposite direction) := by
  rw [reverseGap_finish]
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.move]

/-- Returning across a one-cell departure exposes the boundary found by the
preceding preserving search. -/
theorem read_return_of_gap
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {distance : Nat} {target : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches T direction distance) :
    (((T.moveN direction distance).move direction).move
      (NestingMachine.opposite direction)).read = boundarySymbol target := by
  have hmarked : (T.moveN direction distance).read =
      boundarySymbol target := by
    simpa [FullTM0.Tape.read_moveN, Target.Matches] using hgap.marked
  cases direction <;>
    simpa [NestingMachine.opposite, FullTM0.Tape.read,
      FullTM0.Tape.move] using hmarked

/-- Reverse the cells of one exact blank gap, starting one cell beyond its
found target. -/
theorem reverseGap_of_source_boundary
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {distance : Nat} {found source : Fin 5}
    (gap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary found).Matches T direction distance)
    (source_read : (T.move
      (NestingMachine.opposite direction)).read = boundarySymbol source) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      ((T.moveN direction distance).move
        (NestingMachine.opposite direction))
      (NestingMachine.opposite direction) distance := by
  constructor
  · intro i hi
    let j := distance - i - 1
    have hj : j < distance := by
      dsimp [j]
      omega
    have hblank := gap.blank hj
    cases direction with
    | left =>
        simp only [NestingMachine.opposite,
          FullTM0.Tape.move_apply_delta, FullTM0.Tape.moveN_apply,
          FullTM0.Tape.offset_left, FullTM0.Tape.offset_right,
          FullTM0.Tape.delta_right] at hblank ⊢
        rw [show -(j : Int) = (i : Int) + 1 - (distance : Int) by
          dsimp [j]
          omega] at hblank
        exact hblank
    | right =>
        simp only [NestingMachine.opposite,
          FullTM0.Tape.move_apply_delta, FullTM0.Tape.moveN_apply,
          FullTM0.Tape.offset_left, FullTM0.Tape.offset_right,
          FullTM0.Tape.delta_left] at hblank ⊢
        rw [show (j : Int) = -(i : Int) - 1 + (distance : Int) by
          dsimp [j]
          omega] at hblank
        exact hblank
  · cases direction <;>
      simpa [Target.Matches, FullTM0.Tape.read,
        NestingMachine.opposite, FullTM0.Tape.move_apply_delta,
        FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_left,
        FullTM0.Tape.offset_right, FullTM0.Tape.delta_left,
        FullTM0.Tape.delta_right] using source_read

/-- Match one inward gap with its reverse, including the departure needed to
continue reversing the surrounding route. -/
theorem reverseGap_pair_continue
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {inwardDistance returnDistance : Nat} {source target : Fin 5}
    (hsource : T.read = boundarySymbol source)
    (inward : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches (T.move direction) direction
      inwardDistance)
    (returnGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      (((T.move direction).moveN direction inwardDistance).move
        (NestingMachine.opposite direction))
      (NestingMachine.opposite direction) returnDistance) :
    returnDistance = inwardDistance ∧
      (((((T.move direction).moveN direction inwardDistance).move
          (NestingMachine.opposite direction)).moveN
            (NestingMachine.opposite direction) returnDistance).move
              (NestingMachine.opposite direction)) =
        T.move (NestingMachine.opposite direction) := by
  have hsource' : ((T.move direction).move
      (NestingMachine.opposite direction)).read = boundarySymbol source := by
    rw [move_move_opposite]
    exact hsource
  have hreverse := reverseGap_of_source_boundary inward hsource'
  have hdistance := boundaryGap_distance_unique returnGap hreverse
  subst returnDistance
  exact ⟨rfl, reverseGap_continue T direction inwardDistance⟩

/-- Match the outermost inward gap with its reverse.  With no following
departure, the found tape is exactly the original boundary-centered tape. -/
theorem reverseGap_pair_finish
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {inwardDistance returnDistance : Nat} {source target : Fin 5}
    (hsource : T.read = boundarySymbol source)
    (inward : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches (T.move direction) direction
      inwardDistance)
    (returnGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      (((T.move direction).moveN direction inwardDistance).move
        (NestingMachine.opposite direction))
      (NestingMachine.opposite direction) returnDistance) :
    returnDistance = inwardDistance ∧
      ((((T.move direction).moveN direction inwardDistance).move
          (NestingMachine.opposite direction)).moveN
            (NestingMachine.opposite direction) returnDistance) = T := by
  have hsource' : ((T.move direction).move
      (NestingMachine.opposite direction)).read = boundarySymbol source := by
    rw [move_move_opposite]
    exact hsource
  have hreverse := reverseGap_of_source_boundary inward hsource'
  have hdistance := boundaryGap_distance_unique returnGap hreverse
  subst returnDistance
  refine ⟨rfl, ?_⟩
  rw [reverseGap_finish, move_move_opposite]

/-- Traversing one preserving boundary gap and then its reverse returns to
the identical source-centered tape. -/
theorem reverseRouteLeg_found_eq
    {sourceTape reverseFound : FullTM0.Tape (Symbol numTags)}
    {direction : Turing.Dir} {outwardDistance inwardDistance : Nat}
    {source target : Fin 5}
    (source_read : sourceTape.read = boundarySymbol source)
    (outwardGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches (sourceTape.move direction)
      direction outwardDistance)
    (inwardGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      (((sourceTape.move direction).moveN direction outwardDistance).move
        (NestingMachine.opposite direction))
      (NestingMachine.opposite direction) inwardDistance)
    (reverseFound_eq : reverseFound =
      (((sourceTape.move direction).moveN direction outwardDistance).move
        (NestingMachine.opposite direction)).moveN
          (NestingMachine.opposite direction) inwardDistance) :
    reverseFound = sourceTape := by
  have hsource : ((sourceTape.move direction).move
      (NestingMachine.opposite direction)).read = boundarySymbol source := by
    rw [move_move_opposite]
    exact source_read
  have hreverse := reverseGap_of_source_boundary outwardGap hsource
  have hdistance : inwardDistance = outwardDistance :=
    BoundedMarkerProgram.boundaryGap_distance_unique inwardGap hreverse
  subst inwardDistance
  rw [reverseFound_eq]
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.move,
      FullTM0.Tape.moveN, FullTM0.Tape.offset] <;>
    congr 1 <;> omega

end

end CounterControlRouteRoundtrip
end Hooper
end Kari
end LeanWang
