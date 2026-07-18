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

private theorem move_move_opposite
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir) :
    (T.move direction).move (NestingMachine.opposite direction) = T := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.move]

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
