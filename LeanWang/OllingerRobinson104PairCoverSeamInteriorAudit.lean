/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamInteriorFaces

/-!
# Executable base audit for seam orientation

For both hierarchy phases, check the first successor board for every corrected
parent index.  Recursive children are excluded by the executable seam tests;
every remaining live horizontal or vertical interior must face away from the
queried point.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamInteriorAudit

open RedShadeCycles ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence PairCoverSeamArithmetic
  PairCoverSeamComposition PairCoverSeamInteriorFaces

def coordinates (phase : Phase) (depth : Nat) : List Nat :=
  (List.range (quarterNorth (successorEast phase depth 0))).filter fun value =>
    quarterSouth (successorWest phase depth 0) < value

def checkParent (phase : Phase) (depth : Nat) (parent : Index) : Bool :=
  let grid := fineGrid phase depth (fun _ _ => parent)
  let coords := coordinates phase depth
  coords.all fun column => coords.all fun row => coords.all fun boundary =>
    let horizontal := Signals.horizontalInterior?
      (componentAt grid column boundary) (quadrantAt column boundary)
    let vertical := Signals.verticalInterior?
      (componentAt grid boundary row) (quadrantAt boundary row)
    (!decide (row < boundary) || horizontal.isNone ||
      !containedVerticalSeamCheck phase depth 0 0 column row boundary ||
      decide (horizontal = some .north)) &&
    (!decide (boundary < row) || horizontal.isNone ||
      !containedVerticalSeamCheck phase depth 0 0 column row boundary ||
      decide (horizontal = some .south)) &&
    (!decide (column < boundary) || vertical.isNone ||
      !containedHorizontalSeamCheck phase depth 0 0 column row boundary ||
      decide (vertical = some .east)) &&
    (!decide (boundary < column) || vertical.isNone ||
      !containedHorizontalSeamCheck phase depth 0 0 column row boundary ||
      decide (vertical = some .west))

def check (phase : Phase) (depth : Nat) : Bool :=
  (List.finRange 104).all fun parent => checkParent phase depth parent

set_option linter.style.nativeDecide false in
theorem odd_zero_eq_true : check .odd 0 = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem even_one_eq_true : check .even 1 = true := by
  native_decide

end PairCoverSeamInteriorAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
