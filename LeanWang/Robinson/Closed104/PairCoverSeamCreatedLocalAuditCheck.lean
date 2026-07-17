/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPathQuerySearch
import LeanWang.Robinson.Closed104.RedShadeGraphRefinementAudit

/-!
# Finite local paths for created seam coordinates

Inside one two-substitution macrocell, a wrong-facing seam has an even path
whenever its selected boundary is created.  The same holds when its boundary
and free-line coordinate are sparse but its transverse coordinate is created.
The only created-coordinate family not covered here has a sparse boundary and
a created free-line coordinate.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCreatedLocalAuditCheck

open RedCycles RedShadeCycles RedShadeGraphRefinement
  PairCoverSeamPathBaseAudit Signals.FreeCellLocal

set_option maxRecDepth 20000

def coordinates : List Nat := List.range 8

def isCreated (coordinate : Nat) : Bool :=
  coordinate != 0 && coordinate != 1

def verticalQueries (grid : Nat → Nat → Index)
    (column boundary : Nat) : List Nat :=
  let interior := Signals.horizontalInterior?
    (componentAt grid column boundary) (quadrantAt column boundary)
  coordinates.filter fun row =>
    (((decide (row < boundary) && decide (interior = some .south)) ||
      (decide (boundary < row) && decide (interior = some .north))) &&
      (isCreated boundary || (!isCreated row && isCreated column)))

def horizontalQueries (grid : Nat → Nat → Index)
    (row boundary : Nat) : List Nat :=
  let interior := Signals.verticalInterior?
    (componentAt grid boundary row) (quadrantAt boundary row)
  coordinates.filter fun column =>
    (((decide (column < boundary) && decide (interior = some .west)) ||
      (decide (boundary < column) && decide (interior = some .east))) &&
      (isCreated boundary || (!isCreated column && isCreated row)))

def checkVerticalParent (parent : Index) : Bool :=
  let grid := RedShadeGraphRefinement.fineGrid parent
  coordinates.all fun column => coordinates.all fun boundary =>
    verticalQueriesCheck grid 8 129 513 0 4 column boundary
      (verticalQueries grid column boundary)

def checkHorizontalParent (parent : Index) : Bool :=
  let grid := RedShadeGraphRefinement.fineGrid parent
  coordinates.all fun row => coordinates.all fun boundary =>
    horizontalQueriesCheck grid 8 129 513 0 4 row boundary
      (horizontalQueries grid row boundary)

def completeCheck : Bool :=
  (List.finRange 104).all fun parent =>
    checkVerticalParent parent && checkHorizontalParent parent

set_option linter.style.nativeDecide false in
theorem complete : completeCheck = true := by
  native_decide

end PairCoverSeamCreatedLocalAuditCheck
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
