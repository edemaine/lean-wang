/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedLocalAuditCheck

/-!
# Finite paths for created source-boundary queries

The exceptional projection `query = boundary` is not a strict wrong-facing
query, so it is absent from the ordinary created-coordinate audit.  This file
checks precisely that one additional local shape and its column dual.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedSourceBoundaryAuditCheck

open RedShadeGraphRefinement PairCoverSeamCreatedLocalAuditCheck
  PairCoverSeamPathBaseAudit Signals.FreeCellLocal

set_option maxRecDepth 20000

def verticalQueries (grid : Nat → Nat → Index)
    (column boundary : Nat) : List Nat :=
  coordinates.filter fun row =>
    decide (row = boundary) && isCreated boundary &&
      decide (Signals.horizontalInterior?
        (componentAt grid column boundary) (quadrantAt column boundary) =
          some .north)

def horizontalQueries (grid : Nat → Nat → Index)
    (row boundary : Nat) : List Nat :=
  coordinates.filter fun column =>
    decide (column = boundary) && isCreated boundary &&
      decide (Signals.verticalInterior?
        (componentAt grid boundary row) (quadrantAt boundary row) =
          some .east)

def checkVerticalParent (parent : Index) : Bool :=
  let grid := fineGrid parent
  coordinates.all fun column => coordinates.all fun boundary =>
    verticalQueriesCheck grid 8 129 513 0 4 column boundary
      (verticalQueries grid column boundary)

def checkHorizontalParent (parent : Index) : Bool :=
  let grid := fineGrid parent
  coordinates.all fun row => coordinates.all fun boundary =>
    horizontalQueriesCheck grid 8 129 513 0 4 row boundary
      (horizontalQueries grid row boundary)

def completeCheck : Bool :=
  (List.finRange 104).all fun parent =>
    checkVerticalParent parent && checkHorizontalParent parent

set_option linter.style.nativeDecide false in
theorem complete : completeCheck = true := by
  native_decide

end PairCoverSeamCreatedSourceBoundaryAuditCheck
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
