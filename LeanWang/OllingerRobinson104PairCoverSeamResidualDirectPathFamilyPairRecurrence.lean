/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyPredecessor

/-!
# Recurrence for same-family endpoint pairs

Residual target recognition is a relation between a selected source and a
candidate endpoint, not two independent family searches.  If both fine ports
have even connectors to coarse predecessors in one hierarchy family, two
substitutions preserve that common family.  This is the semantic induction
step behind the projected target search.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyPairRecurrence

open RedCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamShadePaths PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualCyclePredecessorTransport
  PairCoverSeamResidualDirectPathBridges
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Two ports reach canonical cycles in one common hierarchy family. -/
def SameFamilyWithin
    (grid : Nat → Nat → Index) (source target : Port)
    (outerLevel outerBlockX outerBlockY : Nat) : Prop :=
  ∃ family,
    CanonicalCycleAncestorWithinFamily grid source
      outerLevel outerBlockX outerBlockY family ∧
    CanonicalCycleAncestorWithinFamily grid target
      outerLevel outerBlockX outerBlockY family

theorem SameFamilyWithin.symm
    {grid : Nat → Nat → Index} {source target : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    (related : SameFamilyWithin grid source target
      outerLevel outerBlockX outerBlockY) :
    SameFamilyWithin grid target source
      outerLevel outerBlockX outerBlockY := by
  rcases related with ⟨family, sourceFamily, targetFamily⟩
  exact ⟨family, targetFamily, sourceFamily⟩

/-- Even endpoint connectors preserve a common hierarchy family under two
substitutions. -/
theorem SameFamilyWithin.refineThrough
    {grid : Nat → Nat → Index} {oldSource oldTarget source target : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    (related : SameFamilyWithin grid oldSource oldTarget
      outerLevel outerBlockX outerBlockY)
    (oldSourceLive : portPresent grid oldSource = true)
    (oldTargetLive : portPresent grid oldTarget = true)
    (sourceConnector : Path (iterateRefine 2 grid)
      source (sparsePort oldSource) false)
    (targetConnector : Path (iterateRefine 2 grid)
      target (sparsePort oldTarget) false) :
    SameFamilyWithin (iterateRefine 2 grid) source target
      (outerLevel + 2) outerBlockX outerBlockY := by
  rcases related with ⟨family, sourceFamily, targetFamily⟩
  exact ⟨family,
    sourceFamily.refineThrough oldSourceLive sourceConnector,
    targetFamily.refineThrough oldTargetLive targetConnector⟩

/-- A fine port with an even connector to a live coarse predecessor. -/
def EvenPredecessor (grid : Nat → Nat → Index) (target : Port) : Prop :=
  ∃ source,
    portPresent grid source = true ∧
    Path (iterateRefine 2 grid) target (sparsePort source) false

/-- The audited horizontal predecessor is an orientation-independent even
predecessor. -/
theorem HorizontalPredecessor.toEvenPredecessor
    {grid : Nat → Nat → Index} {column boundary : Nat}
    (predecessor : HorizontalPredecessor grid column boundary) :
    EvenPredecessor grid
      (horizontalPort (iterateRefine 2 grid) column boundary) := by
  rcases predecessor with
    ⟨oldColumn, oldBoundary, _sameBlock, _boundarySparse,
      oldInterior, connector⟩
  exact ⟨horizontalPort grid oldColumn oldBoundary,
    horizontalPort_present_of_interior oldInterior, connector⟩

/-- Vertical dual of `HorizontalPredecessor.toEvenPredecessor`. -/
theorem VerticalPredecessor.toEvenPredecessor
    {grid : Nat → Nat → Index} {boundary row : Nat}
    (predecessor : VerticalPredecessor grid boundary row) :
    EvenPredecessor grid
      (verticalPort (iterateRefine 2 grid) boundary row) := by
  rcases predecessor with
    ⟨oldBoundary, oldRow, _sameBlock, _boundarySparse,
      oldInterior, connector⟩
  exact ⟨verticalPort grid oldBoundary oldRow,
    verticalPort_present_of_interior oldInterior, connector⟩

/-- A paired predecessor certificate retains the coarse same-family relation
needed by the induction step. -/
def SameFamilyPredecessors
    (grid : Nat → Nat → Index) (source target : Port)
    (outerLevel outerBlockX outerBlockY : Nat) : Prop :=
  ∃ oldSource oldTarget,
    portPresent grid oldSource = true ∧
    portPresent grid oldTarget = true ∧
    Path (iterateRefine 2 grid) source (sparsePort oldSource) false ∧
    Path (iterateRefine 2 grid) target (sparsePort oldTarget) false ∧
    SameFamilyWithin grid oldSource oldTarget
      outerLevel outerBlockX outerBlockY

/-- Discharge a fine same-family goal from its paired coarse predecessors. -/
theorem SameFamilyPredecessors.refine
    {grid : Nat → Nat → Index} {source target : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    (predecessors : SameFamilyPredecessors grid source target
      outerLevel outerBlockX outerBlockY) :
    SameFamilyWithin (iterateRefine 2 grid) source target
      (outerLevel + 2) outerBlockX outerBlockY := by
  rcases predecessors with
    ⟨oldSource, oldTarget, oldSourceLive, oldTargetLive,
      sourceConnector, targetConnector, related⟩
  exact related.refineThrough oldSourceLive oldTargetLive
    sourceConnector targetConnector

end PairCoverSeamResidualDirectPathFamilyPairRecurrence
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
