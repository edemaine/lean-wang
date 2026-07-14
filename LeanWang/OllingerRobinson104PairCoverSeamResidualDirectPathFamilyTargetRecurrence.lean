/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyPairRecurrence
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathTargets

/-!
# Recurrence for same-family residual targets

The literal sparse copy of a source/target certificate survives two
substitutions.  This module also records the arithmetic fact used by the
created-coordinate branch: a coarse parallel target remains strictly between
an arbitrary point of the corresponding fine sparse interval and the sparse
copy of the coarse boundary.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetRecurrence

open RedCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyPairRecurrence
  PairCoverSeamResidualDirectPathTargets
  RefinedCoordinateProjection Signals.FreeCellLocal

set_option maxRecDepth 20000

@[simp] theorem horizontalPort_sparse
    (grid : Nat → Nat → Index) (x y : Nat) :
    horizontalPort (iterateRefine 2 grid)
        (sparseCoordinate x) (sparseCoordinate y) =
      sparsePort (horizontalPort grid x y) := by
  unfold horizontalPort
  rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]
  unfold sparsePort
  split <;> rfl

@[simp] theorem verticalPort_sparse
    (grid : Nat → Nat → Index) (x y : Nat) :
    verticalPort (iterateRefine 2 grid)
        (sparseCoordinate x) (sparseCoordinate y) =
      sparsePort (verticalPort grid x y) := by
  unfold verticalPort
  rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]
  unfold sparsePort
  split <;> rfl

theorem horizontalInterior_sparse
    (grid : Nat → Nat → Index) (x y : Nat) :
    Signals.horizontalInterior?
        (componentAt (iterateRefine 2 grid)
          (sparseCoordinate x) (sparseCoordinate y))
        (quadrantAt (sparseCoordinate x) (sparseCoordinate y)) =
      Signals.horizontalInterior?
        (componentAt grid x y) (quadrantAt x y) := by
  rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]

theorem verticalInterior_sparse
    (grid : Nat → Nat → Index) (x y : Nat) :
    Signals.verticalInterior?
        (componentAt (iterateRefine 2 grid)
          (sparseCoordinate x) (sparseCoordinate y))
        (quadrantAt (sparseCoordinate x) (sparseCoordinate y)) =
      Signals.verticalInterior?
        (componentAt grid x y) (quadrantAt x y) := by
  rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]

/-- A strict coarse between-point remains between an arbitrary point of the
fine interval selected by the first endpoint and the sparse second endpoint. -/
theorem strictBetween_sparse_of_coarseCoordinate
    {first second value fine : Nat}
    (firstEq : coarseCoordinate fine = first)
    (between : StrictBetween first second value) :
    StrictBetween fine (sparseCoordinate second) (sparseCoordinate value) := by
  have fineBounds := coarseCoordinate_spec fine
  rw [firstEq] at fineBounds
  rcases between with between | between
  · left
    have nextLe : first + 1 ≤ value := by omega
    have fineTarget : fine < sparseCoordinate value :=
      fineBounds.2.trans_le (sparseCoordinate_mono nextLe)
    exact ⟨fineTarget, sparseCoordinate_strictMono between.2⟩
  · right
    have nextLe : value + 1 ≤ first := by omega
    have targetFine : sparseCoordinate value < fine :=
      (sparseCoordinate_strictMono (Nat.lt_succ_self value)).trans_le
        ((sparseCoordinate_mono nextLe).trans fineBounds.1)
    exact ⟨sparseCoordinate_strictMono between.1, targetFine⟩

/-- The exact sparse image preserves strict betweenness. -/
theorem strictBetween_sparse
    {first second value : Nat} (between : StrictBetween first second value) :
    StrictBetween (sparseCoordinate first) (sparseCoordinate second)
      (sparseCoordinate value) := by
  rcases between with between | between
  · exact Or.inl ⟨sparseCoordinate_strictMono between.1,
      sparseCoordinate_strictMono between.2⟩
  · exact Or.inr ⟨sparseCoordinate_strictMono between.1,
      sparseCoordinate_strictMono between.2⟩

/-- A common hierarchy family survives on the two literal sparse endpoints. -/
theorem SameFamilyWithin.refineSparse
    {grid : Nat → Nat → Index} {source target : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    (related : SameFamilyWithin grid source target
      outerLevel outerBlockX outerBlockY)
    (sourceLive : portPresent grid source = true)
    (targetLive : portPresent grid target = true) :
    SameFamilyWithin (iterateRefine 2 grid)
      (sparsePort source) (sparsePort target)
      (outerLevel + 2) outerBlockX outerBlockY := by
  exact related.refineThrough sourceLive targetLive
    (Path.refl _) (Path.refl _)

set_option maxHeartbeats 1000000 in
-- Normalizing the dependent refined-grid endpoint is elaboration intensive.
/-- A row target refines to a target for the literal sparse copy of the whole
query. -/
theorem RowFamilyTarget.refineSparse
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {column row boundary : Nat} {family : HierarchyFamily}
    (target : RowFamilyTarget root outerLevel outerBlockX outerBlockY
      outerWest outerEast column row boundary family) :
    RowFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerWest) (4 * outerEast)
      (sparseCoordinate column) (sparseCoordinate row)
      (sparseCoordinate boundary) family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  have gridEq : iterateRefine 2 oldGrid =
      iterateRefine (outerLevel + 2 + 2) root := by
    dsimp only [oldGrid]
    rw [PlaneRedBoards.iterateRefine_add]
    congr 1
    omega
  rcases target with target | target
  · rcases target with
      ⟨targetX, targetWest, targetEast, targetInterior, targetFamily⟩
    have targetInterior' : Signals.verticalInterior?
        (componentAt (iterateRefine 2 oldGrid)
          (sparseCoordinate targetX) (sparseCoordinate row))
        (quadrantAt (sparseCoordinate targetX) (sparseCoordinate row)) ≠
          none := by
      rw [verticalInterior_sparse]
      simpa only [oldGrid] using targetInterior
    have targetFamily' : CanonicalCycleAncestorWithinFamily
        (iterateRefine 2 oldGrid)
        (verticalPort (iterateRefine 2 oldGrid)
          (sparseCoordinate targetX) (sparseCoordinate row))
        (outerLevel + 2) outerBlockX outerBlockY family := by
      rw [verticalPort_sparse]
      apply CanonicalCycleAncestorWithinFamily.refineSparse
      · simpa only [oldGrid] using targetFamily
      · apply verticalPort_present_of_interior
        exact targetInterior
    left
    refine ⟨sparseCoordinate targetX, ?_, ?_, ?_, ?_⟩
    · rw [← sparseCoordinate_quarterWest]
      exact sparseCoordinate_strictMono targetWest
    · rw [← sparseCoordinate_quarterEast]
      exact sparseCoordinate_strictMono targetEast
    · rw [← gridEq]
      exact targetInterior'
    · rw [← gridEq]
      exact targetFamily'
  · rcases target with ⟨targetY, between, targetInterior, targetFamily⟩
    have targetInterior' : Signals.horizontalInterior?
        (componentAt (iterateRefine 2 oldGrid)
          (sparseCoordinate column) (sparseCoordinate targetY))
        (quadrantAt (sparseCoordinate column) (sparseCoordinate targetY)) ≠
          none := by
      rw [horizontalInterior_sparse]
      simpa only [oldGrid] using targetInterior
    have targetFamily' : CanonicalCycleAncestorWithinFamily
        (iterateRefine 2 oldGrid)
        (horizontalPort (iterateRefine 2 oldGrid)
          (sparseCoordinate column) (sparseCoordinate targetY))
        (outerLevel + 2) outerBlockX outerBlockY family := by
      rw [horizontalPort_sparse]
      apply CanonicalCycleAncestorWithinFamily.refineSparse
      · simpa only [oldGrid] using targetFamily
      · apply horizontalPort_present_of_interior
        exact targetInterior
    right
    refine ⟨sparseCoordinate targetY, strictBetween_sparse between, ?_, ?_⟩
    · rw [← gridEq]
      exact targetInterior'
    · rw [← gridEq]
      exact targetFamily'

set_option maxHeartbeats 1000000 in
-- Normalizing the dependent refined-grid endpoint is elaboration intensive.
/-- Column-dual literal-sparse target refinement. -/
theorem ColumnFamilyTarget.refineSparse
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {row column boundary : Nat} {family : HierarchyFamily}
    (target : ColumnFamilyTarget root outerLevel outerBlockX outerBlockY
      outerSouth outerNorth row column boundary family) :
    ColumnFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerSouth) (4 * outerNorth)
      (sparseCoordinate row) (sparseCoordinate column)
      (sparseCoordinate boundary) family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  have gridEq : iterateRefine 2 oldGrid =
      iterateRefine (outerLevel + 2 + 2) root := by
    dsimp only [oldGrid]
    rw [PlaneRedBoards.iterateRefine_add]
    congr 1
    omega
  rcases target with target | target
  · rcases target with
      ⟨targetY, targetSouth, targetNorth, targetInterior, targetFamily⟩
    have targetInterior' : Signals.horizontalInterior?
        (componentAt (iterateRefine 2 oldGrid)
          (sparseCoordinate column) (sparseCoordinate targetY))
        (quadrantAt (sparseCoordinate column) (sparseCoordinate targetY)) ≠
          none := by
      rw [horizontalInterior_sparse]
      simpa only [oldGrid] using targetInterior
    have targetFamily' : CanonicalCycleAncestorWithinFamily
        (iterateRefine 2 oldGrid)
        (horizontalPort (iterateRefine 2 oldGrid)
          (sparseCoordinate column) (sparseCoordinate targetY))
        (outerLevel + 2) outerBlockX outerBlockY family := by
      rw [horizontalPort_sparse]
      apply CanonicalCycleAncestorWithinFamily.refineSparse
      · simpa only [oldGrid] using targetFamily
      · apply horizontalPort_present_of_interior
        exact targetInterior
    left
    refine ⟨sparseCoordinate targetY, ?_, ?_, ?_, ?_⟩
    · rw [← sparseCoordinate_quarterSouth]
      exact sparseCoordinate_strictMono targetSouth
    · rw [← sparseCoordinate_quarterNorth]
      exact sparseCoordinate_strictMono targetNorth
    · rw [← gridEq]
      exact targetInterior'
    · rw [← gridEq]
      exact targetFamily'
  · rcases target with ⟨targetX, between, targetInterior, targetFamily⟩
    have targetInterior' : Signals.verticalInterior?
        (componentAt (iterateRefine 2 oldGrid)
          (sparseCoordinate targetX) (sparseCoordinate row))
        (quadrantAt (sparseCoordinate targetX) (sparseCoordinate row)) ≠
          none := by
      rw [verticalInterior_sparse]
      simpa only [oldGrid] using targetInterior
    have targetFamily' : CanonicalCycleAncestorWithinFamily
        (iterateRefine 2 oldGrid)
        (verticalPort (iterateRefine 2 oldGrid)
          (sparseCoordinate targetX) (sparseCoordinate row))
        (outerLevel + 2) outerBlockX outerBlockY family := by
      rw [verticalPort_sparse]
      apply CanonicalCycleAncestorWithinFamily.refineSparse
      · simpa only [oldGrid] using targetFamily
      · apply verticalPort_present_of_interior
        exact targetInterior
    right
    refine ⟨sparseCoordinate targetX, strictBetween_sparse between, ?_, ?_⟩
    · rw [← gridEq]
      exact targetInterior'
    · rw [← gridEq]
      exact targetFamily'

end PairCoverSeamResidualDirectPathFamilyTargetRecurrence
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
