/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetTransport

/-!
# Finite family-target bases

This module isolates the finite constant-parent checks needed to construct the
global family targets.  The local certificate covers exactly the residual
queries: the selected boundary is sparse and the queried free line is created.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyBase

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  PairCoverSeamArithmetic PairCoverSeamPathSearch
  PairCoverSeamPathBaseAudit PairCoverSeamPathBoundedBase
  PairCoverSeamPathTranslation
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathFamilySearch
  PairCoverSeamResidualDirectPathFamilyTargetSearch
  PairCoverSeamResidualDirectPathFamilyTargetTransport
  PairCoverSeamResidualDirectPathTargets
  RefinedCoordinateProjection
  ShadedFreeLineRecurrence SparseFreeLinePlaneBase Signals.FreeCellLocal
  ShadedObstructionPairCoverRecurrence

set_option maxRecDepth 20000

/-- Executable family-target certificates for every local residual query at
one depth.  The parent tile remains a parameter, so a direct finite audit has
104 constant-parent instances. -/
structure BoundedFamilyTargetsAt
    (phase : Phase) (depth fuel : Nat) : Prop where
  row : ∀ (parent : Index) {column row boundary : Nat},
    column ∈ coordinates phase depth →
    boundary ∈ coordinates phase depth →
    row ∈ verticalQueries phase depth
      (fineGrid phase depth (fun _ _ => parent))
      (coordinates phase depth) column boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate row →
    rowJointCheckFound (fun _ _ => parent) (outerLevel phase depth)
      (familyWidth (outerLevel phase depth))
      (nodes (fun _ _ => parent) (outerLevel phase depth)
        (familyWidth (outerLevel phase depth)) fuel .even)
      (nodes (fun _ _ => parent) (outerLevel phase depth)
        (familyWidth (outerLevel phase depth)) fuel .odd)
      (successorWest phase depth 0) (successorEast phase depth 0)
      column row boundary = true
  column : ∀ (parent : Index) {column row boundary : Nat},
    boundary ∈ coordinates phase depth →
    row ∈ coordinates phase depth →
    column ∈ horizontalQueries phase depth
      (fineGrid phase depth (fun _ _ => parent))
      (coordinates phase depth) row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate column →
    columnJointCheckFound (fun _ _ => parent) (outerLevel phase depth)
      (familyWidth (outerLevel phase depth))
      (nodes (fun _ _ => parent) (outerLevel phase depth)
        (familyWidth (outerLevel phase depth)) fuel .even)
      (nodes (fun _ _ => parent) (outerLevel phase depth)
        (familyWidth (outerLevel phase depth)) fuel .odd)
      (successorWest phase depth 0) (successorEast phase depth 0)
      row column boundary = true

theorem outerLevel_eq_refinementDepth (phase : Phase) (depth : Nat) :
    outerLevel phase depth = refinementDepth phase depth := by
  simp only [outerLevel, refinementDepth]
  omega

theorem familyWidth_eq_searchSize (phase : Phase) (depth : Nat) :
    familyWidth (outerLevel phase depth) = searchSize phase depth := by
  rw [outerLevel_eq_refinementDepth]
  simp [familyWidth, searchSize]

theorem familyIndexOffset_add_successorWest
    (phase : Phase) (depth parent : Nat) :
    familyIndexOffset (outerLevel phase depth) parent +
        successorWest phase depth 0 =
      successorWest phase depth parent := by
  simp [familyIndexOffset, outerLevel, successorWest, refinementDepth]

theorem familyIndexOffset_add_successorEast
    (phase : Phase) (depth parent : Nat) :
    familyIndexOffset (outerLevel phase depth) parent +
        successorEast phase depth 0 =
      successorEast phase depth parent := by
  simp [familyIndexOffset, outerLevel, successorEast, refinementDepth]

private theorem familyQuarterOffset_eq
    (phase : Phase) (depth parent : Nat) :
    familyQuarterOffset (outerLevel phase depth) parent =
      searchSize phase depth * parent := by
  simp [familyQuarterOffset, familyWidth_eq_searchSize]

theorem isSparseCoordinate_iff_mod (coordinate : Nat) :
    IsSparseCoordinate coordinate ↔
      coordinate % 8 = 0 ∨ coordinate % 8 = 1 := by
  constructor
  · rintro ⟨coarse, rfl⟩
    have hmod := Nat.mod_lt coarse (by decide : 0 < 2)
    have hdecompose := Nat.mod_add_div coarse 2
    rcases (show coarse % 2 = 0 ∨ coarse % 2 = 1 by omega) with h | h
    · have hcoarse : coarse = 2 * (coarse / 2) := by omega
      rw [hcoarse, sparseCoordinate_two_mul]
      simp
    · have hcoarse : coarse = 2 * (coarse / 2) + 1 := by omega
      rw [hcoarse, sparseCoordinate_two_mul_add_one]
      simp
  · intro residue
    have hmod := Nat.mod_lt coordinate (by decide : 0 < 8)
    have hdecompose := Nat.mod_add_div coordinate 8
    rcases residue with h | h
    · refine ⟨2 * (coordinate / 8), ?_⟩
      rw [sparseCoordinate_two_mul]
      omega
    · refine ⟨2 * (coordinate / 8) + 1, ?_⟩
      rw [sparseCoordinate_two_mul_add_one]
      omega

theorem isSparseCoordinate_add_of_mod_eq_zero
    {offset coordinate : Nat} (offsetMod : offset % 8 = 0) :
    IsSparseCoordinate (offset + coordinate) ↔
      IsSparseCoordinate coordinate := by
  rw [isSparseCoordinate_iff_mod, isSparseCoordinate_iff_mod]
  simp only [Nat.add_mod, offsetMod, Nat.zero_add, Nat.mod_mod]

theorem searchSize_mod_eight (phase : Phase) (depth : Nat) :
    searchSize phase depth % 8 = 0 := by
  simp [searchSize, pow_add]

theorem isSparseCoordinate_add_searchOffset_iff
    (phase : Phase) (depth parent coordinate : Nat) :
    IsSparseCoordinate
        (searchSize phase depth * parent + coordinate) ↔
      IsSparseCoordinate coordinate := by
  apply isSparseCoordinate_add_of_mod_eq_zero
  simp [Nat.mul_mod, searchSize_mod_eight]

set_option maxHeartbeats 1000000 in
-- The dependent local-coordinate normalization is expensive to elaborate.
/-- Constant-parent finite certificates supply the global endpoint-selection
obligations at the preceding recurrence depth. -/
theorem BoundedFamilyTargetsAt.toFamilyTargetsAt
    {phase : Phase} {depth fuel : Nat}
    (targets : BoundedFamilyTargetsAt phase (depth + 1) fuel) :
    FamilyTargetsAt phase depth := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      notFits sparseBoundary createdRow wrongFacing
    let localColumn := localCoordinate phase (depth + 1) parentX column
    let localRow := localCoordinate phase (depth + 1) parentY row
    let localBoundary := localCoordinate phase (depth + 1) parentY boundary
    have hlocalColumn := localCoordinate_mem_coordinates
      columnWest columnEast
    have hlocalRow := localCoordinate_mem_coordinates rowSouth rowNorth
    have hlocalBoundary := localCoordinate_mem_coordinates
      boundarySouth boundaryNorth
    have hcolumnEq :
        searchSize phase (depth + 1) * parentX + localColumn = column :=
      offset_add_localCoordinate columnWest
    have hrowEq :
        searchSize phase (depth + 1) * parentY + localRow = row :=
      offset_add_localCoordinate rowSouth
    have hboundaryEq :
        searchSize phase (depth + 1) * parentY + localBoundary = boundary :=
      offset_add_localCoordinate boundarySouth
    have hinteriorEq :
        Signals.horizontalInterior?
            (componentAt
              (fineGrid phase (depth + 1) (fun _ _ => grid parentX parentY))
              localColumn localBoundary)
            (quadrantAt localColumn localBoundary) =
          Signals.horizontalInterior?
            (componentAt
              (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
              column boundary)
            (quadrantAt column boundary) := by
      have h := horizontalInterior_parentBlock phase (depth + 1) grid
        parentX parentY localColumn localBoundary
        (coordinate_lt_searchSize hlocalColumn)
        (coordinate_lt_searchSize hlocalBoundary)
      dsimp only [localColumn, localBoundary] at h
      rw [hcolumnEq, hboundaryEq] at h
      exact h
    have hlocalWrongFacing :
        (localRow < localBoundary ∧
          Signals.horizontalInterior?
            (componentAt
              (fineGrid phase (depth + 1) (fun _ _ => grid parentX parentY))
              localColumn localBoundary)
            (quadrantAt localColumn localBoundary) = some .south) ∨
        (localBoundary < localRow ∧
          Signals.horizontalInterior?
            (componentAt
              (fineGrid phase (depth + 1) (fun _ _ => grid parentX parentY))
              localColumn localBoundary)
            (quadrantAt localColumn localBoundary) = some .north) := by
      rcases wrongFacing with wrongFacing | wrongFacing
      · left
        exact ⟨by omega, hinteriorEq.trans wrongFacing.2⟩
      · right
        exact ⟨by omega, hinteriorEq.trans wrongFacing.2⟩
    have hlocalNotFits :
        ¬FitsContainedVerticalChild phase (depth + 1) 0 0
          localColumn localRow localBoundary := by
      intro fits
      apply notFits
      rw [← hcolumnEq, ← hrowEq, ← hboundaryEq]
      exact (fitsContainedVerticalChild_add_offsets_iff phase (depth + 1)
        parentX parentY localColumn localRow localBoundary).2 fits
    have hlocalCheck : containedVerticalSeamCheck phase (depth + 1) 0 0
        localColumn localRow localBoundary = true :=
      (containedVerticalSeamCheck_eq_true_iff phase (depth + 1) 0 0
        localColumn localRow localBoundary).2 hlocalNotFits
    have hquery : localRow ∈ verticalQueries phase (depth + 1)
        (fineGrid phase (depth + 1) (fun _ _ => grid parentX parentY))
        (coordinates phase (depth + 1)) localColumn localBoundary := by
      simp only [verticalQueries, List.mem_filter, Bool.and_eq_true,
        Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨hlocalRow, hlocalWrongFacing, hlocalCheck⟩
    have hlocalSparseBoundary : IsSparseCoordinate localBoundary := by
      apply (isSparseCoordinate_add_searchOffset_iff phase (depth + 1)
        parentY localBoundary).1
      rwa [hboundaryEq]
    have hlocalCreatedRow : ¬IsSparseCoordinate localRow := by
      intro sparse
      apply createdRow
      rw [← hrowEq]
      exact (isSparseCoordinate_add_searchOffset_iff phase (depth + 1)
        parentY localRow).2 sparse
    have checked := targets.row (grid parentX parentY)
      hlocalColumn hlocalBoundary hquery
      hlocalSparseBoundary hlocalCreatedRow
    have translated := rowJointCheckFound_familyWidth_translate checked
    dsimp only [localColumn, localRow, localBoundary] at translated
    dsimp only [localColumn] at hcolumnEq
    dsimp only [localRow] at hrowEq
    dsimp only [localBoundary] at hboundaryEq
    simpa only [familyQuarterOffset_eq,
      familyIndexOffset_add_successorWest,
      familyIndexOffset_add_successorEast,
      hcolumnEq, hrowEq, hboundaryEq] using translated
  · intro grid parentX parentY column row boundary
      columnWest columnEast boundaryWest boundaryEast rowSouth rowNorth
      notFits sparseBoundary createdColumn wrongFacing
    let localColumn := localCoordinate phase (depth + 1) parentX column
    let localRow := localCoordinate phase (depth + 1) parentY row
    let localBoundary := localCoordinate phase (depth + 1) parentX boundary
    have hlocalColumn := localCoordinate_mem_coordinates
      columnWest columnEast
    have hlocalRow := localCoordinate_mem_coordinates rowSouth rowNorth
    have hlocalBoundary := localCoordinate_mem_coordinates
      boundaryWest boundaryEast
    have hcolumnEq :
        searchSize phase (depth + 1) * parentX + localColumn = column :=
      offset_add_localCoordinate columnWest
    have hrowEq :
        searchSize phase (depth + 1) * parentY + localRow = row :=
      offset_add_localCoordinate rowSouth
    have hboundaryEq :
        searchSize phase (depth + 1) * parentX + localBoundary = boundary :=
      offset_add_localCoordinate boundaryWest
    have hinteriorEq :
        Signals.verticalInterior?
            (componentAt
              (fineGrid phase (depth + 1) (fun _ _ => grid parentX parentY))
              localBoundary localRow)
            (quadrantAt localBoundary localRow) =
          Signals.verticalInterior?
            (componentAt
              (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
              boundary row)
            (quadrantAt boundary row) := by
      have h := verticalInterior_parentBlock phase (depth + 1) grid
        parentX parentY localBoundary localRow
        (coordinate_lt_searchSize hlocalBoundary)
        (coordinate_lt_searchSize hlocalRow)
      dsimp only [localBoundary, localRow] at h
      rw [hboundaryEq, hrowEq] at h
      exact h
    have hlocalWrongFacing :
        (localColumn < localBoundary ∧
          Signals.verticalInterior?
            (componentAt
              (fineGrid phase (depth + 1) (fun _ _ => grid parentX parentY))
              localBoundary localRow)
            (quadrantAt localBoundary localRow) = some .west) ∨
        (localBoundary < localColumn ∧
          Signals.verticalInterior?
            (componentAt
              (fineGrid phase (depth + 1) (fun _ _ => grid parentX parentY))
              localBoundary localRow)
            (quadrantAt localBoundary localRow) = some .east) := by
      rcases wrongFacing with wrongFacing | wrongFacing
      · left
        exact ⟨by omega, hinteriorEq.trans wrongFacing.2⟩
      · right
        exact ⟨by omega, hinteriorEq.trans wrongFacing.2⟩
    have hlocalNotFits :
        ¬FitsContainedHorizontalChild phase (depth + 1) 0 0
          localColumn localRow localBoundary := by
      intro fits
      apply notFits
      rw [← hcolumnEq, ← hrowEq, ← hboundaryEq]
      exact (fitsContainedHorizontalChild_add_offsets_iff phase (depth + 1)
        parentX parentY localColumn localRow localBoundary).2 fits
    have hlocalCheck : containedHorizontalSeamCheck phase (depth + 1) 0 0
        localColumn localRow localBoundary = true :=
      (containedHorizontalSeamCheck_eq_true_iff phase (depth + 1) 0 0
        localColumn localRow localBoundary).2 hlocalNotFits
    have hquery : localColumn ∈ horizontalQueries phase (depth + 1)
        (fineGrid phase (depth + 1) (fun _ _ => grid parentX parentY))
        (coordinates phase (depth + 1)) localRow localBoundary := by
      simp only [horizontalQueries, List.mem_filter, Bool.and_eq_true,
        Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨hlocalColumn, hlocalWrongFacing, hlocalCheck⟩
    have hlocalSparseBoundary : IsSparseCoordinate localBoundary := by
      apply (isSparseCoordinate_add_searchOffset_iff phase (depth + 1)
        parentX localBoundary).1
      rwa [hboundaryEq]
    have hlocalCreatedColumn : ¬IsSparseCoordinate localColumn := by
      intro sparse
      apply createdColumn
      rw [← hcolumnEq]
      exact (isSparseCoordinate_add_searchOffset_iff phase (depth + 1)
        parentX localColumn).2 sparse
    have checked := targets.column (grid parentX parentY)
      hlocalBoundary hlocalRow hquery
      hlocalSparseBoundary hlocalCreatedColumn
    have translated := columnJointCheckFound_familyWidth_translate checked
    dsimp only [localColumn, localRow, localBoundary] at translated
    dsimp only [localColumn] at hcolumnEq
    dsimp only [localRow] at hrowEq
    dsimp only [localBoundary] at hboundaryEq
    simpa only [familyQuarterOffset_eq,
      familyIndexOffset_add_successorWest,
      familyIndexOffset_add_successorEast,
      hrowEq, hcolumnEq, hboundaryEq] using translated

end PairCoverSeamResidualDirectPathFamilyBase
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
