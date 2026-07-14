/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalBase
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyBase

/-!
# Transport exceptional family targets into arbitrary parent blocks

The finite certificates use a constant grid for one parent tile.  These
adapters translate the selected source family and its target into the
corresponding hierarchy block of an arbitrary grid.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalBaseTransport

open RedCycles RedShadeCycles RedShadeGraph
  PairCoverSeamArithmetic PairCoverSeamPathBaseAudit PairCoverSeamShadePaths
  PairCoverSeamPathBoundedBase
  PairCoverSeamPathTranslation PairCoverSeamRefinementCoordinates
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyBase
  PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck
  PairCoverSeamResidualDirectPathFamilyTargetTransport
  PairCoverSeamResidualDirectPathTargets
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence SparseFreeLinePlaneBase
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Translate one certified exceptional row query into an arbitrary parent
block while preserving the selected hierarchy family. -/
theorem BoundedExceptionalTargetsAt.translateRow
    {phase : Phase} {depth fuel : Nat}
    (targets : BoundedExceptionalTargetsAt phase depth fuel)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column boundary query : Nat}
    (columnMember : column ∈ weakCoordinates phase depth)
    (boundaryMember : boundary ∈ coordinates phase depth)
    (queryMember : query ∈ rowExceptionalQueries phase depth
      (iterateRefine (outerLevel phase depth + 2)
        (fun _ _ => grid parentX parentY)) column boundary) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase depth + 2) grid)
        (horizontalPort (iterateRefine (outerLevel phase depth + 2) grid)
          (familyQuarterOffset (outerLevel phase depth) parentX + column)
          (familyQuarterOffset (outerLevel phase depth) parentY + boundary))
        (outerLevel phase depth) parentX parentY family ∧
      RowFamilyTarget grid (outerLevel phase depth) parentX parentY
        (successorWest phase depth parentX)
        (successorEast phase depth parentX)
        (familyQuarterOffset (outerLevel phase depth) parentX + column)
        (familyQuarterOffset (outerLevel phase depth) parentY + query)
        (familyQuarterOffset (outerLevel phase depth) parentY + boundary)
        family := by
  have checked := (targets (grid parentX parentY)).row
    columnMember boundaryMember queryMember
  have translated := rowJointCheckFound_familyWidth_translate checked
  simpa only [familyIndexOffset_add_successorWest,
    familyIndexOffset_add_successorEast] using translated

/-- Column-dual transport of a certified exceptional query. -/
theorem BoundedExceptionalTargetsAt.translateColumn
    {phase : Phase} {depth fuel : Nat}
    (targets : BoundedExceptionalTargetsAt phase depth fuel)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {row boundary query : Nat}
    (rowMember : row ∈ weakCoordinates phase depth)
    (boundaryMember : boundary ∈ coordinates phase depth)
    (queryMember : query ∈ columnExceptionalQueries phase depth
      (iterateRefine (outerLevel phase depth + 2)
        (fun _ _ => grid parentX parentY)) boundary row) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase depth + 2) grid)
        (verticalPort (iterateRefine (outerLevel phase depth + 2) grid)
          (familyQuarterOffset (outerLevel phase depth) parentX + boundary)
          (familyQuarterOffset (outerLevel phase depth) parentY + row))
        (outerLevel phase depth) parentX parentY family ∧
      ColumnFamilyTarget grid (outerLevel phase depth) parentX parentY
        (successorWest phase depth parentY)
        (successorEast phase depth parentY)
        (familyQuarterOffset (outerLevel phase depth) parentY + row)
        (familyQuarterOffset (outerLevel phase depth) parentX + query)
        (familyQuarterOffset (outerLevel phase depth) parentX + boundary)
        family := by
  have checked := (targets (grid parentX parentY)).column
    rowMember boundaryMember queryMember
  have translated := columnJointCheckFound_familyWidth_translate checked
  simpa only [familyIndexOffset_add_successorWest,
    familyIndexOffset_add_successorEast] using translated

private theorem localFineGrid_eq_outerGrid
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    fineGrid phase depth grid =
      iterateRefine (outerLevel phase depth + 2) grid := by
  rw [fineGrid_eq_total]
  congr 1
  simp only [outerLevel, refinementDepth]
  omega

private theorem globalFineGrid_eq_outerGrid
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid phase depth grid) =
      iterateRefine (outerLevel phase depth + 2) grid := by
  rw [globalGrid_eq_total]
  congr 1
  simp only [outerLevel, refinementDepth]
  omega

private theorem offset_add_localCoordinate_of_weakLower
    {phase : Phase} {depth block coordinate : Nat}
    (lower : quarterSouth (successorWest phase depth block) ≤ coordinate) :
    searchSize phase depth * block +
        localCoordinate phase depth block coordinate = coordinate := by
  have lowerEq := quarterOffset_add_south phase depth block
  unfold localCoordinate
  omega

private theorem localCoordinate_mem_weakCoordinates
    {phase : Phase} {depth block coordinate : Nat}
    (lower : quarterSouth (successorWest phase depth block) ≤ coordinate)
    (upper : coordinate < quarterNorth (successorEast phase depth block)) :
    localCoordinate phase depth block coordinate ∈ weakCoordinates phase depth := by
  have lowerEq := quarterOffset_add_south phase depth block
  have upperEq := quarterOffset_add_north phase depth block
  have coordinateEq := offset_add_localCoordinate_of_weakLower lower
  simp only [weakCoordinates, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  constructor <;> omega

private theorem weakCoordinate_lt_searchSize
    {phase : Phase} {depth coordinate : Nat}
    (member : coordinate ∈ weakCoordinates phase depth) :
    coordinate < searchSize phase depth := by
  simp only [weakCoordinates, List.mem_filter, List.mem_range] at member
  have power := two_pow_refinementDepth_eq_four_mul_west phase depth
  have westPositive := west_pos phase depth
  have eastEq : east phase depth = 3 * west phase depth := rfl
  have eastSucc : east phase (depth + 1) = 4 * east phase depth :=
    east_succ phase depth
  have upper : quarterNorth (successorEast phase depth 0) ≤
      searchSize phase depth := by
    simp only [successorEast, Nat.mul_zero, Nat.zero_add, searchSize,
      quarterNorth, pow_add, power, eastSucc, eastEq]
    nlinarith
  exact member.1.trans_le upper

private theorem familyQuarterOffset_eq_searchOffset
    (phase : Phase) (depth parent : Nat) :
    familyQuarterOffset (outerLevel phase depth) parent =
      searchSize phase depth * parent := by
  simp [familyQuarterOffset, familyWidth_eq_searchSize]

private theorem horizontalInterior_local_eq_global
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {column boundary localColumn localBoundary : Nat}
    (columnEq : searchSize phase depth * parentX + localColumn = column)
    (boundaryEq : searchSize phase depth * parentY + localBoundary = boundary)
    (localColumnLt : localColumn < searchSize phase depth)
    (localBoundaryLt : localBoundary < searchSize phase depth) :
    Signals.horizontalInterior?
        (componentAt
          (iterateRefine (outerLevel phase depth + 2)
            (fun _ _ => grid parentX parentY)) localColumn localBoundary)
        (quadrantAt localColumn localBoundary) =
      Signals.horizontalInterior?
        (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
          column boundary)
        (quadrantAt column boundary) := by
  have translated := horizontalInterior_parentBlock phase depth grid
    parentX parentY localColumn localBoundary localColumnLt localBoundaryLt
  rw [localFineGrid_eq_outerGrid, globalFineGrid_eq_outerGrid,
    columnEq, boundaryEq] at translated
  exact translated

/-- Translate the south-facing lower-edge stopping query into an arbitrary
parent block. -/
theorem BoundedExceptionalTargetsAt.translateRowSouthLower
    {phase : Phase} {depth fuel : Nat}
    (targets : BoundedExceptionalTargetsAt phase depth fuel)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column boundary : Nat}
    (columnLower :
      quarterSouth (successorWest phase depth parentX) ≤ column)
    (columnUpper : column <
      quarterNorth (successorEast phase depth parentX))
    (boundaryLower :
      quarterSouth (successorWest phase depth parentY) < boundary)
    (boundaryUpper : boundary <
      quarterNorth (successorEast phase depth parentY))
    (south : Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
        column boundary)
      (quadrantAt column boundary) = some .south) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase depth + 2) grid)
        (horizontalPort (iterateRefine (outerLevel phase depth + 2) grid)
          column boundary)
        (outerLevel phase depth) parentX parentY family ∧
      RowFamilyTarget grid (outerLevel phase depth) parentX parentY
        (successorWest phase depth parentX)
        (successorEast phase depth parentX)
        column (quarterSouth (successorWest phase depth parentY))
        boundary family := by
  let localColumn := localCoordinate phase depth parentX column
  let localBoundary := localCoordinate phase depth parentY boundary
  have localColumnMember := localCoordinate_mem_weakCoordinates
    columnLower columnUpper
  have localBoundaryMember := localCoordinate_mem_coordinates
    boundaryLower boundaryUpper
  have columnEq : searchSize phase depth * parentX + localColumn = column :=
    offset_add_localCoordinate_of_weakLower columnLower
  have boundaryEq :
      searchSize phase depth * parentY + localBoundary = boundary :=
    offset_add_localCoordinate boundaryLower
  have localInteriorEq := horizontalInterior_local_eq_global phase depth grid
    parentX parentY columnEq boundaryEq
    (weakCoordinate_lt_searchSize localColumnMember)
    (coordinate_lt_searchSize localBoundaryMember)
  have localSouth : Signals.horizontalInterior?
      (componentAt
        (iterateRefine (outerLevel phase depth + 2)
          (fun _ _ => grid parentX parentY)) localColumn localBoundary)
      (quadrantAt localColumn localBoundary) = some .south :=
    localInteriorEq.trans south
  have queryMember : quarterSouth (successorWest phase depth 0) ∈
      rowExceptionalQueries phase depth
        (iterateRefine (outerLevel phase depth + 2)
          (fun _ _ => grid parentX parentY)) localColumn localBoundary := by
    simp [rowExceptionalQueries, localSouth]
  have translated := translateRow targets grid parentX parentY
    localColumnMember localBoundaryMember queryMember
  dsimp only [localColumn, localBoundary] at translated columnEq boundaryEq
  simpa only [familyQuarterOffset_eq_searchOffset, columnEq, boundaryEq,
    quarterOffset_add_south] using translated

/-- Translate the north-facing source-boundary stopping query. -/
theorem BoundedExceptionalTargetsAt.translateRowNorthBoundary
    {phase : Phase} {depth fuel : Nat}
    (targets : BoundedExceptionalTargetsAt phase depth fuel)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column boundary : Nat}
    (columnLower :
      quarterSouth (successorWest phase depth parentX) ≤ column)
    (columnUpper : column <
      quarterNorth (successorEast phase depth parentX))
    (boundaryLower :
      quarterSouth (successorWest phase depth parentY) < boundary)
    (boundaryUpper : boundary <
      quarterNorth (successorEast phase depth parentY))
    (north : Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
        column boundary)
      (quadrantAt column boundary) = some .north) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase depth + 2) grid)
        (horizontalPort (iterateRefine (outerLevel phase depth + 2) grid)
          column boundary)
        (outerLevel phase depth) parentX parentY family ∧
      RowFamilyTarget grid (outerLevel phase depth) parentX parentY
        (successorWest phase depth parentX)
        (successorEast phase depth parentX)
        column boundary boundary family := by
  let localColumn := localCoordinate phase depth parentX column
  let localBoundary := localCoordinate phase depth parentY boundary
  have localColumnMember := localCoordinate_mem_weakCoordinates
    columnLower columnUpper
  have localBoundaryMember := localCoordinate_mem_coordinates
    boundaryLower boundaryUpper
  have columnEq : searchSize phase depth * parentX + localColumn = column :=
    offset_add_localCoordinate_of_weakLower columnLower
  have boundaryEq :
      searchSize phase depth * parentY + localBoundary = boundary :=
    offset_add_localCoordinate boundaryLower
  have localInteriorEq := horizontalInterior_local_eq_global phase depth grid
    parentX parentY columnEq boundaryEq
    (weakCoordinate_lt_searchSize localColumnMember)
    (coordinate_lt_searchSize localBoundaryMember)
  have localNorth : Signals.horizontalInterior?
      (componentAt
        (iterateRefine (outerLevel phase depth + 2)
          (fun _ _ => grid parentX parentY)) localColumn localBoundary)
      (quadrantAt localColumn localBoundary) = some .north :=
    localInteriorEq.trans north
  have queryMember : localBoundary ∈
      rowExceptionalQueries phase depth
        (iterateRefine (outerLevel phase depth + 2)
          (fun _ _ => grid parentX parentY)) localColumn localBoundary := by
    simp [rowExceptionalQueries, localNorth]
  have translated := translateRow targets grid parentX parentY
    localColumnMember localBoundaryMember queryMember
  dsimp only [localColumn, localBoundary] at translated columnEq boundaryEq
  simpa only [familyQuarterOffset_eq_searchOffset, columnEq, boundaryEq]
    using translated

/-- Translate an ordinary strict row query whose transverse source coordinate
is exactly the lower collar edge. -/
theorem BoundedExceptionalTargetsAt.translateRowLowerSource
    {phase : Phase} {depth fuel : Nat}
    (targets : BoundedExceptionalTargetsAt phase depth fuel)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {query boundary : Nat}
    (queryLower : quarterSouth (successorWest phase depth parentY) < query)
    (queryUpper : query < quarterNorth (successorEast phase depth parentY))
    (boundaryLower :
      quarterSouth (successorWest phase depth parentY) < boundary)
    (boundaryUpper : boundary <
      quarterNorth (successorEast phase depth parentY))
    (wrongFacing :
      (query < boundary ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            (quarterSouth (successorWest phase depth parentX)) boundary)
          (quadrantAt (quarterSouth (successorWest phase depth parentX))
            boundary) = some .south) ∨
      (boundary < query ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            (quarterSouth (successorWest phase depth parentX)) boundary)
          (quadrantAt (quarterSouth (successorWest phase depth parentX))
            boundary) = some .north))
    (notFits : ¬FitsContainedVerticalChild phase depth parentX parentY
      (quarterSouth (successorWest phase depth parentX)) query boundary) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase depth + 2) grid)
        (horizontalPort (iterateRefine (outerLevel phase depth + 2) grid)
          (quarterSouth (successorWest phase depth parentX)) boundary)
        (outerLevel phase depth) parentX parentY family ∧
      RowFamilyTarget grid (outerLevel phase depth) parentX parentY
        (successorWest phase depth parentX)
        (successorEast phase depth parentX)
        (quarterSouth (successorWest phase depth parentX)) query boundary
        family := by
  let localColumn := quarterSouth (successorWest phase depth 0)
  let localQuery := localCoordinate phase depth parentY query
  let localBoundary := localCoordinate phase depth parentY boundary
  have localColumnMember : localColumn ∈ weakCoordinates phase depth := by
    simp only [localColumn, weakCoordinates, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    constructor
    · have positive := west_pos phase (depth + 1)
      have eastEq : east phase (depth + 1) =
          3 * west phase (depth + 1) := rfl
      simp only [successorWest, successorEast, Nat.mul_zero, Nat.zero_add,
        quarterSouth, quarterNorth, eastEq]
      omega
    · exact le_rfl
  have localQueryMember := localCoordinate_mem_coordinates queryLower queryUpper
  have localBoundaryMember := localCoordinate_mem_coordinates
    boundaryLower boundaryUpper
  have columnEq : searchSize phase depth * parentX + localColumn =
      quarterSouth (successorWest phase depth parentX) := by
    exact quarterOffset_add_south phase depth parentX
  have queryEq : searchSize phase depth * parentY + localQuery = query :=
    offset_add_localCoordinate queryLower
  have boundaryEq :
      searchSize phase depth * parentY + localBoundary = boundary :=
    offset_add_localCoordinate boundaryLower
  have localInteriorEq := horizontalInterior_local_eq_global phase depth grid
    parentX parentY columnEq boundaryEq
    (weakCoordinate_lt_searchSize localColumnMember)
    (coordinate_lt_searchSize localBoundaryMember)
  have localWrongFacing :
      (localQuery < localBoundary ∧
        Signals.horizontalInterior?
          (componentAt
            (iterateRefine (outerLevel phase depth + 2)
              (fun _ _ => grid parentX parentY)) localColumn localBoundary)
          (quadrantAt localColumn localBoundary) = some .south) ∨
      (localBoundary < localQuery ∧
        Signals.horizontalInterior?
          (componentAt
            (iterateRefine (outerLevel phase depth + 2)
              (fun _ _ => grid parentX parentY)) localColumn localBoundary)
          (quadrantAt localColumn localBoundary) = some .north) := by
    rcases wrongFacing with south | north
    · exact Or.inl ⟨by omega, localInteriorEq.trans south.2⟩
    · exact Or.inr ⟨by omega, localInteriorEq.trans north.2⟩
  have localNotFits : ¬FitsContainedVerticalChild phase depth 0 0
      localColumn localQuery localBoundary := by
    intro fits
    apply notFits
    rw [← columnEq, ← queryEq, ← boundaryEq]
    exact (fitsContainedVerticalChild_add_offsets_iff phase depth
      parentX parentY localColumn localQuery localBoundary).2 fits
  have localCheck : containedVerticalSeamCheck phase depth 0 0
      localColumn localQuery localBoundary = true :=
    (containedVerticalSeamCheck_eq_true_iff phase depth 0 0
      localColumn localQuery localBoundary).2 localNotFits
  have ordinaryQuery : localQuery ∈ verticalQueries phase depth
      (iterateRefine (outerLevel phase depth + 2)
        (fun _ _ => grid parentX parentY))
      (coordinates phase depth) localColumn localBoundary := by
    simp only [verticalQueries, List.mem_filter, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨localQueryMember, localWrongFacing, localCheck⟩
  have queryMember : localQuery ∈ rowExceptionalQueries phase depth
      (iterateRefine (outerLevel phase depth + 2)
        (fun _ _ => grid parentX parentY)) localColumn localBoundary := by
    simp only [rowExceptionalQueries, List.mem_append]
    right
    simpa [localColumn] using ordinaryQuery
  have translated := translateRow targets grid parentX parentY
    localColumnMember localBoundaryMember queryMember
  dsimp only [localColumn, localQuery, localBoundary] at translated columnEq queryEq boundaryEq
  simpa only [familyQuarterOffset_eq_searchOffset, columnEq, queryEq,
    boundaryEq] using translated

private theorem verticalInterior_local_eq_global
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {boundary row localBoundary localRow : Nat}
    (boundaryEq : searchSize phase depth * parentX + localBoundary = boundary)
    (rowEq : searchSize phase depth * parentY + localRow = row)
    (localBoundaryLt : localBoundary < searchSize phase depth)
    (localRowLt : localRow < searchSize phase depth) :
    Signals.verticalInterior?
        (componentAt
          (iterateRefine (outerLevel phase depth + 2)
            (fun _ _ => grid parentX parentY)) localBoundary localRow)
        (quadrantAt localBoundary localRow) =
      Signals.verticalInterior?
        (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
          boundary row)
        (quadrantAt boundary row) := by
  have translated := verticalInterior_parentBlock phase depth grid
    parentX parentY localBoundary localRow localBoundaryLt localRowLt
  rw [localFineGrid_eq_outerGrid, globalFineGrid_eq_outerGrid,
    boundaryEq, rowEq] at translated
  exact translated

/-- Column-dual west-facing lower-edge stopping query. -/
theorem BoundedExceptionalTargetsAt.translateColumnWestLower
    {phase : Phase} {depth fuel : Nat}
    (targets : BoundedExceptionalTargetsAt phase depth fuel)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {boundary row : Nat}
    (boundaryLower :
      quarterWest (successorWest phase depth parentX) < boundary)
    (boundaryUpper : boundary <
      quarterEast (successorEast phase depth parentX))
    (rowLower : quarterSouth (successorWest phase depth parentY) ≤ row)
    (rowUpper : row < quarterNorth (successorEast phase depth parentY))
    (westFacing : Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
        boundary row)
      (quadrantAt boundary row) = some .west) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase depth + 2) grid)
        (verticalPort (iterateRefine (outerLevel phase depth + 2) grid)
          boundary row)
        (outerLevel phase depth) parentX parentY family ∧
      ColumnFamilyTarget grid (outerLevel phase depth) parentX parentY
        (successorWest phase depth parentY)
        (successorEast phase depth parentY)
        row (quarterWest (successorWest phase depth parentX)) boundary
        family := by
  let localBoundary := localCoordinate phase depth parentX boundary
  let localRow := localCoordinate phase depth parentY row
  have localBoundaryMember := localCoordinate_mem_coordinates
    boundaryLower boundaryUpper
  have localRowMember := localCoordinate_mem_weakCoordinates
    (by simpa only [quarterSouth, quarterWest] using rowLower)
    (by simpa only [quarterNorth, quarterEast] using rowUpper)
  have boundaryEq :
      searchSize phase depth * parentX + localBoundary = boundary :=
    offset_add_localCoordinate
      (by simpa only [quarterSouth, quarterWest] using boundaryLower)
  have rowEq : searchSize phase depth * parentY + localRow = row :=
    offset_add_localCoordinate_of_weakLower rowLower
  have localInteriorEq := verticalInterior_local_eq_global phase depth grid
    parentX parentY boundaryEq rowEq
    (coordinate_lt_searchSize localBoundaryMember)
    (weakCoordinate_lt_searchSize localRowMember)
  have localWest : Signals.verticalInterior?
      (componentAt
        (iterateRefine (outerLevel phase depth + 2)
          (fun _ _ => grid parentX parentY)) localBoundary localRow)
      (quadrantAt localBoundary localRow) = some .west :=
    localInteriorEq.trans westFacing
  have queryMember : quarterWest (successorWest phase depth 0) ∈
      columnExceptionalQueries phase depth
        (iterateRefine (outerLevel phase depth + 2)
          (fun _ _ => grid parentX parentY)) localBoundary localRow := by
    simp [columnExceptionalQueries, localWest]
  have translated := translateColumn targets grid parentX parentY
    localRowMember localBoundaryMember queryMember
  dsimp only [localBoundary, localRow] at translated boundaryEq rowEq
  simpa only [familyQuarterOffset_eq_searchOffset, boundaryEq, rowEq,
    quarterOffset_add_west] using translated

/-- Column-dual east-facing source-boundary stopping query. -/
theorem BoundedExceptionalTargetsAt.translateColumnEastBoundary
    {phase : Phase} {depth fuel : Nat}
    (targets : BoundedExceptionalTargetsAt phase depth fuel)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {boundary row : Nat}
    (boundaryLower :
      quarterWest (successorWest phase depth parentX) < boundary)
    (boundaryUpper : boundary <
      quarterEast (successorEast phase depth parentX))
    (rowLower : quarterSouth (successorWest phase depth parentY) ≤ row)
    (rowUpper : row < quarterNorth (successorEast phase depth parentY))
    (eastFacing : Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
        boundary row)
      (quadrantAt boundary row) = some .east) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase depth + 2) grid)
        (verticalPort (iterateRefine (outerLevel phase depth + 2) grid)
          boundary row)
        (outerLevel phase depth) parentX parentY family ∧
      ColumnFamilyTarget grid (outerLevel phase depth) parentX parentY
        (successorWest phase depth parentY)
        (successorEast phase depth parentY)
        row boundary boundary family := by
  let localBoundary := localCoordinate phase depth parentX boundary
  let localRow := localCoordinate phase depth parentY row
  have localBoundaryMember := localCoordinate_mem_coordinates
    boundaryLower boundaryUpper
  have localRowMember := localCoordinate_mem_weakCoordinates
    (by simpa only [quarterSouth, quarterWest] using rowLower)
    (by simpa only [quarterNorth, quarterEast] using rowUpper)
  have boundaryEq :
      searchSize phase depth * parentX + localBoundary = boundary :=
    offset_add_localCoordinate
      (by simpa only [quarterSouth, quarterWest] using boundaryLower)
  have rowEq : searchSize phase depth * parentY + localRow = row :=
    offset_add_localCoordinate_of_weakLower rowLower
  have localInteriorEq := verticalInterior_local_eq_global phase depth grid
    parentX parentY boundaryEq rowEq
    (coordinate_lt_searchSize localBoundaryMember)
    (weakCoordinate_lt_searchSize localRowMember)
  have localEast : Signals.verticalInterior?
      (componentAt
        (iterateRefine (outerLevel phase depth + 2)
          (fun _ _ => grid parentX parentY)) localBoundary localRow)
      (quadrantAt localBoundary localRow) = some .east :=
    localInteriorEq.trans eastFacing
  have queryMember : localBoundary ∈
      columnExceptionalQueries phase depth
        (iterateRefine (outerLevel phase depth + 2)
          (fun _ _ => grid parentX parentY)) localBoundary localRow := by
    simp [columnExceptionalQueries, localEast]
  have translated := translateColumn targets grid parentX parentY
    localRowMember localBoundaryMember queryMember
  dsimp only [localBoundary, localRow] at translated boundaryEq rowEq
  simpa only [familyQuarterOffset_eq_searchOffset, boundaryEq, rowEq]
    using translated

/-- Column-dual ordinary strict query whose transverse source row is exactly
the lower collar edge. -/
theorem BoundedExceptionalTargetsAt.translateColumnLowerSource
    {phase : Phase} {depth fuel : Nat}
    (targets : BoundedExceptionalTargetsAt phase depth fuel)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {query boundary : Nat}
    (queryLower : quarterWest (successorWest phase depth parentX) < query)
    (queryUpper : query < quarterEast (successorEast phase depth parentX))
    (boundaryLower :
      quarterWest (successorWest phase depth parentX) < boundary)
    (boundaryUpper : boundary <
      quarterEast (successorEast phase depth parentX))
    (wrongFacing :
      (query < boundary ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            boundary (quarterSouth (successorWest phase depth parentY)))
          (quadrantAt boundary
            (quarterSouth (successorWest phase depth parentY))) = some .west) ∨
      (boundary < query ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            boundary (quarterSouth (successorWest phase depth parentY)))
          (quadrantAt boundary
            (quarterSouth (successorWest phase depth parentY))) = some .east))
    (notFits : ¬FitsContainedHorizontalChild phase depth parentX parentY
      query (quarterSouth (successorWest phase depth parentY)) boundary) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase depth + 2) grid)
        (verticalPort (iterateRefine (outerLevel phase depth + 2) grid)
          boundary (quarterSouth (successorWest phase depth parentY)))
        (outerLevel phase depth) parentX parentY family ∧
      ColumnFamilyTarget grid (outerLevel phase depth) parentX parentY
        (successorWest phase depth parentY)
        (successorEast phase depth parentY)
        (quarterSouth (successorWest phase depth parentY)) query boundary
        family := by
  let localRow := quarterWest (successorWest phase depth 0)
  let localQuery := localCoordinate phase depth parentX query
  let localBoundary := localCoordinate phase depth parentX boundary
  have localRowMember : localRow ∈ weakCoordinates phase depth := by
    simp only [localRow, weakCoordinates, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    constructor
    · have positive := west_pos phase (depth + 1)
      have eastEq : east phase (depth + 1) =
          3 * west phase (depth + 1) := rfl
      simp only [successorWest, successorEast, Nat.mul_zero, Nat.zero_add,
        quarterWest, quarterNorth, eastEq]
      omega
    · exact le_rfl
  have localQueryMember := localCoordinate_mem_coordinates
    (by simpa only [quarterSouth, quarterWest] using queryLower)
    (by simpa only [quarterNorth, quarterEast] using queryUpper)
  have localBoundaryMember := localCoordinate_mem_coordinates
    (by simpa only [quarterSouth, quarterWest] using boundaryLower)
    (by simpa only [quarterNorth, quarterEast] using boundaryUpper)
  have rowEq : searchSize phase depth * parentY + localRow =
      quarterSouth (successorWest phase depth parentY) := by
    simpa only [localRow, quarterSouth, quarterWest] using
      quarterOffset_add_south phase depth parentY
  have queryEq : searchSize phase depth * parentX + localQuery = query :=
    offset_add_localCoordinate
      (by simpa only [quarterSouth, quarterWest] using queryLower)
  have boundaryEq :
      searchSize phase depth * parentX + localBoundary = boundary :=
    offset_add_localCoordinate
      (by simpa only [quarterSouth, quarterWest] using boundaryLower)
  have localInteriorEq := verticalInterior_local_eq_global phase depth grid
    parentX parentY boundaryEq rowEq
    (coordinate_lt_searchSize localBoundaryMember)
    (weakCoordinate_lt_searchSize localRowMember)
  have localWrongFacing :
      (localQuery < localBoundary ∧
        Signals.verticalInterior?
          (componentAt
            (iterateRefine (outerLevel phase depth + 2)
              (fun _ _ => grid parentX parentY)) localBoundary localRow)
          (quadrantAt localBoundary localRow) = some .west) ∨
      (localBoundary < localQuery ∧
        Signals.verticalInterior?
          (componentAt
            (iterateRefine (outerLevel phase depth + 2)
              (fun _ _ => grid parentX parentY)) localBoundary localRow)
          (quadrantAt localBoundary localRow) = some .east) := by
    rcases wrongFacing with west | east
    · exact Or.inl ⟨by omega, localInteriorEq.trans west.2⟩
    · exact Or.inr ⟨by omega, localInteriorEq.trans east.2⟩
  have localNotFits : ¬FitsContainedHorizontalChild phase depth 0 0
      localQuery localRow localBoundary := by
    intro fits
    apply notFits
    rw [← queryEq, ← rowEq, ← boundaryEq]
    exact (fitsContainedHorizontalChild_add_offsets_iff phase depth
      parentX parentY localQuery localRow localBoundary).2 fits
  have localCheck : containedHorizontalSeamCheck phase depth 0 0
      localQuery localRow localBoundary = true :=
    (containedHorizontalSeamCheck_eq_true_iff phase depth 0 0
      localQuery localRow localBoundary).2 localNotFits
  have ordinaryQuery : localQuery ∈ horizontalQueries phase depth
      (iterateRefine (outerLevel phase depth + 2)
        (fun _ _ => grid parentX parentY))
      (coordinates phase depth) localRow localBoundary := by
    simp only [horizontalQueries, List.mem_filter, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨localQueryMember, localWrongFacing, localCheck⟩
  have queryMember : localQuery ∈ columnExceptionalQueries phase depth
      (iterateRefine (outerLevel phase depth + 2)
        (fun _ _ => grid parentX parentY)) localBoundary localRow := by
    simp only [columnExceptionalQueries, List.mem_append]
    right
    simpa [localRow, quarterSouth, quarterWest] using ordinaryQuery
  have translated := translateColumn targets grid parentX parentY
    localRowMember localBoundaryMember queryMember
  dsimp only [localRow, localQuery, localBoundary] at translated rowEq queryEq boundaryEq
  simpa only [familyQuarterOffset_eq_searchOffset, rowEq, queryEq,
    boundaryEq] using translated

end PairCoverSeamResidualDirectPathFamilyExceptionalBaseTransport
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
