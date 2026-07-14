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

open RedCycles RedShadeGraph
  PairCoverSeamArithmetic PairCoverSeamPathBaseAudit PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyBase
  PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck
  PairCoverSeamResidualDirectPathFamilyTargetTransport
  PairCoverSeamResidualDirectPathTargets
  ShadedFreeLineRecurrence Signals.FreeCellLocal

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

end PairCoverSeamResidualDirectPathFamilyExceptionalBaseTransport
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
