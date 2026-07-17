/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyBase
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyTargetIndexedSearch

/-!
# Exhaustive finite family-target checks

This module packages the indexed family floods into the exact local certificate
consumed by `BoundedFamilyTargetsAt.toFamilyTargetsAt`.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyBaseCheck

open RedShadeGraph
  PairCoverSeamArithmetic PairCoverSeamPathBaseAudit
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathFamilyBase
  PairCoverSeamResidualDirectPathFamilyReachIndex
  PairCoverSeamResidualDirectPathFamilySearch
  PairCoverSeamResidualDirectPathFamilyTargetIndexedSearch
  ShadedFreeLineRecurrence

set_option maxRecDepth 20000

def sparseCheck (coordinate : Nat) : Bool :=
  decide (coordinate % 8 = 0 ∨ coordinate % 8 = 1)

theorem sparseCheck_eq_true_iff (coordinate : Nat) :
    sparseCheck coordinate = true ↔
      RefinedCoordinateProjection.IsSparseCoordinate coordinate := by
  simp [sparseCheck,
    PairCoverSeamResidualDirectPathFamilyBase.isSparseCoordinate_iff_mod]

/-- Fuel sufficient to visit every parity-labeled port state in the square. -/
def exhaustiveFuel (phase : Phase) (depth : Nat) : Nat :=
  let width := familyWidth (outerLevel phase depth)
  width * width * 8 + 1

def checkParentParts (phase : Phase) (depth fuel : Nat)
    (parent : Index) : Bool × Bool :=
  let root := fun _ _ => parent
  let outer := outerLevel phase depth
  let width := familyWidth outer
  let evenFound := nodes root outer width fuel .even
  let oddFound := nodes root outer width fuel .odd
  let evenIndex := reachIndex width evenFound
  let oddIndex := reachIndex width oddFound
  let grid := fineGrid phase depth root
  let coords := coordinates phase depth
  let west := successorWest phase depth 0
  let east := successorEast phase depth 0
  let rows := coords.all fun column => coords.all fun boundary =>
    (verticalQueries phase depth grid coords column boundary).filter
        (fun row => sparseCheck boundary && !sparseCheck row) |>.all fun row =>
      rowJointCheckIndexed root outer width evenFound oddFound
        evenIndex oddIndex west east column row boundary
  let columns := coords.all fun boundary => coords.all fun row =>
    (horizontalQueries phase depth grid coords row boundary).filter
        (fun column => sparseCheck boundary && !sparseCheck column) |>.all fun column =>
      columnJointCheckIndexed root outer width evenFound oddFound
        evenIndex oddIndex west east row column boundary
  (rows, columns)

def checkParent (phase : Phase) (depth fuel : Nat) (parent : Index) : Bool :=
  let parts := checkParentParts phase depth fuel parent
  parts.1 && parts.2

def check (phase : Phase) (depth fuel : Nat) : Bool :=
  (List.finRange 104).all fun parent => checkParent phase depth fuel parent

theorem check_sound
    {phase : Phase} {depth fuel : Nat}
    (checked : check phase depth fuel = true) :
    BoundedFamilyTargetsAt phase depth fuel := by
  have parentChecked : ∀ parent : Index,
      checkParent phase depth fuel parent = true := by
    intro parent
    simp only [check, List.all_eq_true] at checked
    exact checked parent (by simp)
  constructor
  · intro parent column row boundary columnMember boundaryMember rowMember
      sparseBoundary createdRow
    have h := parentChecked parent
    simp only [checkParent, checkParentParts, Bool.and_eq_true,
      List.all_eq_true] at h
    exact rowJointCheckIndexed_sound
      (h.1 column columnMember boundary boundaryMember row (by
        have rowCreated : sparseCheck row = false := by
          apply Bool.eq_false_of_not_eq_true
          intro sparse
          exact createdRow ((sparseCheck_eq_true_iff row).1 sparse)
        simp only [List.mem_filter, Bool.and_eq_true]
        exact ⟨rowMember,
          (sparseCheck_eq_true_iff boundary).2 sparseBoundary,
          by simp [rowCreated]⟩))
  · intro parent column row boundary boundaryMember rowMember columnMember
      sparseBoundary createdColumn
    have h := parentChecked parent
    simp only [checkParent, checkParentParts, Bool.and_eq_true,
      List.all_eq_true] at h
    exact columnJointCheckIndexed_sound
      (h.2 boundary boundaryMember row rowMember column (by
        have columnCreated : sparseCheck column = false := by
          apply Bool.eq_false_of_not_eq_true
          intro sparse
          exact createdColumn ((sparseCheck_eq_true_iff column).1 sparse)
        simp only [List.mem_filter, Bool.and_eq_true]
        exact ⟨columnMember,
          (sparseCheck_eq_true_iff boundary).2 sparseBoundary,
          by simp [columnCreated]⟩))

end PairCoverSeamResidualDirectPathFamilyBaseCheck
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
