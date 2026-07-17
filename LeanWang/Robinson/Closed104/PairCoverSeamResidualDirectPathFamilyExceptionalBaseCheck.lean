/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyBaseCheck

/-!
# Finite exceptional target seeds for residual recursion

Repeated coarse-coordinate projection has two stopping cases that are not
ordinary strict seam queries: the projected query may equal its sparse source
boundary, or it may equal the lower collar coordinate.  This checker asks for
same-family targets at exactly those two coordinates.  Family floods are
computed once per parent, and four-parent chunks keep native certificates
independently rebuildable.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamArithmetic PairCoverSeamPathBaseAudit
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathFamilyBaseCheck
  PairCoverSeamResidualDirectPathFamilyReachIndex
  PairCoverSeamResidualDirectPathFamilySearch
  PairCoverSeamResidualDirectPathFamilyTargetIndexedSearch
  PairCoverSeamResidualDirectPathFamilyTargetSearch
  ShadedFreeLineRecurrence Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Include the lower collar coordinate omitted by the strict base queries. -/
def weakCoordinates (phase : Phase) (depth : Nat) : List Nat :=
  (List.range (quarterNorth (successorEast phase depth 0))).filter fun value =>
    quarterSouth (successorWest phase depth 0) ≤ value

def rowExceptionalQueries (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (column boundary : Nat) : List Nat :=
  let stopping :=
    match Signals.horizontalInterior?
        (componentAt grid column boundary) (quadrantAt column boundary) with
    | some .north => [boundary]
    | some .south => [quarterSouth (successorWest phase depth 0)]
    | none => []
  stopping ++
    if column = quarterSouth (successorWest phase depth 0) then
      verticalQueries phase depth grid (coordinates phase depth) column boundary
    else []

def columnExceptionalQueries (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (boundary row : Nat) : List Nat :=
  let stopping :=
    match Signals.verticalInterior?
        (componentAt grid boundary row) (quadrantAt boundary row) with
    | some .east => [boundary]
    | some .west => [quarterWest (successorWest phase depth 0)]
    | none => []
  stopping ++
    if row = quarterWest (successorWest phase depth 0) then
      horizontalQueries phase depth grid (coordinates phase depth) row boundary
    else []

/-- Proof-level interface extracted from the exceptional finite check. -/
structure BoundedExceptionalParentTargetsAt
    (phase : Phase) (depth fuel : Nat) (parent : Index) : Prop where
  row : ∀ {column boundary query : Nat},
    column ∈ weakCoordinates phase depth →
    boundary ∈ coordinates phase depth →
    query ∈ rowExceptionalQueries phase depth
      (iterateRefine (outerLevel phase depth + 2) (fun _ _ => parent))
      column boundary →
    rowJointCheckFound (fun _ _ => parent) (outerLevel phase depth)
      (familyWidth (outerLevel phase depth))
      (nodes (fun _ _ => parent) (outerLevel phase depth)
        (familyWidth (outerLevel phase depth)) fuel .even)
      (nodes (fun _ _ => parent) (outerLevel phase depth)
        (familyWidth (outerLevel phase depth)) fuel .odd)
      (successorWest phase depth 0) (successorEast phase depth 0)
      column query boundary = true
  column : ∀ {row boundary query : Nat},
    row ∈ weakCoordinates phase depth →
    boundary ∈ coordinates phase depth →
    query ∈ columnExceptionalQueries phase depth
      (iterateRefine (outerLevel phase depth + 2) (fun _ _ => parent))
      boundary row →
    columnJointCheckFound (fun _ _ => parent) (outerLevel phase depth)
      (familyWidth (outerLevel phase depth))
      (nodes (fun _ _ => parent) (outerLevel phase depth)
        (familyWidth (outerLevel phase depth)) fuel .even)
      (nodes (fun _ _ => parent) (outerLevel phase depth)
        (familyWidth (outerLevel phase depth)) fuel .odd)
      (successorWest phase depth 0) (successorEast phase depth 0)
      row query boundary = true

def BoundedExceptionalTargetsAt
    (phase : Phase) (depth fuel : Nat) : Prop :=
  ∀ parent, BoundedExceptionalParentTargetsAt phase depth fuel parent

def checkParentParts (phase : Phase) (depth fuel : Nat)
    (parent : Index) : Bool × Bool :=
  let root := fun _ _ => parent
  let outer := outerLevel phase depth
  let width := familyWidth outer
  let evenFound := nodes root outer width fuel .even
  let oddFound := nodes root outer width fuel .odd
  let evenIndex := reachIndex width evenFound
  let oddIndex := reachIndex width oddFound
  let grid := iterateRefine (outer + 2) root
  let weak := weakCoordinates phase depth
  let strict := coordinates phase depth
  let west := successorWest phase depth 0
  let east := successorEast phase depth 0
  let rows := weak.all fun column => strict.all fun boundary =>
    (rowExceptionalQueries phase depth grid column boundary).all fun query =>
      rowJointCheckIndexed root outer width evenFound oddFound
        evenIndex oddIndex west east column query boundary
  let columns := weak.all fun row => strict.all fun boundary =>
    (columnExceptionalQueries phase depth grid boundary row).all fun query =>
      columnJointCheckIndexed root outer width evenFound oddFound
        evenIndex oddIndex west east row query boundary
  (rows, columns)

def checkParent (phase : Phase) (depth fuel : Nat) (parent : Index) : Bool :=
  let parts := checkParentParts phase depth fuel parent
  parts.1 && parts.2

theorem checkParent_sound
    {phase : Phase} {depth fuel : Nat} {parent : Index}
    (checked : checkParent phase depth fuel parent = true) :
    BoundedExceptionalParentTargetsAt phase depth fuel parent := by
  constructor
  · intro column boundary query columnMember boundaryMember
      queryMember
    simp only [checkParent, checkParentParts, Bool.and_eq_true,
      List.all_eq_true] at checked
    have queryChecked := checked.1 column columnMember boundary boundaryMember
    exact rowJointCheckIndexed_sound (queryChecked query queryMember)
  · intro row boundary query rowMember boundaryMember
      queryMember
    simp only [checkParent, checkParentParts, Bool.and_eq_true,
      List.all_eq_true] at checked
    have queryChecked := checked.2 row rowMember boundary boundaryMember
    exact columnJointCheckIndexed_sound (queryChecked query queryMember)

abbrev Chunk := Fin 26

def parentChunk (chunk : Chunk) : List Index :=
  (List.finRange 104).drop (4 * chunk.val) |>.take 4

def checkChunk (phase : Phase) (depth fuel : Nat) (chunk : Chunk) : Bool :=
  (parentChunk chunk).all fun parent => checkParent phase depth fuel parent

set_option linter.style.nativeDecide false in
theorem parents_eq_chunks :
    List.finRange 104 = (List.finRange 26).flatMap parentChunk := by
  native_decide

def ChunkChecks (phase : Phase) (depth fuel : Nat) : Prop :=
  ∀ chunk : Chunk, checkChunk phase depth fuel chunk = true

theorem ChunkChecks.targets
    {phase : Phase} {depth fuel : Nat}
    (checked : ChunkChecks phase depth fuel) :
    BoundedExceptionalTargetsAt phase depth fuel := by
  intro parent
  have parentMember : parent ∈ List.finRange 104 := by simp
  rw [parents_eq_chunks] at parentMember
  simp only [List.mem_flatMap] at parentMember
  rcases parentMember with ⟨chunk, _chunkMember, parentInChunk⟩
  have chunkChecked := checked chunk
  simp only [checkChunk, List.all_eq_true] at chunkChecked
  exact checkParent_sound (chunkChecked parent parentInChunk)

end PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
