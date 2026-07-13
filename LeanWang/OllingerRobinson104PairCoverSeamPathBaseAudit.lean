/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamChecks
import LeanWang.OllingerRobinson104PairCoverSeamPathSearch
import LeanWang.OllingerRobinson104BorderGeometry
import LeanWang.OllingerRobinson104ShadedFreeLineCoordinates

/-!
# Finite base audit for wrong-facing seam paths

For each corrected parent tile, a wrong-facing nonrecursive seam boundary has
an even red-graph path either to a perpendicular interior on the queried free
line or to a parallel interior strictly between the query and the boundary.
The flood is shared across all queries with the same source boundary.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathBaseAudit

open RedCycles RedShadeCycles RedShadeGraph
  ShadedFreeLineRecurrence
  PairCoverSeamArithmetic
  PairCoverSeamPathSearch PairCoverSeamShadePaths
  Signals.FreeCellLocal BorderGeometry

set_option maxRecDepth 20000

def fineGrid (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) : Nat → Nat → Index :=
  iterateRefine 2 (iterateRefine (refinementDepth phase depth) grid)

def coordinates (phase : Phase) (depth : Nat) : List Nat :=
  (List.range (quarterNorth (successorEast phase depth 0))).filter fun value =>
    quarterSouth (successorWest phase depth 0) < value

def searchSize (phase : Phase) (depth : Nat) : Nat :=
  2 ^ (refinementDepth phase depth + 3)

def searchFuel (phase : Phase) (depth : Nat) : Nat :=
  searchSize phase depth * 16 + 1

def fallbackFuel (phase : Phase) (depth : Nat) : Nat :=
  searchSize phase depth * 64 + 1

def verticalQueriesCheck (grid : Nat → Nat → Index)
    (size fuel fallbackFuel west east column boundary : Nat)
    (queries : List Nat) : Bool :=
  match queries with
  | [] => true
  | _ =>
      let found := verticalReachCover grid size size fuel
        west east column boundary queries
      let missing := queries.filter fun row =>
        !verticalReachSeamCheck grid west east column row boundary found
      let fallback := match missing with
        | [] => []
        | _ => verticalReachCover grid size size fallbackFuel
            west east column boundary missing
      queries.all fun row =>
        verticalReachSeamCheck grid west east column row boundary found ||
          verticalReachSeamCheck grid west east column row boundary fallback

def horizontalQueriesCheck (grid : Nat → Nat → Index)
    (size fuel fallbackFuel south north row boundary : Nat)
    (queries : List Nat) : Bool :=
  match queries with
  | [] => true
  | _ =>
      let found := horizontalReachCover grid size size fuel
        south north row boundary queries
      let missing := queries.filter fun column =>
        !horizontalReachSeamCheck grid south north row column boundary found
      let fallback := match missing with
        | [] => []
        | _ => horizontalReachCover grid size size fallbackFuel
            south north row boundary missing
      queries.all fun column =>
        horizontalReachSeamCheck grid south north row column boundary found ||
          horizontalReachSeamCheck grid south north row column boundary fallback

theorem verticalQueriesCheck_sound
    {grid : Nat → Nat → Index}
    {size fuel fallbackFuel west east column boundary row : Nat}
    {queries : List Nat} (hrow : row ∈ queries)
    (checked : verticalQueriesCheck grid size fuel fallbackFuel
      west east column boundary queries = true) :
    VerticalSeamPath grid west east column row boundary := by
  cases hqueries : queries with
  | nil => simp [hqueries] at hrow
  | cons first rest =>
      subst queries
      simp only [verticalQueriesCheck] at checked
      simp only [List.all_eq_true] at checked
      have rowChecked := checked row hrow
      simp only [Bool.or_eq_true] at rowChecked
      rcases rowChecked with hfound | hfallback
      · exact verticalReachCover_check_sound hfound
      · let missing := (first :: rest).filter fun query =>
          !verticalReachSeamCheck grid west east column query boundary
            (verticalReachCover grid size size fuel
              west east column boundary (first :: rest))
        change verticalReachSeamCheck grid west east column row boundary
          (match missing with
            | [] => []
            | _ => verticalReachCover grid size size fallbackFuel
                west east column boundary missing) = true at hfallback
        cases hmissing : missing with
        | nil => simp [hmissing, verticalReachSeamCheck] at hfallback
        | cons query queries =>
            apply verticalReachCover_check_sound
            simpa [hmissing] using hfallback

theorem horizontalQueriesCheck_sound
    {grid : Nat → Nat → Index}
    {size fuel fallbackFuel south north row boundary column : Nat}
    {queries : List Nat} (hcolumn : column ∈ queries)
    (checked : horizontalQueriesCheck grid size fuel fallbackFuel
      south north row boundary queries = true) :
    HorizontalSeamPath grid south north row column boundary := by
  cases hqueries : queries with
  | nil => simp [hqueries] at hcolumn
  | cons first rest =>
      subst queries
      simp only [horizontalQueriesCheck] at checked
      simp only [List.all_eq_true] at checked
      have columnChecked := checked column hcolumn
      simp only [Bool.or_eq_true] at columnChecked
      rcases columnChecked with hfound | hfallback
      · exact horizontalReachCover_check_sound hfound
      · let missing := (first :: rest).filter fun query =>
          !horizontalReachSeamCheck grid south north row query boundary
            (horizontalReachCover grid size size fuel
              south north row boundary (first :: rest))
        change horizontalReachSeamCheck grid south north row column boundary
          (match missing with
            | [] => []
            | _ => horizontalReachCover grid size size fallbackFuel
                south north row boundary missing) = true at hfallback
        cases hmissing : missing with
        | nil => simp [hmissing, horizontalReachSeamCheck] at hfallback
        | cons query queries =>
            apply horizontalReachCover_check_sound
            simpa [hmissing] using hfallback

def verticalQueries (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (coords : List Nat)
    (column boundary : Nat) : List Nat :=
  let interior := Signals.horizontalInterior?
    (componentAt grid column boundary) (quadrantAt column boundary)
  coords.filter fun row =>
    (((decide (row < boundary) && decide (interior = some .south)) ||
      (decide (boundary < row) && decide (interior = some .north))) &&
      containedVerticalSeamCheck phase depth 0 0 column row boundary)

def horizontalQueries (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (coords : List Nat)
    (row boundary : Nat) : List Nat :=
  let interior := Signals.verticalInterior?
    (componentAt grid boundary row) (quadrantAt boundary row)
  coords.filter fun column =>
    (((decide (column < boundary) && decide (interior = some .west)) ||
      (decide (boundary < column) && decide (interior = some .east))) &&
      containedHorizontalSeamCheck phase depth 0 0 column row boundary)

def checkParent (phase : Phase) (depth : Nat) (parent : Index) : Bool :=
  let grid := fineGrid phase depth (fun _ _ => parent)
  let coords := coordinates phase depth
  let size := searchSize phase depth
  let fuel := searchFuel phase depth
  let west := successorWest phase depth 0
  let east := successorEast phase depth 0
  let vertical := coords.all fun column => coords.all fun boundary =>
    let queries := verticalQueries phase depth grid coords column boundary
    verticalQueriesCheck grid size fuel (fallbackFuel phase depth)
      west east column boundary queries
  let horizontal := coords.all fun boundary => coords.all fun row =>
    let queries := horizontalQueries phase depth grid coords row boundary
    horizontalQueriesCheck grid size fuel (fallbackFuel phase depth)
      west east row boundary queries
  vertical && horizontal

structure ParentPaths (phase : Phase) (depth : Nat) (parent : Index) : Prop where
  vertical :
    let grid := fineGrid phase depth (fun _ _ => parent)
    let coords := coordinates phase depth
    ∀ {column boundary row : Nat}, column ∈ coords → boundary ∈ coords →
      row ∈ verticalQueries phase depth grid coords column boundary →
      VerticalSeamPath grid (successorWest phase depth 0)
        (successorEast phase depth 0) column row boundary
  horizontal :
    let grid := fineGrid phase depth (fun _ _ => parent)
    let coords := coordinates phase depth
    ∀ {boundary row column : Nat}, boundary ∈ coords → row ∈ coords →
      column ∈ horizontalQueries phase depth grid coords row boundary →
      HorizontalSeamPath grid (successorWest phase depth 0)
        (successorEast phase depth 0) row column boundary

def Paths (phase : Phase) (depth : Nat) : Prop :=
  ∀ parent : Index, ParentPaths phase depth parent

theorem horizontalPort_congr_of_sameComponents
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (x y : Nat) :
    horizontalPort first x y = horizontalPort second x y := by
  simp only [horizontalPort, same x y]

theorem verticalPort_congr_of_sameComponents
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (x y : Nat) :
    verticalPort first x y = verticalPort second x y := by
  simp only [verticalPort, same x y]

theorem verticalSeamPath_congr_of_sameComponents
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    {west east column row boundary : Nat}
    (path : VerticalSeamPath first west east column row boundary) :
    VerticalSeamPath second west east column row boundary := by
  rcases path with path | path
  · left
    rcases path with ⟨targetX, hwest, heast, hinterior, path⟩
    refine ⟨targetX, hwest, heast, ?_, ?_⟩
    · simpa [same targetX row] using hinterior
    · have transported := path_congr_of_sameComponents same path
      simpa only [horizontalPort_congr_of_sameComponents same,
        verticalPort_congr_of_sameComponents same] using transported
  · right
    rcases path with ⟨targetY, hbetween, hinterior, path⟩
    refine ⟨targetY, hbetween, ?_, ?_⟩
    · simpa [same column targetY] using hinterior
    · have transported := path_congr_of_sameComponents same path
      simpa only [horizontalPort_congr_of_sameComponents same] using transported

theorem horizontalSeamPath_congr_of_sameComponents
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    {south north row column boundary : Nat}
    (path : HorizontalSeamPath first south north row column boundary) :
    HorizontalSeamPath second south north row column boundary := by
  rcases path with path | path
  · left
    rcases path with ⟨targetY, hsouth, hnorth, hinterior, path⟩
    refine ⟨targetY, hsouth, hnorth, ?_, ?_⟩
    · simpa [same column targetY] using hinterior
    · have transported := path_congr_of_sameComponents same path
      simpa only [verticalPort_congr_of_sameComponents same,
        horizontalPort_congr_of_sameComponents same] using transported
  · right
    rcases path with ⟨targetX, hbetween, hinterior, path⟩
    refine ⟨targetX, hbetween, ?_, ?_⟩
    · simpa [same targetX row] using hinterior
    · have transported := path_congr_of_sameComponents same path
      simpa only [verticalPort_congr_of_sameComponents same] using transported

theorem sameComponents_fineGrid_canonicalIndex
    (phase : Phase) (depth : Nat) (parent : Index) :
    SameComponents
      (fineGrid phase depth
        (fun _ _ => BorderSubstitution.canonicalIndex parent))
      (fineGrid phase depth (fun _ _ => parent)) := by
  change SameComponents
    (iterateRefine 2 (iterateRefine (refinementDepth phase depth)
      (fun _ _ => BorderSubstitution.canonicalIndex parent)))
    (iterateRefine 2 (iterateRefine (refinementDepth phase depth)
      (fun _ _ => parent)))
  rw [PlaneRedBoards.iterateRefine_add,
    PlaneRedBoards.iterateRefine_add]
  have same := sameComponents_iterateRefine_canonicalizeGrid
    (2 + refinementDepth phase depth) (fun _ _ => parent)
  have gridEquality : (fun _ _ => BorderSubstitution.canonicalIndex parent) =
      BorderSubstitution.canonicalizeGrid (fun _ _ => parent) := by
    funext x y
    rfl
  rw [gridEquality]
  exact same

theorem ParentPaths.of_canonicalIndex
    {phase : Phase} {depth : Nat} {parent : Index}
    (canonical : ParentPaths phase depth
      (BorderSubstitution.canonicalIndex parent)) :
    ParentPaths phase depth parent := by
  let canonicalGrid := fineGrid phase depth
    (fun _ _ => BorderSubstitution.canonicalIndex parent)
  let grid := fineGrid phase depth (fun _ _ => parent)
  have same : SameComponents canonicalGrid grid := by
    simpa [canonicalGrid, grid] using
      (sameComponents_fineGrid_canonicalIndex phase depth parent)
  constructor
  · dsimp only
    intro column boundary row hcolumn hboundary hrow
    have canonicalRow : row ∈ verticalQueries phase depth canonicalGrid
        (coordinates phase depth) column boundary := by
      simp only [verticalQueries, List.mem_filter] at hrow ⊢
      refine ⟨hrow.1, ?_⟩
      simpa [same column boundary] using hrow.2
    have path := canonical.vertical hcolumn hboundary canonicalRow
    exact verticalSeamPath_congr_of_sameComponents same path
  · dsimp only
    intro boundary row column hboundary hrow hcolumn
    have canonicalColumn : column ∈ horizontalQueries phase depth canonicalGrid
        (coordinates phase depth) row boundary := by
      simp only [horizontalQueries, List.mem_filter] at hcolumn ⊢
      refine ⟨hcolumn.1, ?_⟩
      simpa [same boundary row] using hcolumn.2
    have path := canonical.horizontal hboundary hrow canonicalColumn
    exact horizontalSeamPath_congr_of_sameComponents same path

def canonicalParents : List Index :=
  BorderSubstitution.states.map BorderSubstitution.representative

abbrev Chunk := Fin 14

def parentChunk (chunk : Chunk) : List Index :=
  (canonicalParents.drop (4 * chunk.val)).take 4

def checkChunk (phase : Phase) (depth : Nat) (chunk : Chunk) : Bool :=
  (parentChunk chunk).all fun parent => checkParent phase depth parent

set_option linter.style.nativeDecide false in
theorem canonicalParents_eq_chunks :
    canonicalParents = (List.finRange 14).flatMap parentChunk := by
  native_decide

def CanonicalPaths (phase : Phase) (depth : Nat) : Prop :=
  ∀ parent ∈ canonicalParents, ParentPaths phase depth parent

def ChunkChecks (phase : Phase) (depth : Nat) : Prop :=
  ∀ chunk : Chunk, checkChunk phase depth chunk = true

theorem CanonicalPaths.paths {phase : Phase} {depth : Nat}
    (canonical : CanonicalPaths phase depth) : Paths phase depth := by
  intro parent
  apply ParentPaths.of_canonicalIndex
  apply canonical
  exact List.mem_map.2
    ⟨BorderSubstitution.indexState parent,
      BorderSubstitution.indexState_mem_states parent, rfl⟩

theorem checkParent_sound {phase : Phase} {depth : Nat} {parent : Index}
    (checked : checkParent phase depth parent = true) :
    ParentPaths phase depth parent := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true] at checked
  constructor
  · dsimp only
    intro column boundary row hcolumn hboundary hrow
    exact verticalQueriesCheck_sound hrow
      (checked.1 column hcolumn boundary hboundary)
  · dsimp only
    intro boundary row column hboundary hrow hcolumn
    exact horizontalQueriesCheck_sound hcolumn
      (checked.2 boundary hboundary row hrow)

theorem ChunkChecks.paths {phase : Phase} {depth : Nat}
    (checked : ChunkChecks phase depth) : Paths phase depth := by
  apply CanonicalPaths.paths
  intro parent hparent
  rw [canonicalParents_eq_chunks] at hparent
  simp only [List.mem_flatMap] at hparent
  rcases hparent with ⟨chunk, _, hparent⟩
  apply checkParent_sound
  have chunkChecked := checked chunk
  simp only [checkChunk, List.all_eq_true] at chunkChecked
  exact chunkChecked parent hparent

def check (phase : Phase) (depth : Nat) : Bool :=
  (List.finRange 104).all fun parent => checkParent phase depth parent

def checkCanonical (phase : Phase) (depth : Nat) : Bool :=
  canonicalParents.all fun parent => checkParent phase depth parent

theorem checkCanonical_sound {phase : Phase} {depth : Nat}
    (checked : checkCanonical phase depth = true) : Paths phase depth := by
  apply CanonicalPaths.paths
  intro parent hparent
  apply checkParent_sound
  simp only [checkCanonical, List.all_eq_true] at checked
  exact checked parent hparent

theorem check_sound {phase : Phase} {depth : Nat}
    (checked : check phase depth = true) : Paths phase depth := by
  intro parent
  apply checkParent_sound
  simp only [check, List.all_eq_true] at checked
  exact checked parent (by simp)

end PairCoverSeamPathBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
