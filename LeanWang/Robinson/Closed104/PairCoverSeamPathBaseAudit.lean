/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPathQuerySearch

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

def searchFuel (phase : Phase) (depth : Nat) : Nat :=
  searchSize phase depth * 16 + 1

def fallbackFuel (phase : Phase) (depth : Nat) : Nat :=
  searchSize phase depth * 64 + 1

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

def checkChunk (phase : Phase) (depth : Nat) (chunk : Chunk) : Bool :=
  (parentChunk chunk).all fun parent => checkParent phase depth parent

def ChunkChecks (phase : Phase) (depth : Nat) : Prop :=
  ∀ chunk : Chunk, checkChunk phase depth chunk = true

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
