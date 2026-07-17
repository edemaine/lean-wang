/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPathBaseAudit
import LeanWang.Robinson.Closed104.PairCoverSeamPathQuerySearch

/-!
# Bounded semantics of the seam base certificates

Successful cached Boolean checks imply seam paths whose intermediate ports all
remain in the searched parent block.  The bounded statement can consequently
be transported from a canonical parent representative and later into an
arbitrary coarse-grid block.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathBoundedBase

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness BorderGeometry
  PairCoverSeamShadePaths PairCoverSeamPathSearch
  PairCoverSeamPathBoundedSearch PairCoverSeamPathBaseAudit
  PairCoverSeamArithmetic ShadedFreeLineRecurrence Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem horizontalPort_inBounds
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {column boundary : Nat}
    (hcolumn : column ∈ coordinates phase depth)
    (hboundary : boundary ∈ coordinates phase depth) :
    PortInBounds (horizontalPort grid column boundary)
      (searchSize phase depth) (searchSize phase depth) := by
  have hx := coordinate_lt_searchSize hcolumn
  have hy := coordinate_lt_searchSize hboundary
  unfold horizontalPort
  split <;> exact ⟨hx, hy⟩

private theorem verticalPort_inBounds
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {boundary row : Nat}
    (hboundary : boundary ∈ coordinates phase depth)
    (hrow : row ∈ coordinates phase depth) :
    PortInBounds (verticalPort grid boundary row)
      (searchSize phase depth) (searchSize phase depth) := by
  have hx := coordinate_lt_searchSize hboundary
  have hy := coordinate_lt_searchSize hrow
  unfold verticalPort
  split <;> exact ⟨hx, hy⟩

theorem checkParent_bounded_sound
    {phase : Phase} {depth : Nat} {parent : Index}
    (checked : checkParent phase depth parent = true) :
    BoundedParentPaths phase depth parent := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true] at checked
  constructor
  · dsimp only
    intro column boundary row hcolumn hboundary hrow
    exact verticalQueriesCheck_bounded_sound hrow
      (horizontalPort_inBounds hcolumn hboundary)
      (checked.1 column hcolumn boundary hboundary)
  · dsimp only
    intro boundary row column hboundary hrow hcolumn
    exact horizontalQueriesCheck_bounded_sound hcolumn
      (verticalPort_inBounds hboundary hrow)
      (checked.2 boundary hboundary row hrow)

theorem ChunkChecks.boundedPaths {phase : Phase} {depth : Nat}
    (checked : ChunkChecks phase depth) : BoundedPaths phase depth := by
  apply BoundedCanonicalPaths.paths
  intro parent hparent
  rw [canonicalParents_eq_chunks] at hparent
  simp only [List.mem_flatMap] at hparent
  rcases hparent with ⟨chunk, _, hparent⟩
  apply checkParent_bounded_sound
  have chunkChecked := checked chunk
  simp only [checkChunk, List.all_eq_true] at chunkChecked
  exact chunkChecked parent hparent

end PairCoverSeamPathBoundedBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
