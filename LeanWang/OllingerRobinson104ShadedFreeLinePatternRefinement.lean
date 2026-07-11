/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphPathRefinement
import LeanWang.OllingerRobinson104ShadedFreeLineGraph

/-!
# Whole-pattern refinement of shaded free-line certificates

Robinson's recurrence propagates the complete family of free rows and columns,
not each line independently. A weighted source retains the path already
supplied by the old pattern. Sources on the outer cycle have even parity;
sources on old free lines have odd parity. A projection path with complementary
parity therefore produces an odd path from the refined outer cycle to a new
target.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLinePatternRefinement

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphRefinement ShadedFreeLineGraph Signals.FreeCellLocal

set_option maxRecDepth 20000

/--
An actual old-pattern endpoint, together with its parity-labelled path from the
old outer cycle. The explicit liveness field is needed because matching links
also exist between absent quarter edges.
-/
structure WeightedSource (grid : Nat → Nat → Index)
    (west east south north : Nat) where
  port : Port
  parity : Bool
  start : Port
  onCycle : OnCycle west east south north start
  path : Path grid start port parity
  startLive : portPresent grid start = true
  portLive : portPresent grid port = true

/-- Every weighted source remains reachable after two substitutions. -/
theorem WeightedSource.refine
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (source : WeightedSource grid west east south north) :
    ∃ start : Port,
      OnCycle (4 * west) (4 * east) (4 * south) (4 * north) start ∧
        Path (iterateRefine 2 grid) start (sparsePort source.port)
          source.parity := by
  exact ⟨sparsePort source.start, onCycle_sparse source.onCycle,
    path_refine_sparse source.path source.startLive source.portLive⟩

/-- A target is reached with the parity complementary to its old source. -/
def ProjectsTo {grid : Nat → Nat → Index}
    {west east south north : Nat} (target : Port) : Prop :=
  ∃ source : WeightedSource grid west east south north,
    Path (iterateRefine 2 grid) (sparsePort source.port) target
      (Bool.xor source.parity true)

/-- The exact whole-pattern obligation needed for one Robinson recurrence step. -/
structure PatternProjection (grid : Nat → Nat → Index)
    (west east south north : Nat) (fineOffsets : List Nat)
    (fineCoordinate : Nat → Nat) : Prop where
  vertical : ∀ offset ∈ fineOffsets, ∀ x,
    quarterWest (4 * west) < x → x < quarterEast (4 * east) →
    Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) x (fineCoordinate offset))
      (quadrantAt x (fineCoordinate offset)) ≠ none →
    ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      ⟨x, fineCoordinate offset, .south⟩ ∨
    ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      ⟨x, fineCoordinate offset, .north⟩
  horizontal : ∀ offset ∈ fineOffsets, ∀ y,
    quarterSouth (4 * south) < y → y < quarterNorth (4 * north) →
    Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) (fineCoordinate offset) y)
      (quadrantAt (fineCoordinate offset) y) ≠ none →
    ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      ⟨fineCoordinate offset, y, .west⟩ ∨
    ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      ⟨fineCoordinate offset, y, .east⟩

theorem projected_path
    {grid : Nat → Nat → Index} {west east south north : Nat}
    {target : Port}
    (projection : ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) target) :
    ∃ start : Port,
      OnCycle (4 * west) (4 * east) (4 * south) (4 * north) start ∧
        Path (iterateRefine 2 grid) start target true := by
  rcases projection with ⟨source, tail⟩
  rcases source.refine with ⟨start, onCycle, head⟩
  refine ⟨start, onCycle, ?_⟩
  cases hparity : source.parity <;>
    simpa [hparity] using Path.trans head tail

/-- A whole-pattern projection supplies every refined row/column certificate. -/
theorem certificates_of_projection
    {grid : Nat → Nat → Index} {west east south north : Nat}
    {fineOffsets : List Nat} {fineCoordinate : Nat → Nat}
    (projection : PatternProjection grid west east south north
      fineOffsets fineCoordinate) :
    (∀ offset ∈ fineOffsets,
      RowCertificate (iterateRefine 2 grid)
        (4 * west) (4 * east) (4 * south) (4 * north)
        (fineCoordinate offset)) ∧
    (∀ offset ∈ fineOffsets,
      ColumnCertificate (iterateRefine 2 grid)
        (4 * west) (4 * east) (4 * south) (4 * north)
        (fineCoordinate offset)) := by
  constructor
  · intro offset mem x hwest heast interior
    rcases projection.vertical offset mem x hwest heast interior with
      projected | projected
    · rcases projected_path projected with ⟨start, onCycle, path⟩
      exact ⟨start, onCycle, Or.inl path⟩
    · rcases projected_path projected with ⟨start, onCycle, path⟩
      exact ⟨start, onCycle, Or.inr path⟩
  · intro offset mem y hsouth hnorth interior
    rcases projection.horizontal offset mem y hsouth hnorth interior with
      projected | projected
    · rcases projected_path projected with ⟨start, onCycle, path⟩
      exact ⟨start, onCycle, Or.inl path⟩
    · rcases projected_path projected with ⟨start, onCycle, path⟩
      exact ⟨start, onCycle, Or.inr path⟩

end ShadedFreeLinePatternRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
