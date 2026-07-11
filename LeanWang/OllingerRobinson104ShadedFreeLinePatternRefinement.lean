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

theorem portPresent_of_onCycle
    {grid : Nat → Nat → Index} {west east south north : Nat}
    {port : Port} (cycle : CycleOn grid west east south north)
    (onCycle : OnCycle west east south north port) :
    portPresent grid port = true := by
  cases onCycle with
  | southWest x hwest heast =>
      have line := RedShadeCycles.CycleOn.south_path cycle hwest heast
      simp [portPresent, RedShades.hasWest, line]
  | southEast x hwest heast =>
      have line := RedShadeCycles.CycleOn.south_path cycle hwest heast
      simp [portPresent, RedShades.hasEast, line]
  | northWest x hwest heast =>
      have line := RedShadeCycles.CycleOn.north_path cycle hwest heast
      simp [portPresent, RedShades.hasWest, line]
  | northEast x hwest heast =>
      have line := RedShadeCycles.CycleOn.north_path cycle hwest heast
      simp [portPresent, RedShades.hasEast, line]
  | westSouth y hsouth hnorth =>
      have line := RedShadeCycles.CycleOn.west_path cycle hsouth hnorth
      simp [portPresent, RedShades.hasSouth, line]
  | westNorth y hsouth hnorth =>
      have line := RedShadeCycles.CycleOn.west_path cycle hsouth hnorth
      simp [portPresent, RedShades.hasNorth, line]
  | eastSouth y hsouth hnorth =>
      have line := RedShadeCycles.CycleOn.east_path cycle hsouth hnorth
      simp [portPresent, RedShades.hasSouth, line]
  | eastNorth y hsouth hnorth =>
      have line := RedShadeCycles.CycleOn.east_path cycle hsouth hnorth
      simp [portPresent, RedShades.hasNorth, line]

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

/-- Every perpendicular segment on a retained row has a live odd source. -/
def LiveRowCertificate (grid : Nat → Nat → Index)
    (west east south north row : Nat) : Prop :=
  ∀ x, quarterWest west < x → x < quarterEast east →
    Signals.verticalInterior?
      (componentAt grid x row) (quadrantAt x row) ≠ none →
    ∃ source : WeightedSource grid west east south north,
      source.parity = true ∧
        (source.port = ⟨x, row, .south⟩ ∨
          source.port = ⟨x, row, .north⟩)

/-- Every perpendicular segment on a retained column has a live odd source. -/
def LiveColumnCertificate (grid : Nat → Nat → Index)
    (west east south north column : Nat) : Prop :=
  ∀ y, quarterSouth south < y → y < quarterNorth north →
    Signals.horizontalInterior?
      (componentAt grid column y) (quadrantAt column y) ≠ none →
    ∃ source : WeightedSource grid west east south north,
      source.parity = true ∧
        (source.port = ⟨column, y, .west⟩ ∨
          source.port = ⟨column, y, .east⟩)

theorem LiveRowCertificate.toRowCertificate
    {grid : Nat → Nat → Index} {west east south north row : Nat}
    (certificate : LiveRowCertificate grid west east south north row) :
    RowCertificate grid west east south north row := by
  intro x hwest heast interior
  rcases certificate x hwest heast interior with
    ⟨source, parity, endpoint⟩
  refine ⟨source.start, source.onCycle, ?_⟩
  rcases endpoint with endpoint | endpoint
  · left
    simpa [parity, endpoint] using source.path
  · right
    simpa [parity, endpoint] using source.path

theorem LiveColumnCertificate.toColumnCertificate
    {grid : Nat → Nat → Index} {west east south north column : Nat}
    (certificate : LiveColumnCertificate grid west east south north column) :
    ColumnCertificate grid west east south north column := by
  intro y hsouth hnorth interior
  rcases certificate y hsouth hnorth interior with
    ⟨source, parity, endpoint⟩
  refine ⟨source.start, source.onCycle, ?_⟩
  rcases endpoint with endpoint | endpoint
  · left
    simpa [parity, endpoint] using source.path
  · right
    simpa [parity, endpoint] using source.path

theorem portPresent_sparse (grid : Nat → Nat → Index) (port : Port) :
    portPresent (iterateRefine 2 grid) (sparsePort port) =
      portPresent grid port := by
  cases port with
  | mk x y side =>
      cases side <;>
        simp [portPresent, sparsePort, componentAt_iterateRefine_two_sparse,
          quadrantAt_sparseCoordinate]

/-- Every weighted source remains a weighted source after two substitutions. -/
def WeightedSource.refine
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (source : WeightedSource grid west east south north) :
    WeightedSource (iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north) where
  port := sparsePort source.port
  parity := source.parity
  start := sparsePort source.start
  onCycle := onCycle_sparse source.onCycle
  path := path_refine_sparse source.path source.startLive source.portLive
  startLive := by simpa [portPresent_sparse] using source.startLive
  portLive := by simpa [portPresent_sparse] using source.portLive

/-- A target is reached with the parity complementary to its old source. -/
structure ProjectsTo {grid : Nat → Nat → Index}
    {west east south north : Nat} (target : Port) where
  source : WeightedSource grid west east south north
  path : Path (iterateRefine 2 grid) (sparsePort source.port) target
    (Bool.xor source.parity true)
  targetLive : portPresent (iterateRefine 2 grid) target = true

/-- The exact whole-pattern obligation needed for one Robinson recurrence step. -/
structure PatternProjection (grid : Nat → Nat → Index)
    (west east south north : Nat) (fineOffsets : List Nat)
    (fineCoordinate : Nat → Nat) : Prop where
  vertical : ∀ offset ∈ fineOffsets, ∀ x,
    quarterWest (4 * west) < x → x < quarterEast (4 * east) →
    Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) x (fineCoordinate offset))
      (quadrantAt x (fineCoordinate offset)) ≠ none →
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      ⟨x, fineCoordinate offset, .south⟩) ∨
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      ⟨x, fineCoordinate offset, .north⟩)
  horizontal : ∀ offset ∈ fineOffsets, ∀ y,
    quarterSouth (4 * south) < y → y < quarterNorth (4 * north) →
    Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) (fineCoordinate offset) y)
      (quadrantAt (fineCoordinate offset) y) ≠ none →
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      ⟨fineCoordinate offset, y, .west⟩) ∨
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      ⟨fineCoordinate offset, y, .east⟩)

def ProjectsTo.weightedSource
    {grid : Nat → Nat → Index} {west east south north : Nat}
    {target : Port}
    (projection : ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) target) :
    WeightedSource (iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north) where
  port := target
  parity := true
  start := projection.source.refine.start
  onCycle := projection.source.refine.onCycle
  path := by
    cases hparity : projection.source.parity <;>
      simpa [WeightedSource.refine, hparity] using
        Path.trans projection.source.refine.path projection.path
  startLive := projection.source.refine.startLive
  portLive := projection.targetLive

/-- A whole-pattern projection supplies every refined live certificate. -/
theorem liveCertificates_of_projection
    {grid : Nat → Nat → Index} {west east south north : Nat}
    {fineOffsets : List Nat} {fineCoordinate : Nat → Nat}
    (projection : PatternProjection grid west east south north
      fineOffsets fineCoordinate) :
    (∀ offset ∈ fineOffsets,
      LiveRowCertificate (iterateRefine 2 grid)
        (4 * west) (4 * east) (4 * south) (4 * north)
        (fineCoordinate offset)) ∧
    (∀ offset ∈ fineOffsets,
      LiveColumnCertificate (iterateRefine 2 grid)
        (4 * west) (4 * east) (4 * south) (4 * north)
        (fineCoordinate offset)) := by
  constructor
  · intro offset mem x hwest heast interior
    rcases projection.vertical offset mem x hwest heast interior with
      projected | projected
    · rcases projected with ⟨projected⟩
      exact ⟨projected.weightedSource, rfl, Or.inl rfl⟩
    · rcases projected with ⟨projected⟩
      exact ⟨projected.weightedSource, rfl, Or.inr rfl⟩
  · intro offset mem y hsouth hnorth interior
    rcases projection.horizontal offset mem y hsouth hnorth interior with
      projected | projected
    · rcases projected with ⟨projected⟩
      exact ⟨projected.weightedSource, rfl, Or.inl rfl⟩
    · rcases projected with ⟨projected⟩
      exact ⟨projected.weightedSource, rfl, Or.inr rfl⟩

/-- Forgetting endpoint liveness recovers the original graph certificates. -/
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
  have live := liveCertificates_of_projection projection
  exact ⟨fun offset mem => (live.1 offset mem).toRowCertificate,
    fun offset mem => (live.2 offset mem).toColumnCertificate⟩

end ShadedFreeLinePatternRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
