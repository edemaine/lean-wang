/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeCycleBridgeComposition
import LeanWang.OllingerRobinson104SparseFreeLineLocalProjection
import LeanWang.OllingerRobinson104ShadedFreeLinePatternRefinement

/-!
# Packaging refined-cycle routes as free-line projections

An odd route starting anywhere on the refined outer cycle can be backed by a
literal sparse copy of an old-cycle port.  This converts the nested-cycle
geometry directly into the `ProjectsTo` witnesses consumed by live row and
column certificates.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraCycleRoute

open OrientedRedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphRefinement RedShadeCycleConnectivity
  RedShadeCycleBridgeComposition ShadedFreeLinePatternRefinement
  SparseFreeLineLocalProjection

/-- Package an odd refined-cycle route as a projection from the old cycle. -/
def projectsTo_of_refinedCyclePath
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (oldCycle : CycleOn grid west east south north)
    (fineCycle : CycleOn (RedCycles.iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north))
    {source fineStart target : Port}
    (sourceOnCycle : OnCycle west east south north source)
    (fineStartOnCycle : OnCycle
      (4 * west) (4 * east) (4 * south) (4 * north) fineStart)
    (tail : Path (RedCycles.iterateRefine 2 grid) fineStart target true)
    (targetLive : portPresent (RedCycles.iterateRefine 2 grid) target = true) :
    ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) target := by
  have sparseSourceOnCycle : OnCycle
      (4 * west) (4 * east) (4 * south) (4 * north)
      (sparsePort source) := onCycle_sparse sourceOnCycle
  have connector := onCycle_connected fineCycle
    sparseSourceOnCycle fineStartOnCycle
  exact ProjectsTo.ofCyclePath oldCycle sourceOnCycle
    (by simpa [Bool.xor_assoc] using Path.trans connector tail) targetLive

/-- A descendant-cycle tail reached by an even bridge is an old-cycle projection. -/
theorem projectsTo_of_evenBridgeTail
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (oldCycle : CycleOn grid west east south north)
    (fineCycle : CycleOn (RedCycles.iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north))
    {descendantWest descendantEast descendantSouth descendantNorth : Nat}
    (descendantCycle : CycleOn (RedCycles.iterateRefine 2 grid)
      descendantWest descendantEast descendantSouth descendantNorth)
    (bridge : EvenCycleBridge (RedCycles.iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north)
      descendantWest descendantEast descendantSouth descendantNorth)
    {source descendantStart target : Port}
    (sourceOnCycle : OnCycle west east south north source)
    (descendantStartOnCycle : OnCycle descendantWest descendantEast
      descendantSouth descendantNorth descendantStart)
    (tail : Path (RedCycles.iterateRefine 2 grid)
      descendantStart target true)
    (targetLive : portPresent (RedCycles.iterateRefine 2 grid) target = true) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) target) := by
  rcases even_trans_odd descendantCycle bridge descendantStartOnCycle tail with
    ⟨fineStart, fineStartOnCycle, path⟩
  exact ⟨projectsTo_of_refinedCyclePath oldCycle fineCycle sourceOnCycle
    fineStartOnCycle path targetLive⟩

/-- Rebase a descendant weighted source across an even ancestor bridge. -/
theorem weightedSource_of_evenBridge
    {grid : Nat → Nat → Index}
    {ancestorWest ancestorEast ancestorSouth ancestorNorth : Nat}
    {descendantWest descendantEast descendantSouth descendantNorth : Nat}
    (ancestorCycle : CycleOn grid
      ancestorWest ancestorEast ancestorSouth ancestorNorth)
    (descendantCycle : CycleOn grid
      descendantWest descendantEast descendantSouth descendantNorth)
    (bridge : EvenCycleBridge grid
      ancestorWest ancestorEast ancestorSouth ancestorNorth
      descendantWest descendantEast descendantSouth descendantNorth)
    (source : WeightedSource grid descendantWest descendantEast
      descendantSouth descendantNorth) :
    ∃ rebased : WeightedSource grid ancestorWest ancestorEast
        ancestorSouth ancestorNorth,
      rebased.port = source.port ∧ rebased.parity = source.parity := by
  rcases bridge with ⟨ancestorStart, descendantEntry, ancestorStartOnCycle,
    descendantEntryOnCycle, bridgePath⟩
  have alongDescendant := onCycle_connected descendantCycle
    descendantEntryOnCycle source.onCycle
  refine ⟨{
    port := source.port
    parity := source.parity
    start := ancestorStart
    onCycle := ancestorStartOnCycle
    path := ?_
    startLive := portPresent_of_onCycle ancestorCycle ancestorStartOnCycle
    portLive := source.portLive
  }, rfl, rfl⟩
  simpa [Bool.xor_assoc] using
    Path.trans bridgePath (Path.trans alongDescendant source.path)

/-- Inherited sparse segments and separately routed created segments assemble a row. -/
theorem verticalProjectionAt_of_sparse_or_created
    {grid : Nat → Nat → Index} {west east south north oldRow fineRow : Nat}
    (previous : LiveRowCertificate grid west east south north oldRow)
    (coordinate : fineRow = sparseCoordinate oldRow)
    (classify : ∀ x,
      Signals.verticalInterior?
        (Signals.FreeCellLocal.componentAt (RedCycles.iterateRefine 2 grid)
          x fineRow)
        (Signals.FreeCellLocal.quadrantAt x fineRow) ≠ none →
      (∃ oldX, sparseCoordinate oldX = x ∧
        Signals.verticalInterior?
          (Signals.FreeCellLocal.componentAt grid oldX oldRow)
          (Signals.FreeCellLocal.quadrantAt oldX oldRow) ≠ none) ∨
      (Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨x, fineRow, .south⟩) ∨
       Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨x, fineRow, .north⟩))) :
    VerticalProjectionAt grid west east south north fineRow := by
  intro x hwest heast interior
  rcases classify x interior with inherited | created
  · rcases inherited with ⟨oldX, oldCoordinate, oldInterior⟩
    have oldWest : quarterWest west < oldX := by
      rw [← sparseCoordinate_lt_iff]
      simpa [oldCoordinate] using hwest
    have oldEast : oldX < quarterEast east := by
      rw [← sparseCoordinate_lt_iff]
      simpa [oldCoordinate] using heast
    rcases previous oldX oldWest oldEast oldInterior with
      ⟨source, sourceOdd, endpoint | endpoint⟩
    · left
      refine ⟨ProjectsTo.ofOddSourcePath sourceOdd ?_ ?_⟩
      · simpa [endpoint, sparsePort, oldCoordinate, coordinate] using
          (Path.refl (indexGrid := RedCycles.iterateRefine 2 grid)
            (sparsePort source.port))
      · simpa [endpoint, sparsePort, oldCoordinate, coordinate,
          WeightedSource.refine] using source.refine.portLive
    · right
      refine ⟨ProjectsTo.ofOddSourcePath sourceOdd ?_ ?_⟩
      · simpa [endpoint, sparsePort, oldCoordinate, coordinate] using
          (Path.refl (indexGrid := RedCycles.iterateRefine 2 grid)
            (sparsePort source.port))
      · simpa [endpoint, sparsePort, oldCoordinate, coordinate,
          WeightedSource.refine] using source.refine.portLive
  · exact created

/-- Inherited sparse segments and separately routed created segments assemble a column. -/
theorem horizontalProjectionAt_of_sparse_or_created
    {grid : Nat → Nat → Index}
    {west east south north oldColumn fineColumn : Nat}
    (previous : LiveColumnCertificate grid west east south north oldColumn)
    (coordinate : fineColumn = sparseCoordinate oldColumn)
    (classify : ∀ y,
      Signals.horizontalInterior?
        (Signals.FreeCellLocal.componentAt (RedCycles.iterateRefine 2 grid)
          fineColumn y)
        (Signals.FreeCellLocal.quadrantAt fineColumn y) ≠ none →
      (∃ oldY, sparseCoordinate oldY = y ∧
        Signals.horizontalInterior?
          (Signals.FreeCellLocal.componentAt grid oldColumn oldY)
          (Signals.FreeCellLocal.quadrantAt oldColumn oldY) ≠ none) ∨
      (Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨fineColumn, y, .west⟩) ∨
       Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨fineColumn, y, .east⟩))) :
    HorizontalProjectionAt grid west east south north fineColumn := by
  intro y hsouth hnorth interior
  rcases classify y interior with inherited | created
  · rcases inherited with ⟨oldY, oldCoordinate, oldInterior⟩
    have oldSouth : quarterSouth south < oldY := by
      rw [← sparseCoordinate_lt_iff]
      simpa [oldCoordinate] using hsouth
    have oldNorth : oldY < quarterNorth north := by
      rw [← sparseCoordinate_lt_iff]
      simpa [oldCoordinate] using hnorth
    rcases previous oldY oldSouth oldNorth oldInterior with
      ⟨source, sourceOdd, endpoint | endpoint⟩
    · left
      refine ⟨ProjectsTo.ofOddSourcePath sourceOdd ?_ ?_⟩
      · simpa [endpoint, sparsePort, oldCoordinate, coordinate] using
          (Path.refl (indexGrid := RedCycles.iterateRefine 2 grid)
            (sparsePort source.port))
      · simpa [endpoint, sparsePort, oldCoordinate, coordinate,
          WeightedSource.refine] using source.refine.portLive
    · right
      refine ⟨ProjectsTo.ofOddSourcePath sourceOdd ?_ ?_⟩
      · simpa [endpoint, sparsePort, oldCoordinate, coordinate] using
          (Path.refl (indexGrid := RedCycles.iterateRefine 2 grid)
            (sparsePort source.port))
      · simpa [endpoint, sparsePort, oldCoordinate, coordinate,
          WeightedSource.refine] using source.refine.portLive
  · exact created

end SparseFreeLineEvenExtraCycleRoute
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
