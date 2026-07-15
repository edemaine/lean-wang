/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathBridges

/-!
# Canonical hierarchy targets at red-cycle corners

`RedShadeGraphBoards.OnCycle` deliberately names only strict side interiors.
The four inward red edges at a cycle's southwest, southeast, and northwest
corners are nevertheless valid obstruction-signal targets.  This module joins
those corner ports by even paths to a strict south-side entry and packages the
result as a same-family canonical ancestor.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathCornerTargets

open Figure16 QuarterGeometry OrientedRedCycles RedCycles RedShadeCycles
  RedShadeGraph RedShadeGraphBoards RedShadeGraphRefinement
  RedShadeCycleConnectivity
  PairCoverSeamShadePaths PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualDirectPathBridges Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem eastNorth_vertical_geometry
    {component : Thick} {quadrant : Quadrant}
    (east : RedShades.cornerEast component quadrant = true)
    (north : RedShades.cornerNorth component quadrant = true) :
    RedShades.hasSouth component quadrant = false ∧
      Signals.verticalInterior? component quadrant ≠ none := by
  cases component <;> cases quadrant <;>
    simp_all [RedShades.cornerEast, RedShades.cornerNorth,
      RedShades.hasSouth, RedShades.hasVertical,
      RedShades.cornerSouth, Signals.verticalInterior?, redVerticalAt,
      containsLine, Thick.lineSum?]

private theorem eastSouth_vertical_geometry
    {component : Thick} {quadrant : Quadrant}
    (east : RedShades.cornerEast component quadrant = true)
    (south : RedShades.cornerSouth component quadrant = true) :
    RedShades.hasSouth component quadrant = true ∧
      Signals.verticalInterior? component quadrant ≠ none := by
  cases component <;> cases quadrant <;>
    simp_all [RedShades.cornerEast, RedShades.cornerSouth,
      RedShades.hasSouth, RedShades.hasVertical,
      Signals.verticalInterior?, redVerticalAt, containsLine, Thick.lineSum?]

private theorem eastNorth_horizontal_geometry
    {component : Thick} {quadrant : Quadrant}
    (east : RedShades.cornerEast component quadrant = true)
    (north : RedShades.cornerNorth component quadrant = true) :
    RedShades.hasWest component quadrant = false ∧
      Signals.horizontalInterior? component quadrant ≠ none := by
  cases component <;> cases quadrant <;>
    simp_all [RedShades.cornerEast, RedShades.cornerNorth,
      RedShades.hasWest, RedShades.hasHorizontal,
      RedShades.cornerWest, Signals.horizontalInterior?, redHorizontalAt,
      containsLine, Thick.lineSum?]

private theorem westNorth_horizontal_geometry
    {component : Thick} {quadrant : Quadrant}
    (west : RedShades.cornerWest component quadrant = true)
    (north : RedShades.cornerNorth component quadrant = true) :
    RedShades.hasWest component quadrant = true ∧
      Signals.horizontalInterior? component quadrant ≠ none := by
  cases component <;> cases quadrant <;>
    simp_all [RedShades.cornerWest, RedShades.cornerNorth,
      RedShades.hasWest, RedShades.hasHorizontal,
      Signals.horizontalInterior?, redHorizontalAt, containsLine, Thick.lineSum?]

/-- The west side's southwest vertical corner is a genuine signal target and
connects evenly to a strict south-side cycle entry. -/
theorem verticalSouthwest_path
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (room : quarterWest west + 1 < quarterEast east) :
    Signals.verticalInterior?
        (componentAt grid (quarterWest west) (quarterSouth south))
        (quadrantAt (quarterWest west) (quarterSouth south)) ≠ none ∧
      ∃ entry,
        OnCycle west east south north entry ∧
          Path grid
            (verticalPort grid (quarterWest west) (quarterSouth south))
            entry false := by
  have corner := RedShadeCycles.CycleOn.southwest_corner cycle
  have geometry := eastNorth_vertical_geometry corner.1 corner.2
  let entry : Port :=
    ⟨quarterWest west + 1, quarterSouth south, .west⟩
  have entryOnCycle : OnCycle west east south north entry := by
    exact OnCycle.southWest _ (by omega) room
  have portEq : verticalPort grid
      (quarterWest west) (quarterSouth south) =
      ⟨quarterWest west, quarterSouth south, .north⟩ := by
    simp [verticalPort, geometry.1]
  have turn : Path grid
      ⟨quarterWest west, quarterSouth south, .north⟩
      ⟨quarterWest west, quarterSouth south, .east⟩ false :=
    Path.ofLink (Link.symm (Link.eastNorth _ _ corner.1 corner.2))
  have lane := southwest_to_south cycle (by omega) room
  refine ⟨geometry.2, entry, entryOnCycle, ?_⟩
  rw [portEq]
  simpa [entry, Bool.false_xor] using Path.trans turn lane

/-- The west side's northwest vertical corner is a genuine signal target and
connects evenly to a strict south-side cycle entry. -/
theorem verticalNorthwest_path
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (room : quarterWest west + 1 < quarterEast east) :
    Signals.verticalInterior?
        (componentAt grid (quarterWest west) (quarterNorth north))
        (quadrantAt (quarterWest west) (quarterNorth north)) ≠ none ∧
      ∃ entry,
        OnCycle west east south north entry ∧
          Path grid
            (verticalPort grid (quarterWest west) (quarterNorth north))
            entry false := by
  have northwest := RedShadeCycles.CycleOn.northwest_corner cycle
  have geometry := eastSouth_vertical_geometry northwest.1 northwest.2
  have southwest := RedShadeCycles.CycleOn.southwest_corner cycle
  let entry : Port :=
    ⟨quarterWest west + 1, quarterSouth south, .west⟩
  have entryOnCycle : OnCycle west east south north entry := by
    exact OnCycle.southWest _ (by omega) room
  have portEq : verticalPort grid
      (quarterWest west) (quarterNorth north) =
      ⟨quarterWest west, quarterNorth north, .south⟩ := by
    simp [verticalPort, geometry.1]
  have toNorthwest : Path grid
      ⟨quarterWest west, quarterSouth south, .east⟩
      ⟨quarterWest west, quarterNorth north, .south⟩ false :=
    Path.trans
      (Path.ofLink (Link.eastNorth _ _ southwest.1 southwest.2))
      (southwest_to_northwest_corner cycle)
  have lane := southwest_to_south cycle (by omega) room
  refine ⟨geometry.2, entry, entryOnCycle, ?_⟩
  rw [portEq]
  simpa [entry, Bool.false_xor] using
    Path.trans (path_symm toNorthwest) lane

/-- The south side's southwest horizontal corner is a genuine signal target
and connects evenly to a strict south-side cycle entry. -/
theorem horizontalSouthwest_path
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (room : quarterWest west + 1 < quarterEast east) :
    Signals.horizontalInterior?
        (componentAt grid (quarterWest west) (quarterSouth south))
        (quadrantAt (quarterWest west) (quarterSouth south)) ≠ none ∧
      ∃ entry,
        OnCycle west east south north entry ∧
          Path grid
            (horizontalPort grid (quarterWest west) (quarterSouth south))
            entry false := by
  have corner := RedShadeCycles.CycleOn.southwest_corner cycle
  have geometry := eastNorth_horizontal_geometry corner.1 corner.2
  let entry : Port :=
    ⟨quarterWest west + 1, quarterSouth south, .west⟩
  have entryOnCycle : OnCycle west east south north entry := by
    exact OnCycle.southWest _ (by omega) room
  have portEq : horizontalPort grid
      (quarterWest west) (quarterSouth south) =
      ⟨quarterWest west, quarterSouth south, .east⟩ := by
    simp [horizontalPort, geometry.1]
  refine ⟨geometry.2, entry, entryOnCycle, ?_⟩
  rw [portEq]
  simpa [entry] using southwest_to_south cycle (by omega) room

/-- The south side's southeast horizontal corner is a genuine signal target
and connects evenly to a strict south-side cycle entry. -/
theorem horizontalSoutheast_path
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (room : quarterWest west + 1 < quarterEast east) :
    Signals.horizontalInterior?
        (componentAt grid (quarterEast east) (quarterSouth south))
        (quadrantAt (quarterEast east) (quarterSouth south)) ≠ none ∧
      ∃ entry,
        OnCycle west east south north entry ∧
          Path grid
            (horizontalPort grid (quarterEast east) (quarterSouth south))
            entry false := by
  have corner := RedShadeCycles.CycleOn.southeast_corner cycle
  have geometry := westNorth_horizontal_geometry corner.1 corner.2
  let entry : Port :=
    ⟨quarterWest west + 1, quarterSouth south, .west⟩
  have entryOnCycle : OnCycle west east south north entry := by
    exact OnCycle.southWest _ (by omega) room
  have portEq : horizontalPort grid
      (quarterEast east) (quarterSouth south) =
      ⟨quarterEast east, quarterSouth south, .west⟩ := by
    simp [horizontalPort, geometry.1]
  have lane := southwest_to_south cycle (by omega) room
  refine ⟨geometry.2, entry, entryOnCycle, ?_⟩
  rw [portEq]
  simpa [entry, Bool.false_xor] using
    Path.trans (path_symm (southwest_to_east_corner cycle)) lane

private theorem canonical_room (level blockX : Nat) :
    quarterWest (2 ^ level * (4 * blockX + 1)) + 1 <
      quarterEast (2 ^ level * (4 * blockX + 3)) := by
  have positive : 0 < 2 ^ level := pow_pos (by decide) _
  unfold quarterWest quarterEast
  nlinarith

/-- The southwest vertical corner of a canonical descendant is a target in
that descendant's retained hierarchy family. -/
theorem verticalSouthwest
    {grid : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY level blockX blockY : Nat}
    {family : HierarchyFamily}
    (xWithin : HierarchyAddressWithin outerLevel outerBlockX level blockX)
    (yWithin : HierarchyAddressWithin outerLevel outerBlockY level blockY)
    (inFamily : InHierarchyFamily outerLevel level family)
    (cycle : CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3))) :
    CanonicalCycleAncestorWithinFamily grid
        (verticalPort grid
          (quarterWest (2 ^ level * (4 * blockX + 1)))
          (quarterSouth (2 ^ level * (4 * blockY + 1))))
        outerLevel outerBlockX outerBlockY family ∧
      Signals.verticalInterior?
        (componentAt grid
          (quarterWest (2 ^ level * (4 * blockX + 1)))
          (quarterSouth (2 ^ level * (4 * blockY + 1))))
        (quadrantAt
          (quarterWest (2 ^ level * (4 * blockX + 1)))
          (quarterSouth (2 ^ level * (4 * blockY + 1)))) ≠ none := by
  rcases verticalSouthwest_path cycle (canonical_room level blockX) with
    ⟨interior, entry, entryOnCycle, path⟩
  exact ⟨⟨level, blockX, blockY, xWithin, yWithin, inFamily,
    cycle, entry, entryOnCycle, path⟩, interior⟩

/-- The northwest vertical corner of a canonical descendant is a target in
that descendant's retained hierarchy family. -/
theorem verticalNorthwest
    {grid : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY level blockX blockY : Nat}
    {family : HierarchyFamily}
    (xWithin : HierarchyAddressWithin outerLevel outerBlockX level blockX)
    (yWithin : HierarchyAddressWithin outerLevel outerBlockY level blockY)
    (inFamily : InHierarchyFamily outerLevel level family)
    (cycle : CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3))) :
    CanonicalCycleAncestorWithinFamily grid
        (verticalPort grid
          (quarterWest (2 ^ level * (4 * blockX + 1)))
          (quarterNorth (2 ^ level * (4 * blockY + 3))))
        outerLevel outerBlockX outerBlockY family ∧
      Signals.verticalInterior?
        (componentAt grid
          (quarterWest (2 ^ level * (4 * blockX + 1)))
          (quarterNorth (2 ^ level * (4 * blockY + 3))))
        (quadrantAt
          (quarterWest (2 ^ level * (4 * blockX + 1)))
          (quarterNorth (2 ^ level * (4 * blockY + 3)))) ≠ none := by
  rcases verticalNorthwest_path cycle (canonical_room level blockX) with
    ⟨interior, entry, entryOnCycle, path⟩
  exact ⟨⟨level, blockX, blockY, xWithin, yWithin, inFamily,
    cycle, entry, entryOnCycle, path⟩, interior⟩

/-- The southwest horizontal corner of a canonical descendant is a target in
that descendant's retained hierarchy family. -/
theorem horizontalSouthwest
    {grid : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY level blockX blockY : Nat}
    {family : HierarchyFamily}
    (xWithin : HierarchyAddressWithin outerLevel outerBlockX level blockX)
    (yWithin : HierarchyAddressWithin outerLevel outerBlockY level blockY)
    (inFamily : InHierarchyFamily outerLevel level family)
    (cycle : CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3))) :
    CanonicalCycleAncestorWithinFamily grid
        (horizontalPort grid
          (quarterWest (2 ^ level * (4 * blockX + 1)))
          (quarterSouth (2 ^ level * (4 * blockY + 1))))
        outerLevel outerBlockX outerBlockY family ∧
      Signals.horizontalInterior?
        (componentAt grid
          (quarterWest (2 ^ level * (4 * blockX + 1)))
          (quarterSouth (2 ^ level * (4 * blockY + 1))))
        (quadrantAt
          (quarterWest (2 ^ level * (4 * blockX + 1)))
          (quarterSouth (2 ^ level * (4 * blockY + 1)))) ≠ none := by
  rcases horizontalSouthwest_path cycle (canonical_room level blockX) with
    ⟨interior, entry, entryOnCycle, path⟩
  exact ⟨⟨level, blockX, blockY, xWithin, yWithin, inFamily,
    cycle, entry, entryOnCycle, path⟩, interior⟩

/-- The southeast horizontal corner of a canonical descendant is a target in
that descendant's retained hierarchy family. -/
theorem horizontalSoutheast
    {grid : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY level blockX blockY : Nat}
    {family : HierarchyFamily}
    (xWithin : HierarchyAddressWithin outerLevel outerBlockX level blockX)
    (yWithin : HierarchyAddressWithin outerLevel outerBlockY level blockY)
    (inFamily : InHierarchyFamily outerLevel level family)
    (cycle : CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3))) :
    CanonicalCycleAncestorWithinFamily grid
        (horizontalPort grid
          (quarterEast (2 ^ level * (4 * blockX + 3)))
          (quarterSouth (2 ^ level * (4 * blockY + 1))))
        outerLevel outerBlockX outerBlockY family ∧
      Signals.horizontalInterior?
        (componentAt grid
          (quarterEast (2 ^ level * (4 * blockX + 3)))
          (quarterSouth (2 ^ level * (4 * blockY + 1))))
        (quadrantAt
          (quarterEast (2 ^ level * (4 * blockX + 3)))
          (quarterSouth (2 ^ level * (4 * blockY + 1)))) ≠ none := by
  rcases horizontalSoutheast_path cycle (canonical_room level blockX) with
    ⟨interior, entry, entryOnCycle, path⟩
  exact ⟨⟨level, blockX, blockY, xWithin, yWithin, inFamily,
    cycle, entry, entryOnCycle, path⟩, interior⟩

end PairCoverSeamResidualDirectPathCornerTargets
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
