/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorRecurrence
import LeanWang.OllingerRobinson104ShadedFreeLineProjectionSourceLists

/-!
# Finite base audit for canonical residual-source ancestors

For the even depth-four and odd depth-five bases, every live selector in the
stable hierarchy collar has an even path from one of two consecutive canonical
cycles.  The executable flood is shared by every selector of a parent tile.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCanonicalAncestorBaseAudit

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadeGraphRefinement RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch
  PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualCanonicalAncestorRecurrence
  ShadedFreeLineRecurrence ShadedFreeLineProjectionSourceLists
  OrientedRedBoardTranslations Signals.FreeCellLocal

set_option maxRecDepth 20000

def levels (phase : Phase) : Nat := refinementDepth phase 1

def width (phase : Phase) : Nat := 2 ^ (levels phase + 1)

def largeLevel (phase : Phase) : Nat := levels phase - 2

def smallLevel (phase : Phase) : Nat := levels phase - 3

def largeWest (phase : Phase) : Nat := 2 ^ largeLevel phase

def largeEast (phase : Phase) : Nat := 3 * largeWest phase

def smallWest (phase : Phase) : Nat := 2 ^ smallLevel phase

def smallEast (phase : Phase) : Nat := 3 * smallWest phase

def baseGrid (phase : Phase) (parent : Index) : Nat → Nat → Index :=
  iterateRefine (levels phase) (fun _ _ => parent)

def collarCoordinates (phase : Phase) : List Nat :=
  let lower := quarterWest (largeWest phase) - 1
  let upper := quarterEast (largeEast phase)
  (List.range (upper - lower)).map fun delta => lower + delta

def pairStarts (phase : Phase) : List WeightedStart :=
  ((cyclePorts (largeWest phase) (largeEast phase)
      (largeWest phase) (largeEast phase)) ++
    cyclePorts (smallWest phase) (smallEast phase)
      (smallWest phase) (smallEast phase)).map fun port => ⟨port, false⟩

def nodes (phase : Phase) (parent : Index) : List Node :=
  exploreFastWeighted (baseGrid phase parent) (width phase) (width phase)
    (width phase * width phase * 2) (pairStarts phase)

def reachesEven (grid : Nat → Nat → Index) (found : List Node)
    (target : Port) : Bool :=
  portPresent grid target &&
    found.any fun node =>
      !node.parity && decide (node.current = target)

def horizontalAt (phase : Phase) (parent : Index) (found : List Node)
    (x y : Nat) : Bool :=
  let grid := baseGrid phase parent
  let required := (Signals.horizontalInterior?
    (componentAt grid x y) (quadrantAt x y)).isSome
  !required || reachesEven grid found (horizontalPort grid x y)

def verticalAt (phase : Phase) (parent : Index) (found : List Node)
    (x y : Nat) : Bool :=
  let grid := baseGrid phase parent
  let required := (Signals.verticalInterior?
    (componentAt grid x y) (quadrantAt x y)).isSome
  !required || reachesEven grid found (verticalPort grid x y)

def checkParent (phase : Phase) (parent : Index) : Bool :=
  let coordinates := collarCoordinates phase
  let found := nodes phase parent
  (coordinates.all fun x =>
    coordinates.all (horizontalAt phase parent found x)) &&
  (coordinates.all fun x =>
    coordinates.all (verticalAt phase parent found x))

theorem largeCycle (phase : Phase) (parent : Index) :
    OrientedRedCycles.CycleOn (baseGrid phase parent)
      (largeWest phase) (largeEast phase)
      (largeWest phase) (largeEast phase) := by
  cases phase with
  | even =>
      simpa [baseGrid, levels, largeLevel, largeWest, largeEast,
        refinementDepth, Phase.extra] using
        at_scale (fun _ _ => parent) 2 0 0
  | odd =>
      simpa [baseGrid, levels, largeLevel, largeWest, largeEast,
        refinementDepth, Phase.extra] using
        at_scale (fun _ _ => parent) 3 0 0

theorem smallCycle (phase : Phase) (parent : Index) :
    OrientedRedCycles.CycleOn (baseGrid phase parent)
      (smallWest phase) (smallEast phase)
      (smallWest phase) (smallEast phase) := by
  cases phase with
  | even =>
      simpa [baseGrid, levels, smallLevel, smallWest, smallEast,
        refinementDepth, Phase.extra, PlaneRedBoards.iterateRefine_add] using
        at_scale (iterateRefine 1 (fun _ _ => parent)) 1 0 0
  | odd =>
      simpa [baseGrid, levels, smallLevel, smallWest, smallEast,
        refinementDepth, Phase.extra, PlaneRedBoards.iterateRefine_add] using
        at_scale (iterateRefine 1 (fun _ _ => parent)) 2 0 0

private theorem pairStarts_inBounds (phase : Phase) :
    ∀ start ∈ pairStarts phase,
      PortInBounds start.port (width phase) (width phase) := by
  intro start hstart
  rw [pairStarts, List.mem_map] at hstart
  rcases hstart with ⟨port, hport, rfl⟩
  simp only [List.mem_append] at hport
  have onCycle :
      OnCycle (largeWest phase) (largeEast phase)
          (largeWest phase) (largeEast phase) port ∨
        OnCycle (smallWest phase) (smallEast phase)
          (smallWest phase) (smallEast phase) port := by
    rcases hport with hport | hport
    · exact Or.inl (onCycle_of_mem_cyclePorts (by
          cases phase <;> decide) (by cases phase <;> decide) hport)
    · exact Or.inr (onCycle_of_mem_cyclePorts (by
          cases phase <;> decide) (by cases phase <;> decide) hport)
  cases phase <;> rcases onCycle with onCycle | onCycle <;> cases onCycle <;>
    simp_all [PortInBounds, width, levels, largeWest, largeEast,
      largeLevel, smallWest, smallEast, smallLevel, refinementDepth,
      Phase.extra, quarterWest, quarterEast, quarterSouth, quarterNorth] <;>
    omega

private theorem pairStarts_even (phase : Phase) :
    ∀ start ∈ pairStarts phase, start.parity = false := by
  intro start hstart
  rw [pairStarts, List.mem_map] at hstart
  rcases hstart with ⟨port, _, rfl⟩
  rfl

def BaseRoute (phase : Phase) (parent : Index) (target : Port) : Prop :=
  ∃ entry,
    (OnCycle (largeWest phase) (largeEast phase)
        (largeWest phase) (largeEast phase) entry ∨
      OnCycle (smallWest phase) (smallEast phase)
        (smallWest phase) (smallEast phase) entry) ∧
    BoundedPath (baseGrid phase parent) (width phase) (width phase)
      entry target false

theorem reachesEven_sound
    {phase : Phase} {parent : Index} {target : Port}
    (checked : reachesEven (baseGrid phase parent) (nodes phase parent)
      target = true) :
    BaseRoute phase parent target := by
  simp only [reachesEven, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rcases exploreFastWeighted_bounded_sound (pairStarts_inBounds phase)
      hnode with ⟨start, hstart, path⟩
  rw [hcurrent] at path
  rw [pairStarts, List.mem_map] at hstart
  rcases hstart with ⟨entry, hentry, rfl⟩
  simp only [List.mem_append] at hentry
  refine ⟨entry, ?_, ?_⟩
  · rcases hentry with hentry | hentry
    · exact Or.inl (onCycle_of_mem_cyclePorts (by
          cases phase <;> decide) (by cases phase <;> decide) hentry)
    · exact Or.inr (onCycle_of_mem_cyclePorts (by
          cases phase <;> decide) (by cases phase <;> decide) hentry)
  · have nodeEven : node.parity = false := by
      cases hnodeParity : node.parity <;> simp_all
    simpa [nodeEven] using path

theorem BaseRoute.ancestor
    {phase : Phase} {parent : Index} {target : Port}
    (route : BaseRoute phase parent target) :
    CanonicalCycleAncestor (baseGrid phase parent) target := by
  rcases route with ⟨entry, onLarge | onSmall, path⟩
  · refine ⟨largeLevel phase, 0, 0, ?_, entry, ?_, ?_⟩
    · simpa [largeWest, largeEast, Nat.mul_comm] using largeCycle phase parent
    · simpa [largeWest, largeEast, Nat.mul_comm] using onLarge
    · exact path_symm path.path
  · refine ⟨smallLevel phase, 0, 0, ?_, entry, ?_, ?_⟩
    · simpa [smallWest, smallEast, Nat.mul_comm] using smallCycle phase parent
    · simpa [smallWest, smallEast, Nat.mul_comm] using onSmall
    · exact path_symm path.path

theorem horizontalAt_sound
    {phase : Phase} {parent : Index} {x y : Nat}
    (checked : horizontalAt phase parent (nodes phase parent) x y = true)
    (interior : Signals.horizontalInterior?
      (componentAt (baseGrid phase parent) x y) (quadrantAt x y) ≠ none) :
    CanonicalCycleAncestor (baseGrid phase parent)
      (horizontalPort (baseGrid phase parent) x y) := by
  have required : (Signals.horizontalInterior?
      (componentAt (baseGrid phase parent) x y)
      (quadrantAt x y)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [horizontalAt, required, Bool.not_true, Bool.false_or] at checked
  exact (reachesEven_sound checked).ancestor

theorem verticalAt_sound
    {phase : Phase} {parent : Index} {x y : Nat}
    (checked : verticalAt phase parent (nodes phase parent) x y = true)
    (interior : Signals.verticalInterior?
      (componentAt (baseGrid phase parent) x y) (quadrantAt x y) ≠ none) :
    CanonicalCycleAncestor (baseGrid phase parent)
      (verticalPort (baseGrid phase parent) x y) := by
  have required : (Signals.verticalInterior?
      (componentAt (baseGrid phase parent) x y)
      (quadrantAt x y)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [verticalAt, required, Bool.not_true, Bool.false_or] at checked
  exact (reachesEven_sound checked).ancestor

theorem mem_collarCoordinates {phase : Phase} {coordinate : Nat}
    (bounds : InCollar (largeWest phase) (largeEast phase) coordinate) :
    coordinate ∈ collarCoordinates phase := by
  let lower := quarterWest (largeWest phase) - 1
  let upper := quarterEast (largeEast phase)
  have hlower : lower ≤ coordinate := bounds.1
  have hupper : coordinate < upper := bounds.2
  have heq : lower + (coordinate - lower) = coordinate :=
    Nat.add_sub_of_le hlower
  rw [collarCoordinates, List.mem_map]
  refine ⟨coordinate - lower, ?_, heq⟩
  simp only [List.mem_range]
  have hlowerUpper : lower ≤ upper := hlower.trans (Nat.le_of_lt hupper)
  omega

theorem checkParent_sound
    {phase : Phase} {parent : Index}
    (checked : checkParent phase parent = true) :
    SourceAncestorsIn (baseGrid phase parent)
      (largeWest phase) (largeEast phase)
      (largeWest phase) (largeEast phase) := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true] at checked
  constructor
  · intro column boundary columnBounds boundaryBounds interior
    exact horizontalAt_sound
      (checked.1 column (mem_collarCoordinates columnBounds)
        boundary (mem_collarCoordinates boundaryBounds)) interior
  · intro boundary row boundaryBounds rowBounds interior
    exact verticalAt_sound
      (checked.2 boundary (mem_collarCoordinates boundaryBounds)
        row (mem_collarCoordinates rowBounds)) interior

end PairCoverSeamResidualCanonicalAncestorBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
