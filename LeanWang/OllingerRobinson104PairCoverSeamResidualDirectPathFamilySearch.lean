/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathBridges

/-!
# Sound finite search from a localized hierarchy family

The executable search starts on every canonical descendant cycle of one parity
family inside the outer block at the origin.  Reaching a port with even parity
therefore certifies a `CanonicalCycleAncestorWithinFamily` for that port.  This
is the trusted bridge from the finite endpoint audits to the abstract direct
residual-path interface.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilySearch

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphRefinement RedShadeGraphSearch RedShadeGraphWeightedSearch
  ShadedFreeLineProjectionSourceLists
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualDirectPathBridges

set_option maxRecDepth 20000

/-- Levels in one parity family below an outer hierarchy level. -/
def familyLevels (outerLevel : Nat) (family : HierarchyFamily) : List Nat :=
  (List.range (outerLevel + 1)).filter fun level =>
    match family with
    | .even => decide ((outerLevel - level) % 2 = 0)
    | .odd => decide ((outerLevel - level) % 2 = 1)

theorem mem_familyLevels
    {outerLevel level : Nat} {family : HierarchyFamily}
    (member : level ∈ familyLevels outerLevel family) :
    level ≤ outerLevel ∧ InHierarchyFamily outerLevel level family := by
  simp only [familyLevels, List.mem_filter, List.mem_range] at member
  have levelLe : level ≤ outerLevel := by omega
  refine ⟨levelLe, ?_⟩
  have decompose := Nat.mod_add_div (outerLevel - level) 2
  cases family with
  | even =>
      simp only [decide_eq_true_eq] at member
      exact ⟨(outerLevel - level) / 2, by omega⟩
  | odd =>
      simp only [decide_eq_true_eq] at member
      exact ⟨(outerLevel - level) / 2, by omega⟩

/-- Descendant block coordinates inside the outer block at the origin. -/
def levelBlocks (outerLevel level : Nat) : List Nat :=
  List.range (2 ^ (outerLevel - level))

theorem hierarchyAddress_of_mem_levelBlocks
    {outerLevel level block : Nat} (levelLe : level ≤ outerLevel)
    (member : block ∈ levelBlocks outerLevel level) :
    HierarchyAddressWithin outerLevel 0 level block := by
  simp only [levelBlocks, List.mem_range] at member
  exact ⟨levelLe, Nat.div_eq_of_lt member⟩

/-- Every cycle port at one level, with even initial path parity. -/
def levelStarts (outerLevel level : Nat) : List WeightedStart :=
  let blocks := levelBlocks outerLevel level
  blocks.flatMap fun blockX =>
    blocks.flatMap fun blockY =>
      (cyclePorts
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3))).map fun port => ⟨port, false⟩

/-- All even starts on one localized hierarchy family. -/
def familyStarts (outerLevel : Nat) (family : HierarchyFamily) :
    List WeightedStart :=
  (familyLevels outerLevel family).flatMap (levelStarts outerLevel)

private theorem familyStart_data
    {outerLevel : Nat} {family : HierarchyFamily} {start : WeightedStart}
    (member : start ∈ familyStarts outerLevel family) :
    ∃ level blockX blockY,
      HierarchyAddressWithin outerLevel 0 level blockX ∧
      HierarchyAddressWithin outerLevel 0 level blockY ∧
      InHierarchyFamily outerLevel level family ∧
      OnCycle
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) start.port ∧
      start.parity = false := by
  simp only [familyStarts, List.mem_flatMap] at member
  rcases member with ⟨level, levelMember, startMember⟩
  obtain ⟨levelLe, inFamily⟩ := mem_familyLevels levelMember
  simp only [levelStarts, List.mem_flatMap] at startMember
  rcases startMember with ⟨blockX, blockXMember, startMember⟩
  rcases startMember with ⟨blockY, blockYMember, startMember⟩
  rw [List.mem_map] at startMember
  rcases startMember with ⟨port, portMember, rfl⟩
  refine ⟨level, blockX, blockY,
    hierarchyAddress_of_mem_levelBlocks levelLe blockXMember,
    hierarchyAddress_of_mem_levelBlocks levelLe blockYMember,
    inFamily, ?_, rfl⟩
  apply onCycle_of_mem_cyclePorts
  · have powerPos : 0 < 2 ^ level := pow_pos (by decide) _
    exact Nat.mul_lt_mul_of_pos_left (by omega) powerPos
  · have powerPos : 0 < 2 ^ level := pow_pos (by decide) _
    exact Nat.mul_lt_mul_of_pos_left (by omega) powerPos
  · exact portMember

/-- Lightweight family flood used by the finite target audits. -/
def nodes (root : Nat → Nat → Index) (outerLevel width fuel : Nat)
    (family : HierarchyFamily) : List ReachNode :=
  exploreFastWeightedReach (iterateRefine (outerLevel + 2) root)
    width width fuel (familyStarts outerLevel family)

/-- Boolean membership in the even-parity part of a family flood. -/
def reaches (root : Nat → Nat → Index) (outerLevel : Nat)
    (found : List ReachNode) (target : Port) : Bool :=
  portPresent (iterateRefine (outerLevel + 2) root) target &&
    found.any fun node => !node.parity && decide (node.current = target)

/-- Every accepted family-flood endpoint has the advertised localized family
ancestor. -/
theorem reaches_sound
    {root : Nat → Nat → Index} {outerLevel width fuel : Nat}
    {family : HierarchyFamily} {target : Port}
    (checked : reaches root outerLevel
      (nodes root outerLevel width fuel family) target = true) :
    CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root) target outerLevel 0 0 family := by
  simp only [reaches, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, nodeMember, nodeEven, nodeTarget⟩
  have sound := exploreFastWeightedReach_sound (show node ∈
    nodes root outerLevel width fuel family from nodeMember)
  rcases sound with ⟨start, startMember, path⟩
  rcases familyStart_data startMember with
    ⟨level, blockX, blockY, xWithin, yWithin, inFamily,
      entryOnCycle, startEven⟩
  have levelLe := xWithin.1
  have cycle := cycleAtLevelWithin root (blockX := blockX) (blockY := blockY)
    levelLe
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' nodeEven
  have targetPath : Path (iterateRefine (outerLevel + 2) root)
      target start.port false := by
    rw [nodeTarget] at path
    have forward : Path (iterateRefine (outerLevel + 2) root)
        start.port target false := by
      simpa [startEven, nodeParity] using path
    exact path_symm forward
  exact ⟨level, blockX, blockY, xWithin, yWithin, inFamily,
    cycle, start.port, entryOnCycle, targetPath⟩

end PairCoverSeamResidualDirectPathFamilySearch
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
