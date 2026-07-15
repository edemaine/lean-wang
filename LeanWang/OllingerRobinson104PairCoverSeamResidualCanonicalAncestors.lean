/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCycleLocalTransport
import LeanWang.OllingerRobinson104PairCoverSeamResidualCycleBridges
import LeanWang.OllingerRobinson104TranslatedRedShadeCrossingPaths

/-!
# Canonical hierarchy ancestors for residual seam sources

Residual source ancestry must remember which Robinson hierarchy cycle it
reaches.  This module packages the cycle's scale and block coordinates and
normalizes the arbitrary parity returned by the created-source audit.  An even
local route stops on the audited cell cycle; an odd local route crosses the
odd child-to-parent bridge and therefore reaches the parent cycle evenly.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCanonicalAncestors

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadeGraphRefinement RedShadeCycleConnectivity
  RedShadeCycleCrossingPaths OrientedRedBoardTranslations
  TranslatedRedShadeCrossingPaths
  PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualCycleLocalTransport
  RefinedCoordinateProjection ShadedFreeLinePatternRefinement
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- An even route to a specifically named cycle in the Robinson hierarchy. -/
def CanonicalCycleAncestor (grid : Nat → Nat → Index)
    (source : Port) : Prop :=
  ∃ level blockX blockY,
    CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) ∧
    ∃ entry,
      OnCycle
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) entry ∧
      Path grid source entry false

/-- A hierarchy address belongs to the binary descendant block of an outer
canonical cycle. -/
def HierarchyAddressWithin (outerLevel outerBlock level block : Nat) : Prop :=
  level ≤ outerLevel ∧
    block / 2 ^ (outerLevel - level) = outerBlock

/-- A named cycle ancestor together with its position in a specified outer
hierarchy block.  Descendant selection needs this relation in addition to the
cycle's absolute name. -/
def CanonicalCycleAncestorWithin (grid : Nat → Nat → Index)
    (source : Port) (outerLevel outerBlockX outerBlockY : Nat) : Prop :=
  ∃ level blockX blockY,
    HierarchyAddressWithin outerLevel outerBlockX level blockX ∧
    HierarchyAddressWithin outerLevel outerBlockY level blockY ∧
    CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) ∧
    ∃ entry,
      OnCycle
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) entry ∧
      Path grid source entry false

/-- A localized canonical ancestor at one of the two levels produced directly
by the created-source parity normalization. -/
def LowCanonicalCycleAncestorWithin (grid : Nat → Nat → Index)
    (source : Port) (outerLevel outerBlockX outerBlockY : Nat) : Prop :=
  ∃ level blockX blockY,
    level ≤ 1 ∧
    HierarchyAddressWithin outerLevel outerBlockX level blockX ∧
    HierarchyAddressWithin outerLevel outerBlockY level blockY ∧
    CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) ∧
    ∃ entry,
      OnCycle
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) entry ∧
      Path grid source entry false

/-- A low canonical ancestor retaining the exact audited macrocell from which
parity normalization started.  An even local route stays at that level-zero
cell, while an odd route moves to its level-one parent. -/
def ExactLowCanonicalCycleAncestorWithin (grid : Nat → Nat → Index)
    (source : Port) (sourceBlockX sourceBlockY : Nat)
    (outerLevel outerBlockX outerBlockY : Nat) : Prop :=
  ∃ level blockX blockY,
    ((level = 0 ∧ blockX = sourceBlockX ∧ blockY = sourceBlockY) ∨
      (level = 1 ∧ blockX = sourceBlockX / 2 ∧
        blockY = sourceBlockY / 2)) ∧
    HierarchyAddressWithin outerLevel outerBlockX level blockX ∧
    HierarchyAddressWithin outerLevel outerBlockY level blockY ∧
    CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) ∧
    ∃ entry,
      OnCycle
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) entry ∧
      Path grid source entry false

/-- The exact low ancestor with its audited route parity still visible.
`false` stops at the source macrocell's level-zero cycle; `true` crosses to
its level-one parent. -/
def ExactParityCanonicalCycleAncestorWithin (grid : Nat → Nat → Index)
    (source : Port) (sourceBlockX sourceBlockY : Nat)
    (outerLevel outerBlockX outerBlockY : Nat) (parity : Bool) : Prop :=
  let level := if parity then 1 else 0
  let blockX := if parity then sourceBlockX / 2 else sourceBlockX
  let blockY := if parity then sourceBlockY / 2 else sourceBlockY
  HierarchyAddressWithin outerLevel outerBlockX level blockX ∧
    HierarchyAddressWithin outerLevel outerBlockY level blockY ∧
    CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) ∧
    ∃ entry,
      OnCycle
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) entry ∧
      Path grid source entry false

/-- Forgetting the audited parity retains the exact low ancestor. -/
theorem ExactParityCanonicalCycleAncestorWithin.toExactLow
    {grid : Nat → Nat → Index} {source : Port}
    {sourceBlockX sourceBlockY outerLevel outerBlockX outerBlockY : Nat}
    {parity : Bool}
    (ancestor : ExactParityCanonicalCycleAncestorWithin grid source
      sourceBlockX sourceBlockY outerLevel outerBlockX outerBlockY parity) :
    ExactLowCanonicalCycleAncestorWithin grid source
      sourceBlockX sourceBlockY outerLevel outerBlockX outerBlockY := by
  cases parity with
  | false =>
      simp only [ExactParityCanonicalCycleAncestorWithin, Bool.false_eq_true,
        ↓reduceIte] at ancestor
      rcases ancestor with ⟨xWithin, yWithin,
        cycle, entry, entryOnCycle, path⟩
      exact ⟨0, sourceBlockX, sourceBlockY, Or.inl ⟨rfl, rfl, rfl⟩,
        xWithin, yWithin, cycle, entry, entryOnCycle, path⟩
  | true =>
      simp only [ExactParityCanonicalCycleAncestorWithin, ↓reduceIte]
        at ancestor
      rcases ancestor with ⟨xWithin, yWithin,
        cycle, entry, entryOnCycle, path⟩
      exact ⟨1, sourceBlockX / 2, sourceBlockY / 2,
        Or.inr ⟨rfl, rfl, rfl⟩,
        xWithin, yWithin, cycle, entry, entryOnCycle, path⟩

/-- Forget the exact audited macrocell while retaining the low-level bound. -/
theorem ExactLowCanonicalCycleAncestorWithin.toLow
    {grid : Nat → Nat → Index} {source : Port}
    {sourceBlockX sourceBlockY outerLevel outerBlockX outerBlockY : Nat}
    (ancestor : ExactLowCanonicalCycleAncestorWithin grid source
      sourceBlockX sourceBlockY outerLevel outerBlockX outerBlockY) :
    LowCanonicalCycleAncestorWithin grid source
      outerLevel outerBlockX outerBlockY := by
  rcases ancestor with
    ⟨level, blockX, blockY, exactBlock, xWithin, yWithin,
      cycle, entry, entryOnCycle, path⟩
  refine ⟨level, blockX, blockY, ?_, xWithin, yWithin,
    cycle, entry, entryOnCycle, path⟩
  rcases exactBlock with exactBlock | exactBlock <;> omega

/-- Forget the low-level bound on a created source ancestor. -/
theorem LowCanonicalCycleAncestorWithin.toCanonicalCycleAncestorWithin
    {grid : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    (ancestor : LowCanonicalCycleAncestorWithin grid source
      outerLevel outerBlockX outerBlockY) :
    CanonicalCycleAncestorWithin grid source
      outerLevel outerBlockX outerBlockY := by
  rcases ancestor with
    ⟨level, blockX, blockY, _low, xWithin, yWithin,
      cycle, entry, entryOnCycle, path⟩
  exact ⟨level, blockX, blockY, xWithin, yWithin,
    cycle, entry, entryOnCycle, path⟩

theorem CanonicalCycleAncestorWithin.toCanonical
    {grid : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    (ancestor : CanonicalCycleAncestorWithin grid source
      outerLevel outerBlockX outerBlockY) :
    CanonicalCycleAncestor grid source := by
  rcases ancestor with
    ⟨level, blockX, blockY, _, _, cycle, entry, entryOnCycle, path⟩
  exact ⟨level, blockX, blockY, cycle, entry, entryOnCycle, path⟩

/-- Prepending an even route preserves both the canonical cycle and its outer
hierarchy address. -/
theorem CanonicalCycleAncestorWithin.of_evenPath
    {grid : Nat → Nat → Index} {source target : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    (ancestor : CanonicalCycleAncestorWithin grid target
      outerLevel outerBlockX outerBlockY)
    (path : Path grid source target false) :
    CanonicalCycleAncestorWithin grid source
      outerLevel outerBlockX outerBlockY := by
  rcases ancestor with
    ⟨level, blockX, blockY, xWithin, yWithin,
      cycle, entry, entryOnCycle, tail⟩
  exact ⟨level, blockX, blockY, xWithin, yWithin,
    cycle, entry, entryOnCycle, by simpa using Path.trans path tail⟩

private theorem HierarchyAddressWithin.parent_of_level_zero
    {outerLevel outerBlock block : Nat}
    (within : HierarchyAddressWithin (outerLevel + 2) outerBlock 0 block) :
    HierarchyAddressWithin (outerLevel + 2) outerBlock 1 (block / 2) := by
  rcases within with ⟨_, blockWithin⟩
  constructor
  · omega
  · have exponentZero : outerLevel + 2 - 0 = outerLevel + 2 := by omega
    have exponentParent : outerLevel + 2 - 1 = outerLevel + 1 := by omega
    rw [exponentZero] at blockWithin
    rw [exponentParent, Nat.div_div_eq_div_mul]
    have denominator : 2 * 2 ^ (outerLevel + 1) = 2 ^ (outerLevel + 2) := by
      rw [pow_succ]
      ring
    rwa [denominator]

/-- Two substitutions preserve the outer hierarchy address while raising both
the reached cycle and the enclosing cycle by two levels. -/
theorem CanonicalCycleAncestorWithin.refineSparse
    {grid : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    (ancestor : CanonicalCycleAncestorWithin grid source
      outerLevel outerBlockX outerBlockY)
    (sourceLive : portPresent grid source = true) :
    CanonicalCycleAncestorWithin (iterateRefine 2 grid) (sparsePort source)
      (outerLevel + 2) outerBlockX outerBlockY := by
  rcases ancestor with
    ⟨level, blockX, blockY, xWithin, yWithin,
      cycle, entry, entryOnCycle, path⟩
  have xWithin' : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX (level + 2) blockX := by
    rcases xWithin with ⟨levelLe, blockWithin⟩
    constructor
    · omega
    · have exponent : outerLevel + 2 - (level + 2) =
          outerLevel - level := by omega
      rwa [exponent]
  have yWithin' : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY (level + 2) blockY := by
    rcases yWithin with ⟨levelLe, blockWithin⟩
    constructor
    · omega
    · have exponent : outerLevel + 2 - (level + 2) =
          outerLevel - level := by omega
      rwa [exponent]
  have fineCycle := cycle.iterateRefine 2
  have entryLive := portPresent_of_onCycle cycle entryOnCycle
  have hscale : 2 ^ (level + 2) = 4 * 2 ^ level := by
    rw [pow_add]
    norm_num
    ac_rfl
  refine ⟨level + 2, blockX, blockY, xWithin', yWithin', ?_,
    sparsePort entry, ?_, ?_⟩
  · simpa [RedCycles.doubleN_eq, hscale, Nat.mul_assoc] using fineCycle
  · simpa [hscale, Nat.mul_assoc] using onCycle_sparse entryOnCycle
  · exact path_refine_sparse path sourceLive entryLive

/-- Forgetting the hierarchy name recovers the original cycle-ancestry
interface. -/
theorem CanonicalCycleAncestor.toCycleAncestor
    {grid : Nat → Nat → Index} {source : Port}
    (ancestor : CanonicalCycleAncestor grid source) :
    CycleAncestor grid source := by
  rcases ancestor with
    ⟨level, blockX, blockY, cycle, entry, entryOnCycle, path⟩
  exact ⟨_, _, _, _, cycle, entry, entryOnCycle, path⟩

/-- Prepending an even route preserves the canonical hierarchy name. -/
theorem CanonicalCycleAncestor.of_evenPath
    {grid : Nat → Nat → Index} {source target : Port}
    (ancestor : CanonicalCycleAncestor grid target)
    (path : Path grid source target false) :
    CanonicalCycleAncestor grid source := by
  rcases ancestor with
    ⟨level, blockX, blockY, cycle, entry, entryOnCycle, tail⟩
  exact ⟨level, blockX, blockY, cycle, entry, entryOnCycle,
    by simpa using Path.trans path tail⟩

/-- Two substitutions preserve the canonical cycle name, increasing its scale
by two while retaining its hierarchy block. -/
theorem CanonicalCycleAncestor.refineSparse
    {grid : Nat → Nat → Index} {source : Port}
    (ancestor : CanonicalCycleAncestor grid source)
    (sourceLive : portPresent grid source = true) :
    CanonicalCycleAncestor (iterateRefine 2 grid) (sparsePort source) := by
  rcases ancestor with
    ⟨level, blockX, blockY, cycle, entry, entryOnCycle, path⟩
  have fineCycle := cycle.iterateRefine 2
  have entryLive := portPresent_of_onCycle cycle entryOnCycle
  have hscale : 2 ^ (level + 2) = 4 * 2 ^ level := by
    rw [pow_add]
    norm_num
    ac_rfl
  refine ⟨level + 2, blockX, blockY, ?_, sparsePort entry, ?_, ?_⟩
  · simpa [RedCycles.doubleN_eq, hscale, Nat.mul_assoc] using fineCycle
  · simpa [hscale, Nat.mul_assoc] using onCycle_sparse entryOnCycle
  · exact path_refine_sparse path sourceLive entryLive

/-- A created source in a three-level refinement reaches a named hierarchy
cycle evenly.  The retained level records whether parity normalization stopped
at the cell cycle or its parent. -/
theorem ofLocalCycleRoute
    (grid : Nat → Nat → Index) {source : Port}
    (route : LocalCycleRouteAt (iterateRefine 1 grid) source) :
    CanonicalCycleAncestor (iterateRefine 3 grid) source := by
  unfold LocalCycleRouteAt at route
  rw [PlaneRedBoards.iterateRefine_add] at route
  rcases route with
    ⟨blockX, blockY, entry, parity, childCycle, entryOnChild, sourcePath⟩
  cases hparity : parity
  · refine ⟨0, blockX, blockY, ?_, entry, ?_, ?_⟩
    · simpa using childCycle
    · simpa using entryOnChild
    · simpa [hparity] using sourcePath
  · let parentX := blockX / 2
    let parentY := blockY / 2
    let cornerX : Fin 2 := ⟨blockX % 2, Nat.mod_lt _ (by decide)⟩
    let cornerY : Fin 2 := ⟨blockY % 2, Nat.mod_lt _ (by decide)⟩
    have hblockX : 2 * parentX + cornerX.val = blockX := by
      have := Nat.mod_add_div blockX 2
      dsimp [parentX, cornerX]
      omega
    have hblockY : 2 * parentY + cornerY.val = blockY := by
      have := Nat.mod_add_div blockY 2
      dsimp [parentY, cornerY]
      omega
    have bridge := cornerBridge grid (level := 1) (by omega)
      parentX parentY cornerX cornerY
    have bridge' : OddCycleBridge (iterateRefine 3 grid)
        (2 * (4 * parentX + 1)) (2 * (4 * parentX + 3))
        (2 * (4 * parentY + 1)) (2 * (4 * parentY + 3))
        (4 * blockX + 1) (4 * blockX + 3)
        (4 * blockY + 1) (4 * blockY + 3) := by
      simpa [hblockX, hblockY] using bridge
    rcases bridge' with
      ⟨parentEntry, childExit, parentEntryOnCycle, childExitOnCycle,
        bridgePath⟩
    have aroundChild := onCycle_connected childCycle
      entryOnChild childExitOnCycle
    have sourceToParent : Path (iterateRefine 3 grid)
        source parentEntry false := by
      have sourcePath' : Path (iterateRefine 3 grid) source entry true := by
        simpa [hparity] using sourcePath
      simpa [Bool.xor_assoc] using
        Path.trans sourcePath'
          (Path.trans aroundChild (path_symm bridgePath))
    refine ⟨1, parentX, parentY, ?_, parentEntry, ?_, sourceToParent⟩
    · simpa using at_scale grid 1 parentX parentY
    · simpa using parentEntryOnCycle

/-- Parity normalization retaining the audited route parity and therefore the
exact normalized hierarchy level. -/
theorem ofLocalCycleRouteAtBlockWithParityWithinExact
    (grid : Nat → Nat → Index) {source : Port}
    {outerLevel outerBlockX outerBlockY blockX blockY : Nat}
    {parity : Bool}
    (route : LocalCycleRouteAtBlockWithParity (iterateRefine 1 grid)
      source blockX blockY parity)
    (xWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX 0 blockX)
    (yWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY 0 blockY) :
    ExactParityCanonicalCycleAncestorWithin (iterateRefine 3 grid) source
      blockX blockY (outerLevel + 2) outerBlockX outerBlockY parity := by
  unfold LocalCycleRouteAtBlockWithParity at route
  rw [PlaneRedBoards.iterateRefine_add] at route
  rcases route with ⟨entry, childCycle, entryOnChild, sourcePath⟩
  cases hparity : parity
  · simp only [ExactParityCanonicalCycleAncestorWithin,
      Bool.false_eq_true, ↓reduceIte]
    refine ⟨xWithin, yWithin, ?_, entry, ?_, ?_⟩
    · simpa using childCycle
    · simpa using entryOnChild
    · simpa [hparity] using sourcePath
  · let parentX := blockX / 2
    let parentY := blockY / 2
    let cornerX : Fin 2 := ⟨blockX % 2, Nat.mod_lt _ (by decide)⟩
    let cornerY : Fin 2 := ⟨blockY % 2, Nat.mod_lt _ (by decide)⟩
    have hblockX : 2 * parentX + cornerX.val = blockX := by
      have := Nat.mod_add_div blockX 2
      dsimp [parentX, cornerX]
      omega
    have hblockY : 2 * parentY + cornerY.val = blockY := by
      have := Nat.mod_add_div blockY 2
      dsimp [parentY, cornerY]
      omega
    have bridge := cornerBridge grid (level := 1) (by omega)
      parentX parentY cornerX cornerY
    have bridge' : OddCycleBridge (iterateRefine 3 grid)
        (2 * (4 * parentX + 1)) (2 * (4 * parentX + 3))
        (2 * (4 * parentY + 1)) (2 * (4 * parentY + 3))
        (4 * blockX + 1) (4 * blockX + 3)
        (4 * blockY + 1) (4 * blockY + 3) := by
      simpa [hblockX, hblockY] using bridge
    rcases bridge' with
      ⟨parentEntry, childExit, parentEntryOnCycle, childExitOnCycle,
        bridgePath⟩
    have aroundChild := onCycle_connected childCycle
      entryOnChild childExitOnCycle
    have sourceToParent : Path (iterateRefine 3 grid)
        source parentEntry false := by
      have sourcePath' : Path (iterateRefine 3 grid) source entry true := by
        simpa [hparity] using sourcePath
      simpa [Bool.xor_assoc] using
        Path.trans sourcePath'
          (Path.trans aroundChild (path_symm bridgePath))
    simp only [ExactParityCanonicalCycleAncestorWithin, ↓reduceIte]
    refine ⟨HierarchyAddressWithin.parent_of_level_zero xWithin,
      HierarchyAddressWithin.parent_of_level_zero yWithin,
      ?_, parentEntry, ?_, sourceToParent⟩
    · simpa [parentX, parentY] using at_scale grid 1 parentX parentY
    · simpa [parentX, parentY] using parentEntryOnCycle

/-- Parity normalization for a local route whose audited macrocell is known to
belong to a specified outer hierarchy block.  The resulting cycle is at level
zero or one. -/
theorem ofLocalCycleRouteAtBlockWithinExactLow
    (grid : Nat → Nat → Index) {source : Port}
    {outerLevel outerBlockX outerBlockY blockX blockY : Nat}
    (route : LocalCycleRouteAtBlock (iterateRefine 1 grid)
      source blockX blockY)
    (xWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX 0 blockX)
    (yWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY 0 blockY) :
    ExactLowCanonicalCycleAncestorWithin (iterateRefine 3 grid) source
      blockX blockY (outerLevel + 2) outerBlockX outerBlockY := by
  unfold LocalCycleRouteAtBlock at route
  rcases route with
    ⟨entry, parity, childCycle, entryOnChild, sourcePath⟩
  let exactRoute : LocalCycleRouteAtBlockWithParity (iterateRefine 1 grid)
      source blockX blockY parity :=
    ⟨entry, childCycle, entryOnChild, sourcePath⟩
  exact (ofLocalCycleRouteAtBlockWithParityWithinExact
    grid exactRoute xWithin yWithin).toExactLow

/-- Compatibility projection of
`ofLocalCycleRouteAtBlockWithinExactLow`. -/
theorem ofLocalCycleRouteAtBlockWithinLow
    (grid : Nat → Nat → Index) {source : Port}
    {outerLevel outerBlockX outerBlockY blockX blockY : Nat}
    (route : LocalCycleRouteAtBlock (iterateRefine 1 grid)
      source blockX blockY)
    (xWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX 0 blockX)
    (yWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY 0 blockY) :
    LowCanonicalCycleAncestorWithin (iterateRefine 3 grid) source
      (outerLevel + 2) outerBlockX outerBlockY :=
  (ofLocalCycleRouteAtBlockWithinExactLow grid route xWithin yWithin).toLow

/-- Compatibility projection of `ofLocalCycleRouteAtBlockWithinLow`. -/
theorem ofLocalCycleRouteAtBlockWithin
    (grid : Nat → Nat → Index) {source : Port}
    {outerLevel outerBlockX outerBlockY blockX blockY : Nat}
    (route : LocalCycleRouteAtBlock (iterateRefine 1 grid)
      source blockX blockY)
    (xWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX 0 blockX)
    (yWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY 0 blockY) :
    CanonicalCycleAncestorWithin (iterateRefine 3 grid) source
      (outerLevel + 2) outerBlockX outerBlockY :=
  LowCanonicalCycleAncestorWithin.toCanonicalCycleAncestorWithin
    (ofLocalCycleRouteAtBlockWithinLow grid route xWithin yWithin)

set_option maxHeartbeats 2000000 in
-- The selector depends on the refinement equality used to expose its route.
/-- Horizontal created boundaries terminate at a named local hierarchy cycle. -/
theorem horizontalCreated
    (grid : Nat → Nat → Index) (column boundary : Nat)
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 3 grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    CanonicalCycleAncestor (iterateRefine 3 grid)
      (PairCoverSeamShadePaths.horizontalPort
        (iterateRefine 3 grid) column boundary) := by
  have hgrid : iterateRefine 2 (iterateRefine 1 grid) =
      iterateRefine 3 grid := by
    simpa using PlaneRedBoards.iterateRefine_add 2 1 grid
  have interior' : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (iterateRefine 1 grid)) column boundary)
      (quadrantAt column boundary) ≠ none := by
    rw [hgrid]
    exact interior
  have route := PairCoverSeamResidualCycleLocalTransport.horizontalCreated
    (iterateRefine 1 grid) column boundary createdBoundary interior'
  simpa [hgrid] using ofLocalCycleRoute grid route

set_option maxHeartbeats 2000000 in
-- The selector and its exact audited macrocell depend on the refinement equality.
/-- Horizontal created boundaries retain their enclosing hierarchy block. -/
theorem horizontalCreatedWithin
    (grid : Nat → Nat → Index) (column boundary : Nat)
    {outerLevel outerBlockX outerBlockY : Nat}
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 3 grid) column boundary)
      (quadrantAt column boundary) ≠ none)
    (xWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX 0 (column / 8))
    (yWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY 0 (boundary / 8)) :
    CanonicalCycleAncestorWithin (iterateRefine 3 grid)
      (PairCoverSeamShadePaths.horizontalPort
        (iterateRefine 3 grid) column boundary)
      (outerLevel + 2) outerBlockX outerBlockY := by
  have hgrid : iterateRefine 2 (iterateRefine 1 grid) =
      iterateRefine 3 grid := by
    simpa using PlaneRedBoards.iterateRefine_add 2 1 grid
  have interior' : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (iterateRefine 1 grid)) column boundary)
      (quadrantAt column boundary) ≠ none := by
    rw [hgrid]
    exact interior
  have route := PairCoverSeamResidualCycleLocalTransport.horizontalCreatedAtBlock
    (iterateRefine 1 grid) column boundary createdBoundary interior'
  simpa [hgrid] using
    ofLocalCycleRouteAtBlockWithin grid route xWithin yWithin

set_option maxHeartbeats 2000000 in
-- The selector depends on the refinement equality used to expose its route.
/-- Vertical created boundaries terminate at a named local hierarchy cycle. -/
theorem verticalCreated
    (grid : Nat → Nat → Index) (boundary row : Nat)
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 3 grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    CanonicalCycleAncestor (iterateRefine 3 grid)
      (PairCoverSeamShadePaths.verticalPort
        (iterateRefine 3 grid) boundary row) := by
  have hgrid : iterateRefine 2 (iterateRefine 1 grid) =
      iterateRefine 3 grid := by
    simpa using PlaneRedBoards.iterateRefine_add 2 1 grid
  have interior' : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (iterateRefine 1 grid)) boundary row)
      (quadrantAt boundary row) ≠ none := by
    rw [hgrid]
    exact interior
  have route := PairCoverSeamResidualCycleLocalTransport.verticalCreated
    (iterateRefine 1 grid) boundary row createdBoundary interior'
  simpa [hgrid] using ofLocalCycleRoute grid route

set_option maxHeartbeats 2000000 in
-- The selector and its exact audited macrocell depend on the refinement equality.
/-- Vertical created boundaries retain their enclosing hierarchy block. -/
theorem verticalCreatedWithin
    (grid : Nat → Nat → Index) (boundary row : Nat)
    {outerLevel outerBlockX outerBlockY : Nat}
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 3 grid) boundary row)
      (quadrantAt boundary row) ≠ none)
    (xWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX 0 (boundary / 8))
    (yWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY 0 (row / 8)) :
    CanonicalCycleAncestorWithin (iterateRefine 3 grid)
      (PairCoverSeamShadePaths.verticalPort
        (iterateRefine 3 grid) boundary row)
      (outerLevel + 2) outerBlockX outerBlockY := by
  have hgrid : iterateRefine 2 (iterateRefine 1 grid) =
      iterateRefine 3 grid := by
    simpa using PlaneRedBoards.iterateRefine_add 2 1 grid
  have interior' : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (iterateRefine 1 grid)) boundary row)
      (quadrantAt boundary row) ≠ none := by
    rw [hgrid]
    exact interior
  have route := PairCoverSeamResidualCycleLocalTransport.verticalCreatedAtBlock
    (iterateRefine 1 grid) boundary row createdBoundary interior'
  simpa [hgrid] using
    ofLocalCycleRouteAtBlockWithin grid route xWithin yWithin

end PairCoverSeamResidualCanonicalAncestors
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
