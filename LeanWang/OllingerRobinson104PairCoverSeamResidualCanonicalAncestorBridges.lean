/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorHierarchy
import LeanWang.OllingerRobinson104RedShadeCycleEvenDescendants

/-!
# Bridges between localized canonical residual ancestors

The existing descendant theorem stops at hierarchy level zero.  Residual
selection must also connect the odd hierarchy family, so this module shifts the
same base-four induction by an arbitrary bottom level.  It is downstream of the
finite source audits to keep their native caches stable.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualCanonicalAncestorBridges

open OrientedRedCycles RedCycles RedShadeGraph RedShadeGraphBoards
  RedShadeCycleConnectivity RedShadeGraphRefinement
  OrientedRedBoardTranslations RedShadeCycleCrossingPaths
  TranslatedRedShadeCrossingPaths
  RedShadeCycleBridgeComposition RedShadeCycleEvenDescendants
  PairCoverSeamResidualCanonicalAncestors

set_option maxRecDepth 20000

private def highBit (digit : Fin 4) : Fin 2 :=
  ⟨digit.val / 2, by omega⟩

private def lowBit (digit : Fin 4) : Fin 2 :=
  ⟨digit.val % 2, Nat.mod_lt _ (by decide)⟩

private theorem bits_eq (digit : Fin 4) :
    2 * (highBit digit).val + (lowBit digit).val = digit.val := by
  have h := Nat.mod_add_div digit.val 2
  dsimp [highBit, lowBit]
  omega

/-- Reverse an even bridge by reversing its path. -/
theorem EvenCycleBridge.symm
    {grid : Nat → Nat → Index}
    {firstWest firstEast firstSouth firstNorth : Nat}
    {secondWest secondEast secondSouth secondNorth : Nat}
    (bridge : EvenCycleBridge grid
      firstWest firstEast firstSouth firstNorth
      secondWest secondEast secondSouth secondNorth) :
    EvenCycleBridge grid
      secondWest secondEast secondSouth secondNorth
      firstWest firstEast firstSouth firstNorth := by
  rcases bridge with
    ⟨firstPort, secondPort, firstOnCycle, secondOnCycle, path⟩
  exact ⟨secondPort, firstPort, secondOnCycle, firstOnCycle, path_symm path⟩

/-- Reverse an odd bridge by reversing its path. -/
theorem OddCycleBridge.symm
    {grid : Nat → Nat → Index}
    {firstWest firstEast firstSouth firstNorth : Nat}
    {secondWest secondEast secondSouth secondNorth : Nat}
    (bridge : OddCycleBridge grid
      firstWest firstEast firstSouth firstNorth
      secondWest secondEast secondSouth secondNorth) :
    OddCycleBridge grid
      secondWest secondEast secondSouth secondNorth
      firstWest firstEast firstSouth firstNorth := by
  rcases bridge with
    ⟨firstPort, secondPort, firstOnCycle, secondOnCycle, path⟩
  exact ⟨secondPort, firstPort, secondOnCycle, firstOnCycle, path_symm path⟩

/-- An odd bridge followed by an even bridge remains odd. -/
theorem odd_trans_even
    {grid : Nat → Nat → Index}
    {firstWest firstEast firstSouth firstNorth : Nat}
    {middleWest middleEast middleSouth middleNorth : Nat}
    {lastWest lastEast lastSouth lastNorth : Nat}
    (middle : CycleOn grid middleWest middleEast middleSouth middleNorth)
    (first : OddCycleBridge grid
      firstWest firstEast firstSouth firstNorth
      middleWest middleEast middleSouth middleNorth)
    (second : EvenCycleBridge grid
      middleWest middleEast middleSouth middleNorth
      lastWest lastEast lastSouth lastNorth) :
    OddCycleBridge grid
      firstWest firstEast firstSouth firstNorth
      lastWest lastEast lastSouth lastNorth := by
  rcases first with ⟨firstPort, middleEntry, firstOnCycle,
    entryOnCycle, firstPath⟩
  rcases second with ⟨middleExit, lastPort, exitOnCycle,
    lastOnCycle, secondPath⟩
  have middlePath := onCycle_connected middle entryOnCycle exitOnCycle
  refine ⟨firstPort, lastPort, firstOnCycle, lastOnCycle, ?_⟩
  simpa [Bool.xor_assoc] using
    Path.trans firstPath (Path.trans middlePath secondPath)

/-- Every base-four descendant at an arbitrary lower hierarchy level is evenly
connected to its ancestor. -/
theorem evenDescendantBridge : ∀ (depth baseLevel : Nat)
    (grid : Nat → Nat → Index) (blockX blockY cellX cellY : Nat),
    4 ^ depth * blockX ≤ cellX →
    cellX < 4 ^ depth * (blockX + 1) →
    4 ^ depth * blockY ≤ cellY →
    cellY < 4 ^ depth * (blockY + 1) →
    EvenCycleBridge
      (iterateRefine (baseLevel + 2 * depth + 2) grid)
      (2 ^ (baseLevel + 2 * depth) * (4 * blockX + 1))
      (2 ^ (baseLevel + 2 * depth) * (4 * blockX + 3))
      (2 ^ (baseLevel + 2 * depth) * (4 * blockY + 1))
      (2 ^ (baseLevel + 2 * depth) * (4 * blockY + 3))
      (2 ^ baseLevel * (4 * cellX + 1))
      (2 ^ baseLevel * (4 * cellX + 3))
      (2 ^ baseLevel * (4 * cellY + 1))
      (2 ^ baseLevel * (4 * cellY + 3))
  | 0, baseLevel, grid, blockX, blockY, cellX, cellY,
      cellXLower, cellXUpper, cellYLower, cellYUpper => by
      have hx : cellX = blockX := by
        norm_num at cellXLower cellXUpper
        omega
      have hy : cellY = blockY := by
        norm_num at cellYLower cellYUpper
        omega
      subst cellX
      subst cellY
      have cycle := at_scale grid baseLevel blockX blockY
      have scalePos : 0 < 2 ^ baseLevel := pow_pos (by decide) _
      have width :
          2 ^ baseLevel * (4 * blockX + 1) + 1 <
            2 ^ baseLevel * (4 * blockX + 3) := by
        calc
          2 ^ baseLevel * (4 * blockX + 1) + 1 ≤
              2 ^ baseLevel * (4 * blockX + 1) + 2 ^ baseLevel := by omega
          _ = 2 ^ baseLevel * (4 * blockX + 2) := by ring
          _ < 2 ^ baseLevel * (4 * blockX + 3) :=
            Nat.mul_lt_mul_of_pos_left (by omega) scalePos
      simpa only [Nat.mul_zero, Nat.add_zero] using
        EvenCycleBridge.refl cycle width
  | depth + 1, baseLevel, grid, blockX, blockY, cellX, cellY,
      cellXLower, cellXUpper, cellYLower, cellYUpper => by
      let scale := 4 ^ depth
      have scalePos : 0 < scale := pow_pos (by decide) _
      have quotientXLower : 4 * blockX ≤ cellX / scale := by
        apply (Nat.le_div_iff_mul_le scalePos).2
        rw [pow_succ] at cellXLower
        calc
          4 * blockX * scale = 4 ^ depth * 4 * blockX := by
            dsimp [scale]
            ac_rfl
          _ ≤ cellX := cellXLower
      have quotientXUpper : cellX / scale < 4 * (blockX + 1) := by
        apply (Nat.div_lt_iff_lt_mul scalePos).2
        rw [pow_succ] at cellXUpper
        calc
          cellX < 4 ^ depth * 4 * (blockX + 1) := cellXUpper
          _ = 4 * (blockX + 1) * scale := by
            dsimp [scale]
            ac_rfl
      have quotientYLower : 4 * blockY ≤ cellY / scale := by
        apply (Nat.le_div_iff_mul_le scalePos).2
        rw [pow_succ] at cellYLower
        calc
          4 * blockY * scale = 4 ^ depth * 4 * blockY := by
            dsimp [scale]
            ac_rfl
          _ ≤ cellY := cellYLower
      have quotientYUpper : cellY / scale < 4 * (blockY + 1) := by
        apply (Nat.div_lt_iff_lt_mul scalePos).2
        rw [pow_succ] at cellYUpper
        calc
          cellY < 4 ^ depth * 4 * (blockY + 1) := cellYUpper
          _ = 4 * (blockY + 1) * scale := by
            dsimp [scale]
            ac_rfl
      let digitX : Fin 4 := ⟨cellX / scale - 4 * blockX, by omega⟩
      let digitY : Fin 4 := ⟨cellY / scale - 4 * blockY, by omega⟩
      let middleX := 4 * blockX + digitX.val
      let middleY := 4 * blockY + digitY.val
      have middleXEq : middleX = cellX / scale := by
        dsimp [middleX, digitX]
        omega
      have middleYEq : middleY = cellY / scale := by
        dsimp [middleY, digitY]
        omega
      have nextXLower : scale * middleX ≤ cellX := by
        rw [middleXEq]
        simpa [Nat.mul_comm] using Nat.div_mul_le_self cellX scale
      have nextXUpper : cellX < scale * (middleX + 1) := by
        rw [middleXEq]
        simpa [Nat.mul_comm] using Nat.lt_mul_div_succ cellX scalePos
      have nextYLower : scale * middleY ≤ cellY := by
        rw [middleYEq]
        simpa [Nat.mul_comm] using Nat.div_mul_le_self cellY scale
      have nextYUpper : cellY < scale * (middleY + 1) := by
        rw [middleYEq]
        simpa [Nat.mul_comm] using Nat.lt_mul_div_succ cellY scalePos
      have first := twoCornerBridge grid
        (level := baseLevel + 2 * (depth + 1)) (by omega)
        blockX blockY (highBit digitX) (highBit digitY)
        (lowBit digitX) (lowBit digitY)
      have second := evenDescendantBridge depth baseLevel
        (iterateRefine 2 grid) middleX middleY cellX cellY
        nextXLower nextXUpper nextYLower nextYUpper
      have middleCycle := at_scale (iterateRefine 2 grid)
        (baseLevel + 2 * depth) middleX middleY
      have gridEq :
          iterateRefine (baseLevel + 2 * depth + 2)
              (iterateRefine 2 grid) =
            iterateRefine (baseLevel + 2 * (depth + 1) + 2) grid := by
        rw [PlaneRedBoards.iterateRefine_add]
        congr 1
      rw [gridEq] at second middleCycle
      have levelEq : baseLevel + 2 * (depth + 1) - 2 =
          baseLevel + 2 * depth := by omega
      have bitsXEq :
          2 * (2 * blockX + (highBit digitX).val) + (lowBit digitX).val =
            middleX := by
        have bits := bits_eq digitX
        dsimp [middleX]
        omega
      have bitsYEq :
          2 * (2 * blockY + (highBit digitY).val) + (lowBit digitY).val =
            middleY := by
        have bits := bits_eq digitY
        dsimp [middleY]
        omega
      have first' : EvenCycleBridge
          (iterateRefine (baseLevel + 2 * (depth + 1) + 2) grid)
          (2 ^ (baseLevel + 2 * (depth + 1)) * (4 * blockX + 1))
          (2 ^ (baseLevel + 2 * (depth + 1)) * (4 * blockX + 3))
          (2 ^ (baseLevel + 2 * (depth + 1)) * (4 * blockY + 1))
          (2 ^ (baseLevel + 2 * (depth + 1)) * (4 * blockY + 3))
          (2 ^ (baseLevel + 2 * depth) * (4 * middleX + 1))
          (2 ^ (baseLevel + 2 * depth) * (4 * middleX + 3))
          (2 ^ (baseLevel + 2 * depth) * (4 * middleY + 1))
          (2 ^ (baseLevel + 2 * depth) * (4 * middleY + 3)) := by
        rw [levelEq, bitsXEq, bitsYEq] at first
        exact first
      exact even_trans_even middleCycle first' second

/-- Every descendant an odd number of levels below an arbitrary ancestor is
oddly connected to it. -/
theorem oddDescendantBridge
    (depth baseLevel : Nat) (grid : Nat → Nat → Index)
    (blockX blockY cellX cellY : Nat)
    (cellXLower : (2 * 4 ^ depth) * blockX ≤ cellX)
    (cellXUpper : cellX < (2 * 4 ^ depth) * (blockX + 1))
    (cellYLower : (2 * 4 ^ depth) * blockY ≤ cellY)
    (cellYUpper : cellY < (2 * 4 ^ depth) * (blockY + 1)) :
    OddCycleBridge
      (iterateRefine (baseLevel + 2 * depth + 3) grid)
      (2 ^ (baseLevel + 2 * depth + 1) * (4 * blockX + 1))
      (2 ^ (baseLevel + 2 * depth + 1) * (4 * blockX + 3))
      (2 ^ (baseLevel + 2 * depth + 1) * (4 * blockY + 1))
      (2 ^ (baseLevel + 2 * depth + 1) * (4 * blockY + 3))
      (2 ^ baseLevel * (4 * cellX + 1))
      (2 ^ baseLevel * (4 * cellX + 3))
      (2 ^ baseLevel * (4 * cellY + 1))
      (2 ^ baseLevel * (4 * cellY + 3)) := by
  let scale := 4 ^ depth
  have scalePos : 0 < scale := pow_pos (by decide) _
  have quotientXLower : 2 * blockX ≤ cellX / scale := by
    apply (Nat.le_div_iff_mul_le scalePos).2
    calc
      2 * blockX * scale = (2 * 4 ^ depth) * blockX := by
        dsimp [scale]
        ac_rfl
      _ ≤ cellX := cellXLower
  have quotientXUpper : cellX / scale < 2 * (blockX + 1) := by
    apply (Nat.div_lt_iff_lt_mul scalePos).2
    calc
      cellX < (2 * 4 ^ depth) * (blockX + 1) := cellXUpper
      _ = 2 * (blockX + 1) * scale := by
        dsimp [scale]
        ac_rfl
  have quotientYLower : 2 * blockY ≤ cellY / scale := by
    apply (Nat.le_div_iff_mul_le scalePos).2
    calc
      2 * blockY * scale = (2 * 4 ^ depth) * blockY := by
        dsimp [scale]
        ac_rfl
      _ ≤ cellY := cellYLower
  have quotientYUpper : cellY / scale < 2 * (blockY + 1) := by
    apply (Nat.div_lt_iff_lt_mul scalePos).2
    calc
      cellY < (2 * 4 ^ depth) * (blockY + 1) := cellYUpper
      _ = 2 * (blockY + 1) * scale := by
        dsimp [scale]
        ac_rfl
  let digitX : Fin 2 := ⟨cellX / scale - 2 * blockX, by omega⟩
  let digitY : Fin 2 := ⟨cellY / scale - 2 * blockY, by omega⟩
  let middleX := 2 * blockX + digitX.val
  let middleY := 2 * blockY + digitY.val
  have middleXEq : middleX = cellX / scale := by
    dsimp [middleX, digitX]
    omega
  have middleYEq : middleY = cellY / scale := by
    dsimp [middleY, digitY]
    omega
  have nextXLower : scale * middleX ≤ cellX := by
    rw [middleXEq]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self cellX scale
  have nextXUpper : cellX < scale * (middleX + 1) := by
    rw [middleXEq]
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ cellX scalePos
  have nextYLower : scale * middleY ≤ cellY := by
    rw [middleYEq]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self cellY scale
  have nextYUpper : cellY < scale * (middleY + 1) := by
    rw [middleYEq]
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ cellY scalePos
  have first := cornerBridge grid
    (level := baseLevel + 2 * depth + 1) (by omega)
    blockX blockY digitX digitY
  have second := evenDescendantBridge depth baseLevel
    (iterateRefine 1 grid) middleX middleY cellX cellY
    nextXLower nextXUpper nextYLower nextYUpper
  have middleCycle := at_scale (iterateRefine 1 grid)
    (baseLevel + 2 * depth) middleX middleY
  have gridEq :
      iterateRefine (baseLevel + 2 * depth + 2)
          (iterateRefine 1 grid) =
        iterateRefine (baseLevel + 2 * depth + 3) grid := by
    rw [PlaneRedBoards.iterateRefine_add]
  rw [gridEq] at second middleCycle
  have levelEq : baseLevel + 2 * depth + 1 - 1 =
      baseLevel + 2 * depth := by omega
  have first' : OddCycleBridge
      (iterateRefine (baseLevel + 2 * depth + 3) grid)
      (2 ^ (baseLevel + 2 * depth + 1) * (4 * blockX + 1))
      (2 ^ (baseLevel + 2 * depth + 1) * (4 * blockX + 3))
      (2 ^ (baseLevel + 2 * depth + 1) * (4 * blockY + 1))
      (2 ^ (baseLevel + 2 * depth + 1) * (4 * blockY + 3))
      (2 ^ (baseLevel + 2 * depth) * (4 * middleX + 1))
      (2 ^ (baseLevel + 2 * depth) * (4 * middleX + 3))
      (2 ^ (baseLevel + 2 * depth) * (4 * middleY + 1))
      (2 ^ (baseLevel + 2 * depth) * (4 * middleY + 3)) := by
    rw [levelEq] at first
    exact first
  exact odd_trans_even middleCycle first' second

end PairCoverSeamResidualCanonicalAncestorBridges
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
