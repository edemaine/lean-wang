/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverage
import LeanWang.Robinson.Closed104.RedShadeGraphPathRefinement
import LeanWang.Robinson.Closed104.RedShadeCycleEvenDescendants

/-!
# Connectivity to the root Robinson cycle

Every live red-graph port in the central half-open square of an even-depth
supertile is connected to its enclosing Robinson cycle.  The proof iterates a
single finite local certificate: a local route starts either on the newly
created cell cycle or at the sparse image of an older live port.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphRootConnectivity

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphLocalCoverage RedShadeGraphRefinement
  RedShadeGraphSearchSoundness RedShadeGraphTranslation
  RedShadeCycleConnectivity
  RedShadeCycleBridgeComposition RedShadeCycleEvenDescendants
  OrientedRedBoardTranslations

def scale (depth : Nat) : Nat := 4 ^ depth

def RootReachable (depth : Nat) (grid : Nat → Nat → Index)
    (target : Port) : Prop :=
  ∃ start parity,
    OnCycle (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) start ∧
    Path (iterateRefine (2 * depth + 2) grid) start target parity

private theorem mem_portsIn {width height : Nat} {port : Port}
    (hx : port.x < width) (hy : port.y < height) :
    port ∈ portsIn width height := by
  rcases port with ⟨x, y, side⟩
  simp only [portsIn, List.mem_flatMap, List.mem_range]
  refine ⟨y, hy, x, hx, ?_⟩
  cases side <;> simp

private theorem bounds_of_mem_portsIn {width height : Nat} {port : Port}
    (portMem : port ∈ portsIn width height) :
    port.x < width ∧ port.y < height := by
  unfold portsIn at portMem
  rw [List.mem_flatMap] at portMem
  rcases portMem with ⟨y, hy, portMem⟩
  rw [List.mem_flatMap] at portMem
  rcases portMem with ⟨x, hx, portMem⟩
  simp only [List.mem_range] at hy hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at portMem
  rcases portMem with rfl | rfl | rfl | rfl <;> exact ⟨hx, hy⟩

private theorem portPresent_of_onCycle
    {grid : Nat → Nat → Index} {west east south north : Nat}
    {port : Port} (cycle : CycleOn grid west east south north)
    (onCycle : OnCycle west east south north port) :
    portPresent grid port = true := by
  cases onCycle with
  | southWest x hwest heast =>
      have line := CycleOn.south_path cycle hwest heast
      simp [portPresent, RedShades.hasWest, line]
  | southEast x hwest heast =>
      have line := CycleOn.south_path cycle hwest heast
      simp [portPresent, RedShades.hasEast, line]
  | northWest x hwest heast =>
      have line := CycleOn.north_path cycle hwest heast
      simp [portPresent, RedShades.hasWest, line]
  | northEast x hwest heast =>
      have line := CycleOn.north_path cycle hwest heast
      simp [portPresent, RedShades.hasEast, line]
  | westSouth y hsouth hnorth =>
      have line := CycleOn.west_path cycle hsouth hnorth
      simp [portPresent, RedShades.hasSouth, line]
  | westNorth y hsouth hnorth =>
      have line := CycleOn.west_path cycle hsouth hnorth
      simp [portPresent, RedShades.hasNorth, line]
  | eastSouth y hsouth hnorth =>
      have line := CycleOn.east_path cycle hsouth hnorth
      simp [portPresent, RedShades.hasSouth, line]
  | eastNorth y hsouth hnorth =>
      have line := CycleOn.east_path cycle hsouth hnorth
      simp [portPresent, RedShades.hasNorth, line]

private theorem sparseCoordinate_two_block (block offset : Nat)
    (hoffset : offset < 2) :
    sparseCoordinate (2 * block + offset) =
      8 * block + sparseCoordinate offset := by
  have hoffsetCases : offset = 0 ∨ offset = 1 := by omega
  rcases hoffsetCases with rfl | rfl
  · simp [sparseCoordinate, macroOrigin, localCoordinate]
  · simp [sparseCoordinate, macroOrigin, localCoordinate]
    omega

private theorem sparsePort_two_block (blockX blockY : Nat) (port : Port)
    (hx : port.x < 2) (hy : port.y < 2) :
    sparsePort (translatePort port (2 * blockX) (2 * blockY)) =
      translatePort (sparsePort port) (8 * blockX) (8 * blockY) := by
  rcases port with ⟨x, y, side⟩
  simp only [sparsePort, translatePort]
  rw [sparseCoordinate_two_block blockX x hx,
    sparseCoordinate_two_block blockY y hy]

private theorem rootCycle (depth : Nat) (grid : Nat → Nat → Index) :
    CycleOn (iterateRefine (2 * depth + 2) grid)
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) := by
  have cycle := at_scale grid (2 * depth) 0 0
  have hpow : 2 ^ (2 * depth) = scale depth := by
    rw [pow_mul]
    norm_num [scale]
  rw [hpow] at cycle
  simpa [Nat.mul_comm] using cycle

private theorem localCycleSource_onCycle :
    OnCycle 1 3 1 3 cycleSource := by
  change OnCycle 1 3 1 3 ⟨4, 3, .west⟩
  apply OnCycle.southWest <;> decide

/-- Every live graph port in the central square of the root supertile is
connected, with some crossing parity, to the root Robinson cycle. -/
theorem root_reachable : ∀ (depth : Nat) (grid : Nat → Nat → Index)
    {target : Port},
    grid 0 0 = 0 →
    2 * scale depth ≤ target.x → target.x < 6 * scale depth →
    2 * scale depth ≤ target.y → target.y < 6 * scale depth →
    portPresent (iterateRefine (2 * depth + 2) grid) target = true →
    RootReachable depth grid target
  | 0, grid, target, root, targetWest, targetEast, targetSouth, targetNorth,
      targetPresent => by
      have targetMem : target ∈ portsIn 8 8 :=
        mem_portsIn (by simp [scale] at targetEast ⊢; omega)
          (by simp [scale] at targetNorth ⊢; omega)
      have targetWest' : 2 ≤ target.x := by simpa [scale] using targetWest
      have targetEast' : target.x < 6 := by simpa [scale] using targetEast
      have targetSouth' : 2 ≤ target.y := by simpa [scale] using targetSouth
      have targetNorth' : target.y < 6 := by simpa [scale] using targetNorth
      have localToGlobal := portPresent_two_block grid 0 0 target
        (by omega) (by omega)
      have targetPresent' :
          portPresent (iterateRefine 2 grid)
            (translatePort target (8 * 0) (8 * 0)) = true := by
        simpa [translatePort] using targetPresent
      have localPresent : portPresent (fineGrid 0) target = true := by
        rw [root] at localToGlobal
        exact localToGlobal.trans targetPresent'
      rcases base_exists_boundedPath targetMem targetWest' targetEast'
          targetSouth' targetNorth' localPresent with ⟨parity, localPath⟩
      have translated := boundedPath_two_block grid 0 0 (by
        simpa [root] using localPath)
      refine ⟨cycleSource, parity, ?_, ?_⟩
      · simpa [scale] using localCycleSource_onCycle
      · simpa [translatePort] using translated
  | depth + 1, grid, target, root, targetWest, targetEast, targetSouth,
      targetNorth, targetPresent => by
      let oldGrid := iterateRefine (2 * depth + 2) grid
      let newGrid := iterateRefine (2 * (depth + 1) + 2) grid
      let blockX := target.x / 8
      let blockY := target.y / 8
      let localTarget : Port :=
        ⟨target.x % 8, target.y % 8, target.side⟩
      have gridEq : iterateRefine 2 oldGrid = newGrid := by
        dsimp [oldGrid, newGrid]
        rw [PlaneRedBoards.iterateRefine_add]
        congr 1
        omega
      have localTargetX : localTarget.x < 8 := by
        exact Nat.mod_lt _ (by decide)
      have localTargetY : localTarget.y < 8 := by
        exact Nat.mod_lt _ (by decide)
      have targetEq :
          translatePort localTarget (8 * blockX) (8 * blockY) = target := by
        rcases target with ⟨x, y, side⟩
        simp only [localTarget, blockX, blockY, translatePort]
        have hx := Nat.mod_add_div x 8
        have hy := Nat.mod_add_div y 8
        congr <;> omega
      have localPresent :
          portPresent (fineGrid (oldGrid blockX blockY)) localTarget = true := by
        rw [portPresent_two_block oldGrid blockX blockY localTarget
          localTargetX localTargetY, gridEq, targetEq]
        exact targetPresent
      rcases exists_boundedPath (oldGrid blockX blockY)
          (mem_portsIn localTargetX localTargetY) localPresent with
        ⟨source, sourceMem, localParity, localPath⟩
      have translatedPath := boundedPath_two_block oldGrid blockX blockY localPath
      rw [gridEq, targetEq] at translatedPath
      have scaleSucc : scale (depth + 1) = 4 * scale depth := by
        simp [scale, pow_succ, Nat.mul_comm]
      have scalePos : 0 < scale depth := pow_pos (by decide) _
      have blockXLower : scale depth ≤ blockX := by
        apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
        rw [scaleSucc] at targetWest
        omega
      have blockXUpper : blockX < 3 * scale depth := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).2
        rw [scaleSucc] at targetEast
        omega
      have blockYLower : scale depth ≤ blockY := by
        apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
        rw [scaleSucc] at targetSouth
        omega
      have blockYUpper : blockY < 3 * scale depth := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).2
        rw [scaleSucc] at targetNorth
        omega
      rcases source_cases sourceMem with sourceEq | inherited
      · subst source
        have cellCycle : CycleOn newGrid
            (4 * blockX + 1) (4 * blockX + 3)
            (4 * blockY + 1) (4 * blockY + 3) := by
          have cycle := depthTwo_at oldGrid blockX blockY
          rw [gridEq] at cycle
          exact cycle
        have sourceOnCell : OnCycle
            (4 * blockX + 1) (4 * blockX + 3)
            (4 * blockY + 1) (4 * blockY + 3)
            (translatePort cycleSource (8 * blockX) (8 * blockY)) := by
          have sourceEq :
              translatePort cycleSource (8 * blockX) (8 * blockY) =
                ⟨8 * blockX + 4, 8 * blockY + 3, .west⟩ := by
            simp [translatePort, cycleSource, quarterWest, quarterSouth]
          have southEq : quarterSouth (4 * blockY + 1) = 8 * blockY + 3 := by
            simp [quarterSouth]
            omega
          rw [sourceEq]
          simpa only [southEq] using
            (OnCycle.southWest
              (west := 4 * blockX + 1) (east := 4 * blockX + 3)
              (south := 4 * blockY + 1) (north := 4 * blockY + 3)
              (8 * blockX + 4)
              (by simp [quarterWest]; omega)
              (by simp [quarterEast]; omega))
        have blockXBound : blockX < 4 ^ (depth + 1) := by
          rw [show 4 ^ (depth + 1) = 4 * scale depth by
            simp [scale, pow_succ, Nat.mul_comm]]
          omega
        have blockYBound : blockY < 4 ^ (depth + 1) := by
          rw [show 4 ^ (depth + 1) = 4 * scale depth by
            simp [scale, pow_succ, Nat.mul_comm]]
          omega
        rcases rootDescendantBridge (depth + 1) grid blockX blockY
            blockXBound blockYBound with
          ⟨rootStart, cellEntry, rootStartOn, cellEntryOn, bridgePath⟩
        have alongCell := onCycle_connected cellCycle cellEntryOn sourceOnCell
        refine ⟨rootStart, localParity, ?_, ?_⟩
        · simpa [scale] using rootStartOn
        · simpa using Path.trans bridgePath
            (Path.trans alongCell translatedPath)
      · rcases inherited with ⟨old, oldMem, oldLocalPresent, sourceEq⟩
        subst source
        have oldBounds := bounds_of_mem_portsIn oldMem
        let oldGlobal := translatePort old (2 * blockX) (2 * blockY)
        have oldPresent : portPresent oldGrid oldGlobal = true := by
          rw [← portPresent_old_block oldGrid blockX blockY old
            oldBounds.1 oldBounds.2]
          exact oldLocalPresent
        have oldWest : 2 * scale depth ≤ oldGlobal.x := by
          dsimp [oldGlobal, translatePort]
          omega
        have oldEast : oldGlobal.x < 6 * scale depth := by
          dsimp [oldGlobal, translatePort]
          omega
        have oldSouth : 2 * scale depth ≤ oldGlobal.y := by
          dsimp [oldGlobal, translatePort]
          omega
        have oldNorth : oldGlobal.y < 6 * scale depth := by
          dsimp [oldGlobal, translatePort]
          omega
        rcases root_reachable depth grid root oldWest oldEast oldSouth oldNorth
            oldPresent with ⟨oldStart, oldParity, oldStartOn, oldPath⟩
        have oldStartPresent :=
          portPresent_of_onCycle (rootCycle depth grid) oldStartOn
        have refinedPath :=
          path_refine_sparse oldPath oldStartPresent oldPresent
        rw [gridEq] at refinedPath
        have sourceGlobalEq :
            sparsePort oldGlobal =
              translatePort (sparsePort old) (8 * blockX) (8 * blockY) := by
          exact sparsePort_two_block blockX blockY old
            oldBounds.1 oldBounds.2
        rw [← sourceGlobalEq] at translatedPath
        refine ⟨sparsePort oldStart, Bool.xor oldParity localParity, ?_, ?_⟩
        · have sparseOn := onCycle_sparse oldStartOn
          simpa [scaleSucc, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
            using sparseOn
        · exact Path.trans refinedPath translatedPath

end RedShadeGraphRootConnectivity
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
