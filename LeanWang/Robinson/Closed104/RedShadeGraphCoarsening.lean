/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverage
import LeanWang.Robinson.Closed104.RedShadeGraphPathRefinement

/-!
# Semantic coarsening of red shades

A valid shade assignment after two Robinson substitutions induces a valid
assignment before those substitutions.  A coarse port reads the shade at its
side-sensitive refined image.  Refined graph paths then prove every coarse
local rule without reconstructing shade blocks.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphCoarsening

open RedCycles RedShadePaths RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphRefinement RedShadeGraphLocalCoverage
  RedShadeGraphTranslation Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem value_isSome_eq_portPresent
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid) (port : Port) :
    (value stateGrid port).isSome = portPresent grid port := by
  rcases port with ⟨x, y, side⟩
  have allowed := valid.allowed x y
  unfold RedShades.locallyAllowed at allowed
  change RedShades.allowedFor (componentAt grid x y) (quadrantAt x y)
    (stateGrid x y) = true at allowed
  simp only [RedShades.allowedFor, Bool.and_eq_true, decide_eq_true_eq,
    RedShades.optionPresent] at allowed
  cases side <;> simp only [value, portPresent] <;> aesop

set_option linter.style.nativeDecide false in
private theorem local_refinedPort_present (parent : Index) (x y : Fin 2)
    (side : Side) :
    portPresent (fineGrid parent) (refinedPort ⟨x, y, side⟩) =
      portPresent (coarseGrid parent) ⟨x, y, side⟩ := by
  revert parent x y side
  intro parent x y side
  cases side <;> revert parent x y <;> native_decide

private theorem sparseCoordinate_two_block (block offset : Nat)
    (hoffset : offset < 2) :
    sparseCoordinate (2 * block + offset) =
      8 * block + sparseCoordinate offset := by
  have cases : offset = 0 ∨ offset = 1 := by omega
  rcases cases with rfl | rfl
  · simp [sparseCoordinate, macroOrigin, localCoordinate]
  · simp [sparseCoordinate, macroOrigin, localCoordinate]
    omega

private theorem exitCoordinate_two_block (block offset : Nat)
    (hoffset : offset < 2) :
    exitCoordinate (2 * block + offset) =
      8 * block + exitCoordinate offset := by
  have cases : offset = 0 ∨ offset = 1 := by omega
  rcases cases with rfl | rfl
  · simp [exitCoordinate, sparseCoordinate, macroOrigin, localCoordinate]
  · simp [exitCoordinate, macroOrigin, localCoordinate]
    omega

private theorem refinedPort_two_block (port : Port) :
    refinedPort port =
      translatePort
        (refinedPort
          ⟨localCoordinate port.x, localCoordinate port.y, port.side⟩)
        (8 * (port.x / 2)) (8 * (port.y / 2)) := by
  rcases port with ⟨x, y, side⟩
  have hx : x = 2 * (x / 2) + localCoordinate x := by
    simp only [localCoordinate]
    omega
  have hy : y = 2 * (y / 2) + localCoordinate y := by
    simp only [localCoordinate]
    omega
  conv_lhs => rw [hx, hy]
  have hxLocal := localCoordinate_lt_two x
  have hyLocal := localCoordinate_lt_two y
  cases side
  · simp only [refinedPort, sparsePort, translatePort]
    rw [sparseCoordinate_two_block, sparseCoordinate_two_block] <;> assumption
  · simp only [refinedPort, translatePort]
    rw [exitCoordinate_two_block, sparseCoordinate_two_block] <;> assumption
  · simp only [refinedPort, sparsePort, translatePort]
    rw [sparseCoordinate_two_block, sparseCoordinate_two_block] <;> assumption
  · simp only [refinedPort, translatePort]
    rw [sparseCoordinate_two_block, exitCoordinate_two_block] <;> assumption

private theorem refinedPort_local_bounds (port : Port) (hx : port.x < 2)
    (hy : port.y < 2) :
    (refinedPort port).x < 8 ∧ (refinedPort port).y < 8 := by
  rcases port with ⟨x, y, side⟩
  change x < 2 at hx
  change y < 2 at hy
  have hxCases : x = 0 ∨ x = 1 := by omega
  have hyCases : y = 0 ∨ y = 1 := by omega
  rcases hxCases with rfl | rfl <;> rcases hyCases with rfl | rfl <;>
    cases side <;> decide

/-- Refinement preserves the incidence of every side-sensitive coarse port. -/
theorem refinedPort_present (grid : Nat → Nat → Index) (port : Port) :
    portPresent (iterateRefine 2 grid) (refinedPort port) =
      portPresent grid port := by
  let localPort : Port :=
    ⟨localCoordinate port.x, localCoordinate port.y, port.side⟩
  have localBounds : (refinedPort localPort).x < 8 ∧
      (refinedPort localPort).y < 8 :=
    refinedPort_local_bounds localPort
      (localCoordinate_lt_two _) (localCoordinate_lt_two _)
  rw [refinedPort_two_block port]
  rw [← portPresent_two_block grid (port.x / 2) (port.y / 2)
    (refinedPort localPort) localBounds.1 localBounds.2]
  let localX : Fin 2 := ⟨localCoordinate port.x, localCoordinate_lt_two _⟩
  let localY : Fin 2 := ⟨localCoordinate port.y, localCoordinate_lt_two _⟩
  change portPresent (fineGrid (grid (port.x / 2) (port.y / 2)))
      (refinedPort ⟨localX, localY, port.side⟩) = portPresent grid port
  rw [local_refinedPort_present]
  exact portPresent_coarseGrid_local grid port

/-- Port labels pulled back through two substitutions. -/
def labeling {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid) :
    ValidPortLabeling grid where
  label port := value stateGrid (refinedPort port)
  present port := by
    rw [value_isSome_eq_portPresent valid]
    exact refinedPort_present grid port
  related link := (link_refine link).sound valid

/-- The coarsened shade assignment. -/
def stateGrid {grid : Nat → Nat → Index}
    {fineStateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) fineStateGrid) :
    Nat → Nat → RedShades.State :=
  (labeling valid).stateGrid

@[simp] theorem value_stateGrid
    {grid : Nat → Nat → Index}
    {fineStateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) fineStateGrid)
    (port : Port) :
    value (stateGrid valid) port = value fineStateGrid (refinedPort port) := by
  rcases port with ⟨x, y, side⟩
  cases side <;> rfl

/-- Coarsening preserves all local shade rules and edge matches. -/
theorem valid {grid : Nat → Nat → Index}
    {fineStateGrid : Nat → Nat → RedShades.State}
    (fineValid : ValidShadeGrid (iterateRefine 2 grid) fineStateGrid) :
    ValidShadeGrid grid (stateGrid fineValid) :=
  ValidPortLabeling.validShadeGrid (labeling fineValid)

private theorem southwest_present {grid : Nat → Nat → Index}
    {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    portPresent grid ⟨quarterWest west, quarterSouth south, .east⟩ = true := by
  have corner := (RedShadeCycles.CycleOn.southwest_corner cycle).1
  simp [portPresent, RedShades.hasEast, corner]

private theorem southeast_present {grid : Nat → Nat → Index}
    {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    portPresent grid ⟨quarterEast east, quarterSouth south, .west⟩ = true := by
  have corner := (RedShadeCycles.CycleOn.southeast_corner cycle).1
  simp [portPresent, RedShades.hasWest, corner]

private theorem northeast_present {grid : Nat → Nat → Index}
    {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    portPresent grid ⟨quarterEast east, quarterNorth north, .west⟩ = true := by
  have corner := (RedShadeCycles.CycleOn.northeast_corner cycle).1
  simp [portPresent, RedShades.hasWest, corner]

private theorem northwest_present {grid : Nat → Nat → Index}
    {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    portPresent grid ⟨quarterWest west, quarterNorth north, .east⟩ = true := by
  have corner := (RedShadeCycles.CycleOn.northwest_corner cycle).1
  simp [portPresent, RedShades.hasEast, corner]

/-- A uniformly shaded refined cycle induces the same shade on its coarse
ancestor. -/
theorem cycleShade
    {grid : Nat → Nat → Index}
    {fineStateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade}
    (fineValid : ValidShadeGrid (iterateRefine 2 grid) fineStateGrid)
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (shaded : CycleShade fineStateGrid
      (4 * west) (4 * east) (4 * south) (4 * north) shade) :
    CycleShade (stateGrid fineValid) west east south north shade := by
  constructor
  · let port : Port := ⟨quarterWest west, quarterSouth south, .east⟩
    have path := livePortPath grid port (southwest_present cycle)
    have start : value fineStateGrid (sparsePort port) = some shade := by
      simpa [port, value, sparsePort] using shaded.southwest
    have relation : value fineStateGrid (sparsePort port) =
        value fineStateGrid (refinedPort port) := path.sound fineValid
    change value (stateGrid fineValid) port = some shade
    rw [value_stateGrid]
    exact relation.symm.trans start
  · let port : Port := ⟨quarterEast east, quarterSouth south, .west⟩
    have path := livePortPath grid port (southeast_present cycle)
    have start : value fineStateGrid (sparsePort port) = some shade := by
      simpa [port, value, sparsePort] using shaded.southeast
    have relation : value fineStateGrid (sparsePort port) =
        value fineStateGrid (refinedPort port) := path.sound fineValid
    change value (stateGrid fineValid) port = some shade
    rw [value_stateGrid]
    exact relation.symm.trans start
  · let port : Port := ⟨quarterEast east, quarterNorth north, .west⟩
    have path := livePortPath grid port (northeast_present cycle)
    have start : value fineStateGrid (sparsePort port) = some shade := by
      simpa [port, value, sparsePort] using shaded.northeast
    have relation : value fineStateGrid (sparsePort port) =
        value fineStateGrid (refinedPort port) := path.sound fineValid
    change value (stateGrid fineValid) port = some shade
    rw [value_stateGrid]
    exact relation.symm.trans start
  · let port : Port := ⟨quarterWest west, quarterNorth north, .east⟩
    have path := livePortPath grid port (northwest_present cycle)
    have start : value fineStateGrid (sparsePort port) = some shade := by
      simpa [port, value, sparsePort] using shaded.northwest
    have relation : value fineStateGrid (sparsePort port) =
        value fineStateGrid (refinedPort port) := path.sound fineValid
    change value (stateGrid fineValid) port = some shade
    rw [value_stateGrid]
    exact relation.symm.trans start

end RedShadeGraphCoarsening
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
