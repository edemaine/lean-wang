/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineLocalStates
import LeanWang.OllingerRobinson104SignalFreeCellEmbedding

/-!
# Transporting sparse free-line ancestors between translated macrocells

The finite state checks apply to a constant-parent `8 x 8` quarter block.  This
module transports their witnesses to the corresponding translated block in an
arbitrary iterated refinement, retaining the exact sparse global coordinate.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineLocalTransport

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearchSoundness
  RedShadeGraphTranslation RefinementTranslation Signals.FreeCellLocal
  Signals.FreeCellEmbedding SparseFreeLineLocalStates

set_option maxRecDepth 20000

theorem sparseCoordinate_two_block (block offset : Nat) (hoffset : offset < 2) :
    sparseCoordinate (2 * block + offset) = 8 * block + sparseCoordinate offset := by
  have cases : offset = 0 ∨ offset = 1 := by omega
  rcases cases with rfl | rfl
  · simp [sparseCoordinate, macroOrigin, localCoordinate]
  · have hdiv : (2 * block + 1) / 2 = block := by omega
    simp [sparseCoordinate, macroOrigin, localCoordinate, hdiv]

theorem componentAt_old_block (grid : Nat → Nat → Index)
    (level blockX blockY localX localY : Nat)
    (hx : localX < 2) (hy : localY < 2) :
    componentAt (iterateRefine level grid)
        (2 * blockX + localX) (2 * blockY + localY) =
      componentAt (coarseGrid (iterateRefine level grid blockX blockY))
        localX localY := by
  simp [componentAt, coarseGrid]
  congr <;> omega

theorem quadrantAt_old_block (blockX blockY localX localY : Nat)
    (hx : localX < 2) (hy : localY < 2) :
    quadrantAt (2 * blockX + localX) (2 * blockY + localY) =
      quadrantAt localX localY := by
  have hxCases : localX = 0 ∨ localX = 1 := by omega
  have hyCases : localY = 0 ∨ localY = 1 := by omega
  rcases hxCases with rfl | rfl <;> rcases hyCases with rfl | rfl <;>
    simp [quadrantAt]

/-- A bounded local path translates into the corresponding arbitrary macrocell. -/
theorem boundedPath_two_block
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {first target : Port} {parity : Bool}
    (path : BoundedPath (fineGrid (grid blockX blockY)) 8 8
      first target parity) :
    Path (iterateRefine 2 grid)
      (translatePort first (8 * blockX) (8 * blockY))
      (translatePort target (8 * blockX) (8 * blockY)) parity := by
  have componentsEq : ∀ x y, x < 8 → y < 8 →
      componentAt (fineGrid (grid blockX blockY)) x y =
        componentAt (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
    intro x y hx hy
    exact (componentAt_shift_eq_constant 2 grid blockX blockY x y hx hy).symm
  have shifted :=
    (BoundedPath.congr_of_component_eq componentsEq path).path
  simpa using path_translate (depth := 2) (grid := grid)
    (blockX := blockX) (blockY := blockY) shifted

/-- A bounded path on an arbitrary shifted neighborhood translates globally. -/
theorem boundedPath_shift
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {width height : Nat} {first target : Port} {parity : Bool}
    (path : BoundedPath (iterateRefine 2 (shiftGrid grid blockX blockY))
      width height first target parity) :
    Path (iterateRefine 2 grid)
      (translatePort first (8 * blockX) (8 * blockY))
      (translatePort target (8 * blockX) (8 * blockY)) parity := by
  simpa using path_translate (depth := 2) (grid := grid)
    (blockX := blockX) (blockY := blockY) path.path

theorem portPresent_shift
    (grid : Nat → Nat → Index) (blockX blockY : Nat) (port : Port) :
    portPresent (iterateRefine 2 (shiftGrid grid blockX blockY)) port =
      portPresent (iterateRefine 2 grid)
        (translatePort port (8 * blockX) (8 * blockY)) := by
  simpa using RedShadeGraphTranslation.portPresent_translate
    2 grid blockX blockY port

theorem portPresent_old_block
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (port : Port) (hx : port.x < 2) (hy : port.y < 2) :
    portPresent (coarseGrid (grid blockX blockY)) port =
      portPresent grid
        (translatePort port (2 * blockX) (2 * blockY)) := by
  rcases port with ⟨x, y, side⟩
  have hcomponent : componentAt (coarseGrid (grid blockX blockY)) x y =
      componentAt grid (2 * blockX + x) (2 * blockY + y) := by
    change componentAt (coarseGrid (grid blockX blockY)) x y =
      componentAt (iterateRefine 0 grid) (2 * blockX + x) (2 * blockY + y)
    exact (componentAt_old_block grid 0 blockX blockY x y hx hy).symm
  have hquadrant := quadrantAt_old_block blockX blockY x y hx hy
  cases side <;> simp only [portPresent, translatePort] <;>
    rw [hcomponent, hquadrant]

theorem portPresent_two_block
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (port : Port) (hx : port.x < 8) (hy : port.y < 8) :
    portPresent (fineGrid (grid blockX blockY)) port =
      portPresent (iterateRefine 2 grid)
        (translatePort port (8 * blockX) (8 * blockY)) := by
  rcases port with ⟨x, y, side⟩
  have hcomponent : componentAt (fineGrid (grid blockX blockY)) x y =
      componentAt (iterateRefine 2 grid)
        (8 * blockX + x) (8 * blockY + y) := by
    change componentAt
        (iterateRefine 2 (fun _ _ => iterateRefine 0 grid blockX blockY)) x y = _
    exact (componentAt_two_block grid 0 blockX blockY x y hx hy).symm
  have hquadrant := quadrantAt_block blockX blockY x y
  cases side <;> simp only [portPresent, translatePort] <;>
    rw [hcomponent, hquadrant]

/-- A checked local vertical ancestor becomes an old-grid sparse ancestor. -/
theorem verticalAncestor_two_block
    (grid : Nat → Nat → Index) (level blockX blockY : Nat)
    (sourceY targetY targetX : Nat)
    (hsourceY : sourceY < 2) (htargetY : targetY < 8)
    (htargetX : targetX < 8)
    (checked : verticalCheck sourceY targetY
      (iterateRefine level grid blockX blockY) = true)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine (level + 2) grid)
        (8 * blockX + targetX) (8 * blockY + targetY))
      (quadrantAt (8 * blockX + targetX) (8 * blockY + targetY)) ≠ none) :
    ∃ sourceX, sourceX < 2 ∧
      sparseCoordinate (2 * blockX + sourceX) = 8 * blockX + targetX ∧
      Signals.verticalInterior?
        (componentAt (iterateRefine level grid)
          (2 * blockX + sourceX) (2 * blockY + sourceY))
        (quadrantAt (2 * blockX + sourceX) (2 * blockY + sourceY)) ≠ none := by
  let parent := iterateRefine level grid blockX blockY
  have localInterior : Signals.verticalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY) ≠ none := by
    rw [componentAt_two_block grid level blockX blockY targetX targetY
      htargetX htargetY] at interior
    rw [quadrantAt_block] at interior
    change Signals.verticalInterior?
      (componentAt (iterateRefine 2 (fun _ _ => parent)) targetX targetY)
      (quadrantAt targetX targetY) ≠ none
    simpa only [parent] using interior
  rcases verticalCheck_sound checked targetX htargetX localInterior with
    ⟨sourceX, hsourceX, coordinate, sourceInterior⟩
  refine ⟨sourceX, hsourceX, ?_, ?_⟩
  · rw [sparseCoordinate_two_block blockX sourceX hsourceX, coordinate]
  · rw [componentAt_old_block grid level blockX blockY sourceX sourceY
      hsourceX hsourceY]
    rw [quadrantAt_old_block blockX blockY sourceX sourceY
      hsourceX hsourceY]
    exact sourceInterior

/-- A checked local horizontal ancestor becomes an old-grid sparse ancestor. -/
theorem horizontalAncestor_two_block
    (grid : Nat → Nat → Index) (level blockX blockY : Nat)
    (sourceX targetX targetY : Nat)
    (hsourceX : sourceX < 2) (htargetX : targetX < 8)
    (htargetY : targetY < 8)
    (checked : horizontalCheck sourceX targetX
      (iterateRefine level grid blockX blockY) = true)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine (level + 2) grid)
        (8 * blockX + targetX) (8 * blockY + targetY))
      (quadrantAt (8 * blockX + targetX) (8 * blockY + targetY)) ≠ none) :
    ∃ sourceY, sourceY < 2 ∧
      sparseCoordinate (2 * blockY + sourceY) = 8 * blockY + targetY ∧
      Signals.horizontalInterior?
        (componentAt (iterateRefine level grid)
          (2 * blockX + sourceX) (2 * blockY + sourceY))
        (quadrantAt (2 * blockX + sourceX) (2 * blockY + sourceY)) ≠ none := by
  let parent := iterateRefine level grid blockX blockY
  have localInterior : Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY) ≠ none := by
    rw [componentAt_two_block grid level blockX blockY targetX targetY
      htargetX htargetY] at interior
    rw [quadrantAt_block] at interior
    change Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (fun _ _ => parent)) targetX targetY)
      (quadrantAt targetX targetY) ≠ none
    simpa only [parent] using interior
  rcases horizontalCheck_sound checked targetY htargetY localInterior with
    ⟨sourceY, hsourceY, coordinate, sourceInterior⟩
  refine ⟨sourceY, hsourceY, ?_, ?_⟩
  · rw [sparseCoordinate_two_block blockY sourceY hsourceY, coordinate]
  · rw [componentAt_old_block grid level blockX blockY sourceX sourceY
      hsourceX hsourceY]
    rw [quadrantAt_old_block blockX blockY sourceX sourceY
      hsourceX hsourceY]
    exact sourceInterior

end SparseFreeLineLocalTransport
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
