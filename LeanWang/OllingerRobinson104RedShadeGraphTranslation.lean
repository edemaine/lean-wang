/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraph
import LeanWang.OllingerRobinson104RedShadeGraphRefinementAudit
import LeanWang.OllingerRobinson104RedShadeGraphSearchSoundness
import LeanWang.OllingerRobinson104RefinementTranslation

/-!
Translation of finite red-shade graph certificates between refined blocks.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphTranslation

open RedCycles RedShadeGraph RedShadeGraphSearchSoundness
  RedShadeGraphRefinement RefinementTranslation Signals.FreeCellLocal

theorem link_congr_of_component_eq
    {firstGrid secondGrid : Nat → Nat → Index}
    {width height : Nat} {first second : Port} {parity : Bool}
    (componentsEq : ∀ x y, x < width → y < height →
      componentAt firstGrid x y = componentAt secondGrid x y)
    (link : Link firstGrid first second parity)
    (hfirst : PortInBounds first width height)
    (hsecond : PortInBounds second width height) :
    Link secondGrid first second parity := by
  induction link with
  | horizontalMatch x y => exact Link.horizontalMatch x y
  | verticalMatch x y => exact Link.verticalMatch x y
  | horizontal x y hpath =>
      apply Link.horizontal
      rw [← componentsEq x y hfirst.1 hfirst.2]
      exact hpath
  | vertical x y hpath =>
      apply Link.vertical
      rw [← componentsEq x y hfirst.1 hfirst.2]
      exact hpath
  | westNorth x y hwest hnorth =>
      apply Link.westNorth
      · rw [← componentsEq x y hfirst.1 hfirst.2]
        exact hwest
      · rw [← componentsEq x y hfirst.1 hfirst.2]
        exact hnorth
  | westSouth x y hwest hsouth =>
      apply Link.westSouth
      · rw [← componentsEq x y hfirst.1 hfirst.2]
        exact hwest
      · rw [← componentsEq x y hfirst.1 hfirst.2]
        exact hsouth
  | eastNorth x y heast hnorth =>
      apply Link.eastNorth
      · rw [← componentsEq x y hfirst.1 hfirst.2]
        exact heast
      · rw [← componentsEq x y hfirst.1 hfirst.2]
        exact hnorth
  | eastSouth x y heast hsouth =>
      apply Link.eastSouth
      · rw [← componentsEq x y hfirst.1 hfirst.2]
        exact heast
      · rw [← componentsEq x y hfirst.1 hfirst.2]
        exact hsouth
  | crossing x y hhorizontal hvertical =>
      apply Link.crossing
      · rw [← componentsEq x y hfirst.1 hfirst.2]
        exact hhorizontal
      · rw [← componentsEq x y hfirst.1 hfirst.2]
        exact hvertical
  | symm link ih => exact Link.symm (ih hsecond hfirst)

theorem BoundedPath.congr_of_component_eq
    {firstGrid secondGrid : Nat → Nat → Index}
    {width height : Nat} {first second : Port} {parity : Bool}
    (componentsEq : ∀ x y, x < width → y < height →
      componentAt firstGrid x y = componentAt secondGrid x y)
    (path : BoundedPath firstGrid width height first second parity) :
    BoundedPath secondGrid width height first second parity := by
  induction path with
  | refl port hport => exact BoundedPath.refl port hport
  | ofLink link hfirst hsecond =>
      exact BoundedPath.ofLink
        (link_congr_of_component_eq componentsEq link hfirst hsecond)
        hfirst hsecond
  | trans _ _ firstIH secondIH => exact BoundedPath.trans firstIH secondIH

def translatePort (port : Port) (offsetX offsetY : Nat) : Port :=
  ⟨offsetX + port.x, offsetY + port.y, port.side⟩

/-- Port liveness is invariant under the canonical refined-block translation. -/
theorem portPresent_translate
    (depth : Nat) (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (port : Port) :
    portPresent (iterateRefine depth (shiftGrid grid blockX blockY)) port =
      portPresent (iterateRefine depth grid)
        (translatePort port (2 ^ (depth + 1) * blockX)
          (2 ^ (depth + 1) * blockY)) := by
  rcases port with ⟨x, y, side⟩
  have hscale : 2 ∣ 2 ^ (depth + 1) := dvd_pow_self 2 (by omega)
  cases side <;> simp only [portPresent, translatePort] <;>
    rw [componentAt_iterateRefine_shift,
      quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]

theorem link_translate
    {depth : Nat} {grid : Nat → Nat → Index} {blockX blockY : Nat}
    {first second : Port} {parity : Bool}
    (link : Link (iterateRefine depth (shiftGrid grid blockX blockY))
      first second parity) :
    Link (iterateRefine depth grid)
      (translatePort first (2 ^ (depth + 1) * blockX)
        (2 ^ (depth + 1) * blockY))
      (translatePort second (2 ^ (depth + 1) * blockX)
        (2 ^ (depth + 1) * blockY)) parity := by
  let offsetX := 2 ^ (depth + 1) * blockX
  let offsetY := 2 ^ (depth + 1) * blockY
  have hscale : 2 ∣ 2 ^ (depth + 1) := dvd_pow_self 2 (by omega)
  induction link with
  | horizontalMatch x y =>
      simpa only [translatePort, offsetX, offsetY, Nat.add_assoc] using
        (Link.horizontalMatch (indexGrid := iterateRefine depth grid)
          (offsetX + x) (offsetY + y))
  | verticalMatch x y =>
      simpa only [translatePort, offsetX, offsetY, Nat.add_assoc] using
        (Link.verticalMatch (indexGrid := iterateRefine depth grid)
          (offsetX + x) (offsetY + y))
  | horizontal x y hpath =>
      apply Link.horizontal
      rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
      rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
      exact hpath
  | vertical x y hpath =>
      apply Link.vertical
      rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
      rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
      exact hpath
  | westNorth x y hwest hnorth =>
      apply Link.westNorth
      · rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
        rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
        exact hwest
      · rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
        rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
        exact hnorth
  | westSouth x y hwest hsouth =>
      apply Link.westSouth
      · rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
        rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
        exact hwest
      · rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
        rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
        exact hsouth
  | eastNorth x y heast hnorth =>
      apply Link.eastNorth
      · rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
        rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
        exact heast
      · rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
        rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
        exact hnorth
  | eastSouth x y heast hsouth =>
      apply Link.eastSouth
      · rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
        rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
        exact heast
      · rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
        rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
        exact hsouth
  | crossing x y hhorizontal hvertical =>
      apply Link.crossing
      · rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
        rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
        exact hhorizontal
      · rw [← componentAt_iterateRefine_shift depth grid blockX blockY x y]
        rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
        exact hvertical
  | symm link ih => exact Link.symm ih

theorem path_translate
    {depth : Nat} {grid : Nat → Nat → Index} {blockX blockY : Nat}
    {first second : Port} {parity : Bool}
    (path : Path (iterateRefine depth (shiftGrid grid blockX blockY))
      first second parity) :
    Path (iterateRefine depth grid)
      (translatePort first (2 ^ (depth + 1) * blockX)
        (2 ^ (depth + 1) * blockY))
      (translatePort second (2 ^ (depth + 1) * blockX)
        (2 ^ (depth + 1) * blockY)) parity := by
  induction path with
  | refl port => exact Path.refl _
  | ofLink link => exact Path.ofLink (link_translate link)
  | trans firstPath secondPath firstIH secondIH =>
      exact Path.trans firstIH secondIH

end RedShadeGraphTranslation
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
