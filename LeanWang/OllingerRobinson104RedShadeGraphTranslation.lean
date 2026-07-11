/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraph
import LeanWang.OllingerRobinson104RefinementTranslation

/-!
Translation of finite red-shade graph certificates between refined blocks.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphTranslation

open RedCycles RedShadeGraph RefinementTranslation Signals.FreeCellLocal

def translatePort (port : Port) (offsetX offsetY : Nat) : Port :=
  ⟨offsetX + port.x, offsetY + port.y, port.side⟩

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
