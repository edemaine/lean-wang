/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SignalFreeCellLocal

/-!
Repeat the finite free-cell gadget through arbitrary refinement depth.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals
namespace FreeCellEmbedding

open RedCycles PlaneRedBoards FreeCellLocal

set_option maxRecDepth 20000

/-- A depth-two refined block depends only on its one coarse parent tile. -/
theorem iterateRefine_two_block (grid : Nat → Nat → Index)
    (level blockX blockY localX localY : Nat)
    (hx : localX < 4) (hy : localY < 4) :
    iterateRefine (level + 2) grid
        (4 * blockX + localX) (4 * blockY + localY) =
      iterateRefine 2
        (fun _ _ => iterateRefine level grid blockX blockY) localX localY := by
  have hlevel : level + 2 = 2 + level := by omega
  rw [hlevel, ← iterateRefine_add]
  rw [iterateRefine_two_apply, iterateRefine_two_apply]
  have hxDiv : ((4 * blockX + localX) / 2) / 2 = blockX := by omega
  have hyDiv : ((4 * blockY + localY) / 2) / 2 = blockY := by omega
  have hxOuter : parityOffset (4 * blockX + localX) = parityOffset localX := by
    apply Fin.ext
    simp [parityOffset]
    omega
  have hyOuter : parityOffset (4 * blockY + localY) = parityOffset localY := by
    apply Fin.ext
    simp [parityOffset]
    omega
  have hxInner : parityOffset ((4 * blockX + localX) / 2) =
      parityOffset (localX / 2) := by
    apply Fin.ext
    simp [parityOffset]
    omega
  have hyInner : parityOffset ((4 * blockY + localY) / 2) =
      parityOffset (localY / 2) := by
    apply Fin.ext
    simp [parityOffset]
    omega
  rw [hxDiv, hyDiv, hxOuter, hyOuter, hxInner, hyInner]

theorem quadrantAt_block (blockX blockY localX localY : Nat) :
    quadrantAt (8 * blockX + localX) (8 * blockY + localY) =
      quadrantAt localX localY := by
  have hx : (8 * blockX + localX) % 2 = localX % 2 := by omega
  have hy : (8 * blockY + localY) % 2 = localY % 2 := by omega
  simp [quadrantAt, hx, hy]

/-- Quarter components in a repeated depth-two block are translated copies. -/
theorem componentAt_two_block (grid : Nat → Nat → Index)
    (level blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    componentAt (iterateRefine (level + 2) grid)
        (8 * blockX + localX) (8 * blockY + localY) =
      componentAt
        (iterateRefine 2
          (fun _ _ => iterateRefine level grid blockX blockY))
        localX localY := by
  have hxDiv : (8 * blockX + localX) / 2 = 4 * blockX + localX / 2 := by omega
  have hyDiv : (8 * blockY + localY) / 2 = 4 * blockY + localY / 2 := by omega
  rw [componentAt, componentAt, hxDiv, hyDiv]
  rw [iterateRefine_two_block grid level blockX blockY
    (localX / 2) (localY / 2) (by omega) (by omega)]


end FreeCellEmbedding
end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
