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

theorem verticalInteriorAt_two_block (grid : Nat → Nat → Index)
    (level blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    verticalInteriorAt (iterateRefine (level + 2) grid)
        (8 * blockX + localX) (8 * blockY + localY) =
      verticalInteriorAt
        (iterateRefine 2
          (fun _ _ => iterateRefine level grid blockX blockY))
        localX localY := by
  unfold verticalInteriorAt
  rw [componentAt_two_block grid level blockX blockY localX localY hx hy,
    quadrantAt_block]

theorem horizontalInteriorAt_two_block (grid : Nat → Nat → Index)
    (level blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    horizontalInteriorAt (iterateRefine (level + 2) grid)
        (8 * blockX + localX) (8 * blockY + localY) =
      horizontalInteriorAt
        (iterateRefine 2
          (fun _ _ => iterateRefine level grid blockX blockY))
        localX localY := by
  unfold horizontalInteriorAt
  rw [componentAt_two_block grid level blockX blockY localX localY hx hy,
    quadrantAt_block]

def freeCount (depth : Nat) : Nat := 2 ^ (depth - 3)

def freeBlock (depth index : Nat) : Nat :=
  2 ^ (depth - 4) + index

def freeCoordinate (depth index : Nat) : Nat :=
  4 + 2 ^ (depth - 1) + 8 * index + index % 2

theorem freeCoordinate_eq (depth index : Nat) (hdepth : 5 ≤ depth) :
    freeCoordinate depth index =
      8 * freeBlock depth index + 4 + index % 2 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hdepth
  have hsubOne : 5 + extra - 1 = extra + 4 := by omega
  have hsubFour : 5 + extra - 4 = extra + 1 := by omega
  simp only [freeCoordinate, freeBlock, hsubOne, hsubFour]
  rw [pow_add, pow_add]
  norm_num
  omega

theorem freeBlock_parity (depth index : Nat) (hdepth : 5 ≤ depth) :
    parityOffset (freeBlock depth index) = parityOffset index := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hdepth
  have hsubFour : 5 + extra - 4 = extra + 1 := by omega
  apply Fin.ext
  simp [freeBlock, parityOffset, hsubFour, pow_succ, Nat.add_mod]

theorem freeCoordinate_lt_quarterSize {depth index : Nat}
    (hdepth : 5 ≤ depth) (hindex : index < freeCount depth) :
    freeCoordinate depth index < 2 ^ (depth + 1) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hdepth
  have hsubOne : 5 + extra - 1 = extra + 4 := by omega
  have hsubThree : 5 + extra - 3 = extra + 2 := by omega
  have haddOne : 5 + extra + 1 = extra + 6 := by omega
  have hcount : 2 ^ (extra + 2) = 4 * 2 ^ extra := by
    simp [pow_add, mul_comm]
  have hmiddle : 2 ^ (extra + 4) = 16 * 2 ^ extra := by
    simp [pow_add, mul_comm]
  have hsize : 2 ^ (extra + 6) = 64 * 2 ^ extra := by
    simp [pow_add, mul_comm]
  simp only [freeCoordinate, freeCount, hsubOne, hsubThree, haddOne,
    hcount, hmiddle, hsize] at hindex ⊢
  have hmod : index % 2 < 2 := Nat.mod_lt _ (by decide : 0 < 2)
  have hpow : 0 < 2 ^ extra := pow_pos (by decide) _
  omega

/-- The local parent of a selected block is a child with the selected parity. -/
theorem exists_freeBlock_parent (grid : Nat → Nat → Index)
    {depth i j : Nat} (hdepth : 5 ≤ depth) :
    ∃ parent : Index,
      iterateRefine (depth - 2) grid (freeBlock depth i) (freeBlock depth j) =
        childBlock parent (parityOffset i) (parityOffset j) := by
  let blockX := freeBlock depth i
  let blockY := freeBlock depth j
  let parent := iterateRefine (depth - 3) grid (blockX / 2) (blockY / 2)
  refine ⟨parent, ?_⟩
  have hlevel : depth - 2 = (depth - 3) + 1 := by omega
  rw [hlevel]
  change childBlock parent (parityOffset blockX) (parityOffset blockY) = _
  rw [freeBlock_parity depth i hdepth,
    freeBlock_parity depth j hdepth]

/-- Named global copy of the finite free-cell gadget. -/
structure Geometry (grid : Nat → Nat → Index)
    (depth i j : Nat) : Prop where
  westBoundary :
    verticalInteriorAt (iterateRefine depth grid)
      (8 * freeBlock depth i + 3) (freeCoordinate depth j) = some .east
  eastBoundary :
    verticalInteriorAt (iterateRefine depth grid)
      (8 * freeBlock depth i + 6) (freeCoordinate depth j) = some .west
  verticalClear4 :
    verticalInteriorAt (iterateRefine depth grid)
      (8 * freeBlock depth i + 4) (freeCoordinate depth j) = none
  verticalClear5 :
    verticalInteriorAt (iterateRefine depth grid)
      (8 * freeBlock depth i + 5) (freeCoordinate depth j) = none
  southBoundary :
    horizontalInteriorAt (iterateRefine depth grid)
      (freeCoordinate depth i) (8 * freeBlock depth j + 3) = some .north
  northBoundary :
    horizontalInteriorAt (iterateRefine depth grid)
      (freeCoordinate depth i) (8 * freeBlock depth j + 6) = some .south
  horizontalClear4 :
    horizontalInteriorAt (iterateRefine depth grid)
      (freeCoordinate depth i) (8 * freeBlock depth j + 4) = none
  horizontalClear5 :
    horizontalInteriorAt (iterateRefine depth grid)
      (freeCoordinate depth i) (8 * freeBlock depth j + 5) = none

/-- Every selected coordinate is a translated copy of the finite gadget. -/
theorem geometry (grid : Nat → Nat → Index)
    {depth i j : Nat} (hdepth : 5 ≤ depth) : Geometry grid depth i j := by
  rcases exists_freeBlock_parent grid (i := i) (j := j) hdepth with
    ⟨parent, hparent⟩
  let ix := parityOffset i
  let iy := parityOffset j
  have hlocal := FreeCellLocal.geometry parent ix iy
  have hdepthEq : depth = (depth - 2) + 2 := by omega
  have hcoordX := freeCoordinate_eq depth i hdepth
  have hcoordY := freeCoordinate_eq depth j hdepth
  have localGrid_eq :
      iterateRefine 2
          (fun _ _ => iterateRefine (depth - 2) grid
            (freeBlock depth i) (freeBlock depth j)) =
        localGrid parent ix iy := by
    rw [hparent]
    rfl
  have hvertical (localX localY : Nat) (hx : localX < 8) (hy : localY < 8) :
      verticalInteriorAt (iterateRefine depth grid)
          (8 * freeBlock depth i + localX)
          (8 * freeBlock depth j + localY) =
        verticalInteriorAt
          (iterateRefine 2
            (fun _ _ => iterateRefine (depth - 2) grid
              (freeBlock depth i) (freeBlock depth j)))
          localX localY := by
    simpa only [← hdepthEq] using
      verticalInteriorAt_two_block grid (depth - 2)
        (freeBlock depth i) (freeBlock depth j) localX localY hx hy
  have hhorizontal (localX localY : Nat) (hx : localX < 8) (hy : localY < 8) :
      horizontalInteriorAt (iterateRefine depth grid)
          (8 * freeBlock depth i + localX)
          (8 * freeBlock depth j + localY) =
        horizontalInteriorAt
          (iterateRefine 2
            (fun _ _ => iterateRefine (depth - 2) grid
              (freeBlock depth i) (freeBlock depth j)))
          localX localY := by
    simpa only [← hdepthEq] using
      horizontalInteriorAt_two_block grid (depth - 2)
        (freeBlock depth i) (freeBlock depth j) localX localY hx hy
  refine {
    westBoundary := ?_
    eastBoundary := ?_
    verticalClear4 := ?_
    verticalClear5 := ?_
    southBoundary := ?_
    northBoundary := ?_
    horizontalClear4 := ?_
    horizontalClear5 := ?_
  }
  · rw [hcoordY]
    simp only [Nat.add_assoc]
    rw [hvertical 3 (4 + j % 2)
      (by omega) (by have := Nat.mod_lt j (by decide : 0 < 2); omega)]
    rw [localGrid_eq]
    simpa [iy, parityOffset] using hlocal.westBoundary
  · rw [hcoordY]
    simp only [Nat.add_assoc]
    rw [hvertical 6 (4 + j % 2)
      (by omega) (by have := Nat.mod_lt j (by decide : 0 < 2); omega)]
    rw [localGrid_eq]
    simpa [iy, parityOffset] using hlocal.eastBoundary
  · rw [hcoordY]
    simp only [Nat.add_assoc]
    rw [hvertical 4 (4 + j % 2)
      (by omega) (by have := Nat.mod_lt j (by decide : 0 < 2); omega)]
    rw [localGrid_eq]
    simpa [iy, parityOffset] using hlocal.verticalClear4
  · rw [hcoordY]
    simp only [Nat.add_assoc]
    rw [hvertical 5 (4 + j % 2)
      (by omega) (by have := Nat.mod_lt j (by decide : 0 < 2); omega)]
    rw [localGrid_eq]
    simpa [iy, parityOffset] using hlocal.verticalClear5
  · rw [hcoordX]
    simp only [Nat.add_assoc]
    rw [hhorizontal (4 + i % 2) 3
      (by have := Nat.mod_lt i (by decide : 0 < 2); omega) (by omega)]
    rw [localGrid_eq]
    simpa [ix, parityOffset] using hlocal.southBoundary
  · rw [hcoordX]
    simp only [Nat.add_assoc]
    rw [hhorizontal (4 + i % 2) 6
      (by have := Nat.mod_lt i (by decide : 0 < 2); omega) (by omega)]
    rw [localGrid_eq]
    simpa [ix, parityOffset] using hlocal.northBoundary
  · rw [hcoordX]
    simp only [Nat.add_assoc]
    rw [hhorizontal (4 + i % 2) 4
      (by have := Nat.mod_lt i (by decide : 0 < 2); omega) (by omega)]
    rw [localGrid_eq]
    simpa [ix, parityOffset] using hlocal.horizontalClear4
  · rw [hcoordX]
    simp only [Nat.add_assoc]
    rw [hhorizontal (4 + i % 2) 5
      (by have := Nat.mod_lt i (by decide : 0 < 2); omega) (by omega)]
    rw [localGrid_eq]
    simpa [ix, parityOffset] using hlocal.horizontalClear5

end FreeCellEmbedding
end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
