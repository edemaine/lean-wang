/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SignalFreeCellLocal

/-!
Translation equivariance of iterated Robinson refinement.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RefinementTranslation

open RedCycles Signals.FreeCellLocal

set_option maxRecDepth 20000

def shiftGrid (grid : Nat → Nat → Index) (blockX blockY : Nat) :
    Nat → Nat → Index :=
  fun x y => grid (blockX + x) (blockY + y)

theorem iterateRefine_shift : ∀ (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat),
    iterateRefine depth (shiftGrid grid blockX blockY) x y =
      iterateRefine depth grid
        (2 ^ depth * blockX + x) (2 ^ depth * blockY + y) := by
  intro depth
  induction depth with
  | zero =>
      intro grid blockX blockY x y
      simp [iterateRefine, shiftGrid]
  | succ depth ih =>
      intro grid blockX blockY x y
      change childBlock
          (iterateRefine depth (shiftGrid grid blockX blockY)
            (x / 2) (y / 2))
          (parityOffset x) (parityOffset y) =
        childBlock
          (iterateRefine depth grid
            ((2 ^ (depth + 1) * blockX + x) / 2)
            ((2 ^ (depth + 1) * blockY + y) / 2))
          (parityOffset (2 ^ (depth + 1) * blockX + x))
          (parityOffset (2 ^ (depth + 1) * blockY + y))
      rw [ih]
      have hxDiv : (2 ^ (depth + 1) * blockX + x) / 2 =
          2 ^ depth * blockX + x / 2 := by
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
          (Nat.mul_add_div (m := 2) (by decide) (2 ^ depth * blockX) x)
      have hyDiv : (2 ^ (depth + 1) * blockY + y) / 2 =
          2 ^ depth * blockY + y / 2 := by
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
          (Nat.mul_add_div (m := 2) (by decide) (2 ^ depth * blockY) y)
      have hxParity : parityOffset (2 ^ (depth + 1) * blockX + x) =
          parityOffset x := by
        apply Fin.ext
        simpa [parityOffset, pow_succ, mul_assoc, mul_comm, mul_left_comm] using
          (Nat.mul_add_mod 2 (2 ^ depth * blockX) x)
      have hyParity : parityOffset (2 ^ (depth + 1) * blockY + y) =
          parityOffset y := by
        apply Fin.ext
        simpa [parityOffset, pow_succ, mul_assoc, mul_comm, mul_left_comm] using
          (Nat.mul_add_mod 2 (2 ^ depth * blockY) y)
      rw [hxDiv, hyDiv, hxParity, hyParity]

theorem quadrantAt_shift (scale blockX blockY quarterX quarterY : Nat)
    (hscale : 2 ∣ scale) :
    quadrantAt (scale * blockX + quarterX)
        (scale * blockY + quarterY) =
      quadrantAt quarterX quarterY := by
  rcases hscale with ⟨half, rfl⟩
  have hx : (2 * half * blockX + quarterX) % 2 = quarterX % 2 := by
    simp [mul_assoc]
  have hy : (2 * half * blockY + quarterY) % 2 = quarterY % 2 := by
    simp [mul_assoc]
  simp [quadrantAt, hx, hy]

theorem componentAt_iterateRefine_shift (depth : Nat)
    (grid : Nat → Nat → Index) (blockX blockY quarterX quarterY : Nat) :
    componentAt (iterateRefine depth (shiftGrid grid blockX blockY))
        quarterX quarterY =
      componentAt (iterateRefine depth grid)
        (2 ^ (depth + 1) * blockX + quarterX)
        (2 ^ (depth + 1) * blockY + quarterY) := by
  unfold componentAt
  have hxDiv : (2 ^ (depth + 1) * blockX + quarterX) / 2 =
      2 ^ depth * blockX + quarterX / 2 := by
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      (Nat.mul_add_div (m := 2) (by decide)
        (2 ^ depth * blockX) quarterX)
  have hyDiv : (2 ^ (depth + 1) * blockY + quarterY) / 2 =
      2 ^ depth * blockY + quarterY / 2 := by
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      (Nat.mul_add_div (m := 2) (by decide)
        (2 ^ depth * blockY) quarterY)
  rw [hxDiv, hyDiv, iterateRefine_shift]

theorem verticalInterior_iterateRefine_shift (depth : Nat)
    (grid : Nat → Nat → Index) (blockX blockY quarterX quarterY : Nat) :
    Signals.verticalInterior?
        (componentAt (iterateRefine depth (shiftGrid grid blockX blockY))
          quarterX quarterY)
        (quadrantAt quarterX quarterY) =
      Signals.verticalInterior?
        (componentAt (iterateRefine depth grid)
          (2 ^ (depth + 1) * blockX + quarterX)
          (2 ^ (depth + 1) * blockY + quarterY))
        (quadrantAt (2 ^ (depth + 1) * blockX + quarterX)
          (2 ^ (depth + 1) * blockY + quarterY)) := by
  rw [componentAt_iterateRefine_shift]
  rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY quarterX quarterY
    (by exact dvd_pow_self 2 (by omega))]

theorem horizontalInterior_iterateRefine_shift (depth : Nat)
    (grid : Nat → Nat → Index) (blockX blockY quarterX quarterY : Nat) :
    Signals.horizontalInterior?
        (componentAt (iterateRefine depth (shiftGrid grid blockX blockY))
          quarterX quarterY)
        (quadrantAt quarterX quarterY) =
      Signals.horizontalInterior?
        (componentAt (iterateRefine depth grid)
          (2 ^ (depth + 1) * blockX + quarterX)
          (2 ^ (depth + 1) * blockY + quarterY))
        (quadrantAt (2 ^ (depth + 1) * blockX + quarterX)
          (2 ^ (depth + 1) * blockY + quarterY)) := by
  rw [componentAt_iterateRefine_shift]
  rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY quarterX quarterY
    (by exact dvd_pow_self 2 (by omega))]

end RefinementTranslation
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
