/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseStep

/-!
# Coordinates for the recursive even-extra window

Anchoring the old exceptional line four index cells below its component row
makes the anchor scale exactly under two substitutions.  In these coordinates
the certified old line and the requested new line are both at local coordinate
`8`, before and after refinement respectively.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraWindowCoordinates

open BorderCoverageOffsets RedShadeGraph RedShadeGraphRefinement
  ShadedFreeLineRecurrence SparseFreeLineOffsets

set_option maxRecDepth 20000

def exceptionalCoordinate (depth : Nat) : Nat :=
  lineCoordinate .even (depth + 2)
    (mainChild (extraChild (pivot depth)))

def anchor (depth : Nat) : Nat := exceptionalCoordinate depth / 2 - 4

theorem exceptionalCoordinate_eq (depth : Nat) :
    exceptionalCoordinate depth = 64 * 4 ^ depth + 8 := by
  unfold exceptionalCoordinate
  rw [lineCoordinate_even]
  simp only [mainChild, extraChild, pivot]
  have hodd : (4 * (2 * 4 ^ depth) + 1) % 2 ≠ 0 := by omega
  rw [if_neg hodd]
  have hpow : 4 ^ (depth + 2) = 16 * 4 ^ depth := by
    rw [pow_add]
    norm_num
    omega
  rw [hpow]
  omega

theorem exceptionalCoordinate_even (depth : Nat) :
    exceptionalCoordinate depth % 2 = 0 := by
  rw [exceptionalCoordinate_eq]
  omega

theorem exceptionalCoordinate_succ (depth : Nat) :
    exceptionalCoordinate (depth + 1) =
      4 * exceptionalCoordinate depth - 24 := by
  rw [exceptionalCoordinate_eq, exceptionalCoordinate_eq, pow_succ]
  omega

theorem anchor_eq (depth : Nat) : anchor depth = 32 * 4 ^ depth := by
  rw [anchor, exceptionalCoordinate_eq]
  omega

theorem anchor_succ (depth : Nat) :
    anchor (depth + 1) = 4 * anchor depth := by
  rw [anchor_eq, anchor_eq, pow_succ]
  omega

/-- The old certified quarter-line is local coordinate `8` in its window. -/
theorem source_local (depth : Nat) :
    exceptionalCoordinate depth = 2 * anchor depth + 8 := by
  rw [exceptionalCoordinate_eq, anchor_eq]
  omega

/-- After two substitutions, the next target is local coordinate `8`. -/
theorem target_local (depth : Nat) :
    exceptionalCoordinate (depth + 1) = 8 * anchor depth + 8 := by
  rw [exceptionalCoordinate_eq, anchor_eq, pow_succ]
  omega

/-- Literal sparse refinement overshoots the next exceptional line by `24`. -/
theorem sparseCoordinate_exceptionalCoordinate (depth : Nat) :
    sparseCoordinate (exceptionalCoordinate depth) =
      exceptionalCoordinate (depth + 1) + 24 := by
  rw [exceptionalCoordinate_eq, exceptionalCoordinate_eq, pow_succ]
  simp [sparseCoordinate, macroOrigin, localCoordinate]
  omega

theorem sparsePort_exceptionalRow (depth x : Nat) (side : Side) :
    sparsePort ⟨x, exceptionalCoordinate depth, side⟩ =
      ⟨sparseCoordinate x, exceptionalCoordinate (depth + 1) + 24, side⟩ := by
  simp [sparsePort, sparseCoordinate_exceptionalCoordinate]

theorem sparsePort_exceptionalColumn (depth y : Nat) (side : Side) :
    sparsePort ⟨exceptionalCoordinate depth, y, side⟩ =
      ⟨exceptionalCoordinate (depth + 1) + 24, sparseCoordinate y, side⟩ := by
  simp [sparsePort, sparseCoordinate_exceptionalCoordinate]

end SparseFreeLineEvenExtraWindowCoordinates
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
