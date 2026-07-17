/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedFreeLineRecurrence
import LeanWang.Robinson.Closed104.SparseFreeLineOffsets

/-!
# Coordinates for the recursive even-extra window

Closed forms for the exceptional line and its sparse predecessor.
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

/-- The exceptional target is the sparse copy of the retained extra-pivot line. -/
theorem exceptionalCoordinate_as_sparseSource (depth : Nat) :
    exceptionalCoordinate depth = sparseCoordinate
      (lineCoordinate .even (depth + 1) (extraChild (pivot depth))) := by
  have hsource : lineCoordinate .even (depth + 1)
      (extraChild (pivot depth)) = 16 * 4 ^ depth + 2 := by
    rw [lineCoordinate_even]
    simp [extraChild, pivot, pow_succ]
    omega
  rw [exceptionalCoordinate_eq, hsource]
  simp [sparseCoordinate, macroOrigin, localCoordinate]
  omega

end SparseFreeLineEvenExtraWindowCoordinates
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
