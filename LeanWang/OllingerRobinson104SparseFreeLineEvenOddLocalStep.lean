/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderCoverageOffsets

/-!
# The local even-phase odd-offset recurrence

The retained coordinate lemmas used by the even-phase odd-offset recurrence.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenOddLocalStep

open ShadedFreeLineRecurrence BorderCoverageOffsets

theorem coordinate_mod_four {depth offset : Nat} (hmod : offset % 4 = 3) :
    lineCoordinate .even (depth + 1) offset % 4 = 0 := by
  rw [lineCoordinate_even, pow_succ]
  omega

theorem coordinate_even {depth offset : Nat} (hmod : offset % 4 = 3) :
    lineCoordinate .even (depth + 1) offset % 2 = 0 := by
  have hfour := coordinate_mod_four (depth := depth) hmod
  omega

theorem coordinate_half_even {depth offset : Nat} (hmod : offset % 4 = 3) :
    (lineCoordinate .even (depth + 1) offset / 2) % 2 = 0 := by
  have hfour := coordinate_mod_four (depth := depth) hmod
  omega

end SparseFreeLineEvenOddLocalStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
