/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverageData

/-! Native validation of the static local red-graph forests. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphLocalCoverage

set_option linter.style.nativeDecide false in
theorem allParentsCovered_eq_true : allParentsCovered = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem baseCovered_eq_true : baseCovered = true := by
  native_decide

end RedShadeGraphLocalCoverage
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
