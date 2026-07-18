/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphRefinementAudit

/-! Native validation of the static connector forests. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphRefinement

set_option linter.style.nativeDecide false in
theorem complete_eq_true : complete = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem boundedComplete_eq_true : boundedComplete = true := by
  native_decide

end RedShadeGraphRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
