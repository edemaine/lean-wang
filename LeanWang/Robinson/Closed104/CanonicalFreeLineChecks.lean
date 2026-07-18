/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalFreeLineData

/-! Cached native certificate for the canonical free-line local audit. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalFreeLine

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
theorem evenLocalComplete_eq_true : evenLocalComplete = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem evenBaseComplete_eq_true : evenBaseComplete = true := by
  native_decide

end CanonicalFreeLine
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
