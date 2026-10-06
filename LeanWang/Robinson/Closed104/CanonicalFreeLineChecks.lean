/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.CanonicalFreeLineData

/-! Kernel certificate for the canonical free-line local audit. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalFreeLine

set_option maxRecDepth 20000

theorem evenLocalComplete_eq_true : evenLocalComplete = true := by
  decide +kernel

theorem evenBaseComplete_eq_true : evenBaseComplete = true := by
  decide +kernel

end CanonicalFreeLine
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
