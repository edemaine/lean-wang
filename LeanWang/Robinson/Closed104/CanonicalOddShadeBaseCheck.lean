/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.CanonicalOddShadeBaseData

/-! Kernel certificate for odd base connectivity. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddShadeBase

set_option maxRecDepth 20000

set_option maxHeartbeats 2000000 in
-- Each selected witness is validated by the bounded path checker.
theorem complete_eq_true : complete = true := by
  decide +kernel

end CanonicalOddShadeBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
