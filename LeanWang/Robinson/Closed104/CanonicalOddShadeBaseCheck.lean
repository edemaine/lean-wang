/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalOddShadeBaseData

/-! Cached native certificate for odd base connectivity. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddShadeBase

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
set_option maxHeartbeats 2000000 in
-- The bounded flood checks all parity-labelled graph states in one base box.
theorem complete_eq_true : complete = true := by
  native_decide

end CanonicalOddShadeBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
