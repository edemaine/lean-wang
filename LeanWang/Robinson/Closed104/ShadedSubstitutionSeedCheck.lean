/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSubstitutionData

/-! # Seed check for the finite-state red-shade substitution -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSubstitution

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
theorem seed_mem_reachable : encodeNode false 0 ∈ reachable := by
  native_decide

end ShadedSubstitution
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
