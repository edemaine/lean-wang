/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104StableTiles

/-! Expensive finite certificate for the first substitution-derived depth. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem depthOneStableAndValid :
    horizontalStableBool 1 = true ∧
      verticalStableBool 1 = true ∧
      allDerivedChildRectanglesValidBool 1 = true := by
  native_decide

end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
