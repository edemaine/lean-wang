/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.SparseFreeLineOddExtraBaseAuditCheck

/-! Cheap finite source-bound checks for the odd-extra base audit. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineOddExtraBaseAudit

open RedShadeGraphRefinement RedShadeGraphSearchSoundness

def startsBounded (parent : Index) : Bool :=
  (starts parent).all fun start =>
    decide (start.port.x < 33) && decide (start.port.y < 33)

def candidatesSparseLower (parent : Index) : Bool :=
  (candidates parent).all fun candidate =>
    decide (16 ≤ (sparsePort candidate.port).x) &&
      decide (16 ≤ (sparsePort candidate.port).y)

set_option linter.style.nativeDecide false in
theorem startsBounded_complete : ∀ parent, startsBounded parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem candidatesSparseLower_complete :
    ∀ parent, candidatesSparseLower parent = true := by
  native_decide

end SparseFreeLineOddExtraBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
