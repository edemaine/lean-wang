/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditDefs

/-! Cached residual-cycle predecessor audit for parents 0 through 12. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCyclePredecessorAuditChunk00

open PairCoverSeamResidualCyclePredecessorAudit

set_option linter.style.nativeDecide false in
theorem complete : ∀ parent : Index,
    0 ≤ parent.val → parent.val < 13 → checkParent parent = true := by
  native_decide

end PairCoverSeamResidualCyclePredecessorAuditChunk00
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
