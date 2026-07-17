/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathExactPredecessorAuditDefs

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathExactPredecessorAuditChunk00

open PairCoverSeamResidualDirectPathExactPredecessorAudit

set_option linter.style.nativeDecide false in
theorem complete : ∀ parent : Index,
    0 ≤ parent.val → parent.val < 13 → checkParent parent = true := by
  native_decide

end PairCoverSeamResidualDirectPathExactPredecessorAuditChunk00
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
