/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAuditDefs

/-! Cached forward family-target lift audit for parents 68 through 79. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk05

open PairCoverSeamResidualDirectPathFamilyTargetLiftAudit

set_option linter.style.nativeDecide false in
theorem complete : forall parent : Index,
    68 <= parent.val -> parent.val < 80 -> checkParent parent = true := by
  native_decide

end PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk05
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
