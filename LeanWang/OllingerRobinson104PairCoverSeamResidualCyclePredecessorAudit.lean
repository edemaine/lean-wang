/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditChunk00
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditChunk01
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditChunk02
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditChunk03
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditChunk04
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditChunk05
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditChunk06
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditChunk07

/-! Assemble the cached finite predecessor audit for all 104 closed tiles. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCyclePredecessorAudit

theorem complete (parent : Index) : checkParent parent = true := by
  by_cases h13 : parent.val < 13
  · exact PairCoverSeamResidualCyclePredecessorAuditChunk00.complete parent
      (by omega) h13
  by_cases h26 : parent.val < 26
  · exact PairCoverSeamResidualCyclePredecessorAuditChunk01.complete parent
      (by omega) h26
  by_cases h39 : parent.val < 39
  · exact PairCoverSeamResidualCyclePredecessorAuditChunk02.complete parent
      (by omega) h39
  by_cases h52 : parent.val < 52
  · exact PairCoverSeamResidualCyclePredecessorAuditChunk03.complete parent
      (by omega) h52
  by_cases h65 : parent.val < 65
  · exact PairCoverSeamResidualCyclePredecessorAuditChunk04.complete parent
      (by omega) h65
  by_cases h78 : parent.val < 78
  · exact PairCoverSeamResidualCyclePredecessorAuditChunk05.complete parent
      (by omega) h78
  by_cases h91 : parent.val < 91
  · exact PairCoverSeamResidualCyclePredecessorAuditChunk06.complete parent
      (by omega) h91
  exact PairCoverSeamResidualCyclePredecessorAuditChunk07.complete parent
    (by omega) parent.isLt

end PairCoverSeamResidualCyclePredecessorAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
