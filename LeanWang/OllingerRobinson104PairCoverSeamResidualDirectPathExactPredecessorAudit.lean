/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorAuditChunk00
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorAuditChunk01
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorAuditChunk02
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorAuditChunk03
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorAuditChunk04
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorAuditChunk05
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorAuditChunk06
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorAuditChunk07

/-! Assemble the cached exact predecessor audit for all 104 closed tiles. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathExactPredecessorAudit

theorem complete (parent : Index) : checkParent parent = true := by
  by_cases h13 : parent.val < 13
  · exact PairCoverSeamResidualDirectPathExactPredecessorAuditChunk00.complete
      parent (by omega) h13
  by_cases h26 : parent.val < 26
  · exact PairCoverSeamResidualDirectPathExactPredecessorAuditChunk01.complete
      parent (by omega) h26
  by_cases h39 : parent.val < 39
  · exact PairCoverSeamResidualDirectPathExactPredecessorAuditChunk02.complete
      parent (by omega) h39
  by_cases h52 : parent.val < 52
  · exact PairCoverSeamResidualDirectPathExactPredecessorAuditChunk03.complete
      parent (by omega) h52
  by_cases h65 : parent.val < 65
  · exact PairCoverSeamResidualDirectPathExactPredecessorAuditChunk04.complete
      parent (by omega) h65
  by_cases h78 : parent.val < 78
  · exact PairCoverSeamResidualDirectPathExactPredecessorAuditChunk05.complete
      parent (by omega) h78
  by_cases h91 : parent.val < 91
  · exact PairCoverSeamResidualDirectPathExactPredecessorAuditChunk06.complete
      parent (by omega) h91
  exact PairCoverSeamResidualDirectPathExactPredecessorAuditChunk07.complete
    parent (by omega) parent.isLt

end PairCoverSeamResidualDirectPathExactPredecessorAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
