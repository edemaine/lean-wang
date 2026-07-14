/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Tactic.FinCases
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAuditChunk00
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAuditChunk01
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAuditChunk02
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAuditChunk03
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAuditChunk04
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAuditChunk05
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAuditChunk06
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAuditChunk07

/-! Assemble the parallel state chunks for the even-extra base audit. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace SparseFreeLineEvenExtraBaseAuditChunks

open SparseFreeLineEvenExtraBaseAudit

theorem complete (chunk : Fin 8) : ChunkComplete chunk := by
  fin_cases chunk
  · exact SparseFreeLineEvenExtraBaseAuditChunk00.complete
  · exact SparseFreeLineEvenExtraBaseAuditChunk01.complete
  · exact SparseFreeLineEvenExtraBaseAuditChunk02.complete
  · exact SparseFreeLineEvenExtraBaseAuditChunk03.complete
  · exact SparseFreeLineEvenExtraBaseAuditChunk04.complete
  · exact SparseFreeLineEvenExtraBaseAuditChunk05.complete
  · exact SparseFreeLineEvenExtraBaseAuditChunk06.complete
  · exact SparseFreeLineEvenExtraBaseAuditChunk07.complete

end SparseFreeLineEvenExtraBaseAuditChunks
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
