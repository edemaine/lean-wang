/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Tactic.FinCases
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseAuditChunk00
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseAuditChunk01
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseAuditChunk02
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseAuditChunk03
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseAuditChunk04
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseAuditChunk05
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseAuditChunk06
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseAuditChunk07

/-! Assemble the parallel state chunks for the cycle-only base audit. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace SparseFreeLineEvenExtraCycleBaseAuditChunks

open SparseFreeLineEvenExtraCycleBaseAudit

theorem complete (chunk : Fin 8) : ChunkComplete chunk := by
  fin_cases chunk
  · exact SparseFreeLineEvenExtraCycleBaseAuditChunk00.complete
  · exact SparseFreeLineEvenExtraCycleBaseAuditChunk01.complete
  · exact SparseFreeLineEvenExtraCycleBaseAuditChunk02.complete
  · exact SparseFreeLineEvenExtraCycleBaseAuditChunk03.complete
  · exact SparseFreeLineEvenExtraCycleBaseAuditChunk04.complete
  · exact SparseFreeLineEvenExtraCycleBaseAuditChunk05.complete
  · exact SparseFreeLineEvenExtraCycleBaseAuditChunk06.complete
  · exact SparseFreeLineEvenExtraCycleBaseAuditChunk07.complete

end SparseFreeLineEvenExtraCycleBaseAuditChunks
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
