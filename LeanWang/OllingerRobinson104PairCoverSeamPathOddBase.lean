/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Tactic.FinCases
import LeanWang.OllingerRobinson104PairCoverSeamPathBoundedBase
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk00
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk01
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk02
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk03
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk04
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk05
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk06
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk07
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk08
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk09
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk10
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk11
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk12
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBaseChunk13

/-! Assemble the cached canonical certificates for the odd seam-path base. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathOddBase

open ShadedFreeLineRecurrence PairCoverSeamPathBaseAudit
  PairCoverSeamPathBoundedBase

theorem chunkChecks : ChunkChecks .odd 0 := by
  intro chunk
  fin_cases chunk
  · exact PairCoverSeamPathOddBaseChunk00.complete
  · exact PairCoverSeamPathOddBaseChunk01.complete
  · exact PairCoverSeamPathOddBaseChunk02.complete
  · exact PairCoverSeamPathOddBaseChunk03.complete
  · exact PairCoverSeamPathOddBaseChunk04.complete
  · exact PairCoverSeamPathOddBaseChunk05.complete
  · exact PairCoverSeamPathOddBaseChunk06.complete
  · exact PairCoverSeamPathOddBaseChunk07.complete
  · exact PairCoverSeamPathOddBaseChunk08.complete
  · exact PairCoverSeamPathOddBaseChunk09.complete
  · exact PairCoverSeamPathOddBaseChunk10.complete
  · exact PairCoverSeamPathOddBaseChunk11.complete
  · exact PairCoverSeamPathOddBaseChunk12.complete
  · exact PairCoverSeamPathOddBaseChunk13.complete

theorem paths : Paths .odd 0 :=
  chunkChecks.paths

theorem boundedPaths : BoundedPaths .odd 0 :=
  PairCoverSeamPathBoundedBase.ChunkChecks.boundedPaths chunkChecks

end PairCoverSeamPathOddBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
