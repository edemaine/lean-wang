/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Tactic.FinCases
import LeanWang.OllingerRobinson104PairCoverSeamPathComponentCertificate
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk00
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk01
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk02
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk03
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk04
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk05
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk06
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk07
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk08
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk09
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk10
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk11
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk12
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBaseChunk13

/-! Assemble the cached canonical certificates for the even seam-path base. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathEvenBase

open ShadedFreeLineRecurrence PairCoverSeamPathBaseAudit
  PairCoverSeamPathBoundedBase PairCoverSeamPathComponentCertificate

theorem chunkChecks :
    PairCoverSeamPathComponentCertificate.ChunkChecks .even 1 evenRoots := by
  intro chunk
  fin_cases chunk
  · exact PairCoverSeamPathEvenBaseChunk00.complete
  · exact PairCoverSeamPathEvenBaseChunk01.complete
  · exact PairCoverSeamPathEvenBaseChunk02.complete
  · exact PairCoverSeamPathEvenBaseChunk03.complete
  · exact PairCoverSeamPathEvenBaseChunk04.complete
  · exact PairCoverSeamPathEvenBaseChunk05.complete
  · exact PairCoverSeamPathEvenBaseChunk06.complete
  · exact PairCoverSeamPathEvenBaseChunk07.complete
  · exact PairCoverSeamPathEvenBaseChunk08.complete
  · exact PairCoverSeamPathEvenBaseChunk09.complete
  · exact PairCoverSeamPathEvenBaseChunk10.complete
  · exact PairCoverSeamPathEvenBaseChunk11.complete
  · exact PairCoverSeamPathEvenBaseChunk12.complete
  · exact PairCoverSeamPathEvenBaseChunk13.complete

theorem boundedPaths : BoundedPaths .even 1 :=
  PairCoverSeamPathComponentCertificate.ChunkChecks.boundedPaths
    evenRoots_inBounds chunkChecks

theorem paths : Paths .even 1 :=
  PairCoverSeamPathComponentCertificate.BoundedPaths.paths boundedPaths

end PairCoverSeamPathEvenBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
