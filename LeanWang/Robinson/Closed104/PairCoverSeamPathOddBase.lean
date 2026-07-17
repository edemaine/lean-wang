/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Tactic.FinCases
import LeanWang.Robinson.Closed104.PairCoverSeamPathComponentCertificate
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk00
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk01
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk02
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk03
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk04
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk05
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk06
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk07
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk08
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk09
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk10
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk11
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk12
import LeanWang.Robinson.Closed104.PairCoverSeamPathOddBaseChunk13

/-! Assemble the cached canonical certificates for the odd seam-path base. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathOddBase

open ShadedFreeLineRecurrence PairCoverSeamPathBaseAudit
  PairCoverSeamPathBoundedBase PairCoverSeamPathComponentCertificate

theorem chunkChecks :
    PairCoverSeamPathComponentCertificate.ChunkChecks .odd 0 oddRoots := by
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

theorem boundedPaths : BoundedPaths .odd 0 :=
  PairCoverSeamPathComponentCertificate.ChunkChecks.boundedPaths
    oddRoots_inBounds chunkChecks

theorem paths : Paths .odd 0 :=
  PairCoverSeamPathComponentCertificate.BoundedPaths.paths boundedPaths

end PairCoverSeamPathOddBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
