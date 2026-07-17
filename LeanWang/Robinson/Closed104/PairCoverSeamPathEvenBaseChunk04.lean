/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPathComponentCertificate

/-! Cached canonical certificate 4 for the even seam-path base. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathEvenBaseChunk04

open ShadedFreeLineRecurrence PairCoverSeamPathComponentCertificate

set_option linter.style.nativeDecide false in
set_option maxHeartbeats 1000000 in
-- Four native parent checks exceed the default declaration budget.
theorem complete : checkChunk .even 1 evenRoots ⟨4, by decide⟩ = true := by
  apply checkChunk_of_parentChecks
  intro offset
  fin_cases offset <;>
    rw [← compiledCheckChunkParent_eq_checkChunkParent] <;>
    native_decide

end PairCoverSeamPathEvenBaseChunk04
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
