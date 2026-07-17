/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Reduction
import LeanWang.Robinson.Closed104.ShadedCarrierCornerAddressing
import LeanWang.Robinson.Closed104.PairCoverSeamRequiredForward

/-!
# Robinson proof of Wang-tile undecidability

This module closes the fixed-universal-machine reduction with the corrected
Ollinger--Robinson 104-tile routed scaffold.  It exports one proof-neutral
`DominoProblem.Reduction`; many-one reducibility and undecidability are generic
consequences of that certificate.
-/

noncomputable section

namespace LeanWang
namespace Robinson

open OllingerRobinson.Figure13Layers.Closed104

/-- The concrete Robinson reduction certificate. -/
def reduction : DominoProblem.Reduction :=
  UniversalTM0Reduction.routedReduction
    ShadedSignals.routedScaffold
    ShadedCarrierCornerAddressing.realizesRoutedPointedPlanes
    PairCoverSeamRequiredForward.closed104_forcesRoutedFixedCornerSquares

/-- Fixed nonhalting many-one reduces to the Wang domino problem. -/
theorem fixedNonhalting_manyOneReducible :
    DominoProblem.FixedNonhalting ≤₀ DominoProblem.Holds :=
  reduction.manyOneReducible

/-- Fixed nonhalting many-one reduces to the encoded Wang domino problem. -/
theorem fixedNonhalting_manyOneReducible_encodedDominoProblem :
    DominoProblem.FixedNonhalting ≤₀ DominoProblem.EncodedHolds :=
  reduction.encodedManyOneReducible

/-- Encoded Wang domino undecidability via the Robinson construction. -/
theorem encoded_domino_problem_undecidable :
    DominoProblem.EncodedUndecidable :=
  reduction.encodedUndecidable

/-- Wang domino undecidability via the Robinson construction. -/
theorem domino_problem_undecidable : DominoProblem.Undecidable :=
  reduction.undecidable

end Robinson
end LeanWang

end
