/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlConcreteReduction
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardLaw

/-!
# Kari--Hooper proof of Wang-tile undecidability

This module closes the effective Hooper immortality construction and Kari's
affine Wang-tile compiler.  It exports a proof-neutral
`DominoProblem.Reduction`; many-one reducibility, co-r.e. completeness, and
undecidability are generic consequences of that certificate.
-/

noncomputable section

namespace LeanWang
namespace Kari

/-- The concrete Kari--Hooper reduction certificate. -/
def reduction : DominoProblem.Reduction :=
  Hooper.CounterControlConcreteReduction.reduction_of_outwardLaws fun c hmortal =>
    Hooper.CounterControlGenuineValidationOutwardLaw.outwardInstructionHandoffLaw
      Hooper.CounterControlReduction.base c hmortal

/-- Fixed nonhalting many-one reduces to the Wang domino problem. -/
theorem fixedNonhalting_manyOneReducible :
    DominoProblem.FixedNonhalting ≤₀ DominoProblem.Holds :=
  reduction.manyOneReducible

/-- Fixed nonhalting many-one reduces to the encoded Wang domino problem. -/
theorem fixedNonhalting_manyOneReducible_encodedDominoProblem :
    DominoProblem.FixedNonhalting ≤₀ DominoProblem.EncodedHolds :=
  reduction.encodedManyOneReducible

/-- The Wang domino problem is co-r.e.-hard via the Kari--Hooper construction. -/
theorem domino_problem_coRE_hard : DominoProblem.CoREHard :=
  reduction.coREHard

/-- The encoded Wang domino problem is co-r.e.-hard via Kari--Hooper. -/
theorem encoded_domino_problem_coRE_hard : DominoProblem.EncodedCoREHard :=
  reduction.encodedCoREHard

/-- The Wang domino problem is co-r.e.-complete via Kari--Hooper. -/
theorem domino_problem_coRE_complete : DominoProblem.CoREComplete :=
  reduction.coREComplete

/-- The encoded Wang domino problem is co-r.e.-complete via Kari--Hooper. -/
theorem encoded_domino_problem_coRE_complete :
    DominoProblem.EncodedCoREComplete :=
  reduction.encodedCoREComplete

/-- Encoded Wang domino undecidability via the Kari--Hooper construction. -/
theorem encoded_domino_problem_undecidable :
    DominoProblem.EncodedUndecidable :=
  reduction.encodedUndecidable

/-- Wang domino undecidability via the Kari--Hooper construction. -/
theorem domino_problem_undecidable : DominoProblem.Undecidable :=
  reduction.undecidable

end Kari
end LeanWang

end
