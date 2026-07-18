/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlConcreteFamilies
import LeanWang.Kari.Hooper.CounterControlAffineReduction

/-!
# Reduction assembled from the concrete command families

This module isolates the final proof-neutral glue.  A uniform implementation
of outward validation supplies the complete guarded converse laws for the
effective Hooper controller; Kari's affine compiler then produces the shared
domino-reduction certificate.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlConcreteReduction

noncomputable section

/-- Turn a uniform outward-validation handoff into the complete computable
Wang-tiles reduction. -/
def reduction_of_outwardLaws
    (houtward : ∀ (c : Nat.Partrec.Code)
        (hmortal : ¬ DominoProblem.FixedNonhalting c),
      CounterControlGenuineValidation.OutwardInstructionHandoffLaw
        CounterControlReduction.base c hmortal) :
    DominoProblem.Reduction :=
  CounterControlAffineReduction.reduction_of_laws fun c =>
    CounterControlConcreteFamilies.laws_of_outwardLaws
      CounterControlReduction.base c (houtward c)

end

end CounterControlConcreteReduction
end Hooper
end Kari
end LeanWang
