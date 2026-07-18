/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCoreSimulation
import LeanWang.Kari.Hooper.CounterControlInstructionSimulation

/-!
# The finite-frame forward Basic Lemma for the counter controller

The instruction-simulation module supplies the concrete one-step law.  The
generic trace/core layer turns it into `CoreGrows`; Hooper's simultaneous
strong induction then proves that every genuine finite compiled search finds
its target whenever the source computation is nonhalting.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlFiniteForward

open CounterControlSearchSystem
open CounterControlCoreSimulation

noncomputable section

/-- The complete instruction compiler supplies the uniform forward step laws
required by the abstract finite-frame argument. -/
theorem forwardStepLaws (base : Nat) (c : Nat.Partrec.Code) :
    ForwardStepLaws base c := by
  intro frame hshort
  exact CounterControlInstructionSimulation.oneStepGrows base c frame hshort

/-- A nonhalting canonical source core eventually restores every suspended
search boundary. -/
theorem coreGrows (base : Nat) (c : Nat.Partrec.Code) :
    CoreGrows base c (DominoProblem.FixedNonhalting c) :=
  coreGrows_of_forwardStepLaws base c (forwardStepLaws base c)

/-- Concrete forward Basic Lemma: under source nonhalting, every finite
generated search finds its target. -/
theorem solves_all (base : Nat) (c : Nat.Partrec.Code)
    (hnonhalting : DominoProblem.FixedNonhalting c) :
    ∀ distance : Nat, (searchSystem base c).Solves distance :=
  CounterControlSearchSystem.solves_all base c
    (DominoProblem.FixedNonhalting c) (coreGrows base c) hnonhalting

end

end CounterControlFiniteForward
end Hooper
end Kari
end LeanWang
