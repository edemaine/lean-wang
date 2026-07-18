/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCoreSimulation
import LeanWang.Kari.Hooper.CounterControlInstructionResolution

/-!
# The finite-frame converse Basic Lemma for the counter controller

The instruction-resolution module supplies the concrete one-step law.  The
generic trace/core layer turns it into `CoreResolves`, after which Hooper's
simultaneous strong induction proves that every genuine finite compiled
search either finds its target exactly or makes the controller halt.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlFiniteConverse

open CounterControlSearchSystem
open CounterControlCoreSimulation

noncomputable section

/-- The complete instruction compiler supplies the uniform resolving step
laws required by the abstract finite-frame argument. -/
theorem resolvingStepLaws (base : Nat) (c : Nat.Partrec.Code) :
    ResolvingStepLaws base c := by
  intro frame hshort
  apply CounterControlInstructionResolution.oneStepResolves
  simpa [CounterControlSearchResolution.ShortResolves] using hshort

/-- The canonical core of every genuine nested frame either restores its
suspended boundary or halts. -/
theorem coreResolves (base : Nat) (c : Nat.Partrec.Code) :
    CoreResolves base c :=
  coreResolves_of_resolvingStepLaws base c (resolvingStepLaws base c)

/-- Concrete converse Basic Lemma: every finite generated search resolves. -/
theorem resolves_all (base : Nat) (c : Nat.Partrec.Code) :
    ∀ distance : Nat, (searchSystem base c).Resolves distance :=
  CounterControlSearchSystem.resolves_all base c (coreResolves base c)

end

end CounterControlFiniteConverse
end Hooper
end Kari
end LeanWang
