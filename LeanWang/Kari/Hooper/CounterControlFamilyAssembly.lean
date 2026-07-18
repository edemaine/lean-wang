/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedConverse
import LeanWang.Kari.Hooper.CounterControlGuardedEscapeAssembly
import LeanWang.Kari.Hooper.CounterControlMonotoneEntryAssembly

/-!
# Assembly of the concrete Hooper command families

The operational converse has two passes over the same four specialized raw
command families.  Arbitrary genuine searches need weak monotone entry into
the guarded invariant; guarded searches then need strict escape.  This file
packages those two family records and turns them into the proof-neutral laws
consumed by the affine reduction.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlFamilyAssembly

noncomputable section

/-- All specialized command-family facts needed under source mortality. -/
structure Families
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) : Prop where
  monotone : CounterControlMonotoneEntryAssembly.FamilyContinuations
    base c hmortal
  guarded : CounterControlGuardedEscapeAssembly.FamilyContinuations
    base c hmortal

/-- Uniform family continuations discharge the two local converse laws. -/
theorem laws_of_families
    (base : Nat) (c : Nat.Partrec.Code)
    (families : ∀ hmortal : ¬ DominoProblem.FixedNonhalting c,
      Families base c hmortal) :
    CounterControlGuardedConverse.Laws base c := by
  refine ⟨?_, ?_⟩
  · intro hmortal
    exact
      CounterControlMonotoneEntryAssembly.monotoneGuardedEntryLaw_of_families
        base c hmortal (families hmortal).monotone
  · intro hmortal
    exact CounterControlGuardedEscapeAssembly.guardedEscapeLaw_of_families
      base c hmortal (families hmortal).guarded

end

end CounterControlFamilyAssembly
end Hooper
end Kari
end LeanWang
