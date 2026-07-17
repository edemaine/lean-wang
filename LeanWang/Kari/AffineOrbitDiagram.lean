/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.AffineLimit

/-!
# From admissible affine orbits to transducer diagrams

`AffineLimit` proves the difficult converse direction: every upper-half
diagram yields a forward affine orbit.  This file packages the constructive
direction.  A forward orbit is *digit-admissible* when each row's Beatty
digits lie in the input and output alphabets declared by its selected compiled
branch.  The canonical bounded carries from `AffineBeatty` then give an exact
upper-half transducer diagram.

Machine-specific compilers need prove only these finite digit-membership
conditions.  The local carry equations, horizontal matching, branch tags, and
conversion to Wang tiles are handled here once and for all.
-/

namespace LeanWang
namespace Kari

noncomputable section

namespace AffineLimit

/-- The finite alphabets of each selected branch contain every Beatty digit
of the corresponding pair of consecutive orbit states. -/
structure DigitAdmissible {system : AffineSystem}
    (orbit : ForwardOrbit system) : Prop where
  canonical_bound : ∀ y : Nat,
    (orbit.branch y).carryBound =
      AffineBeatty.carryBound (orbit.branch y).branch
  input_mem : ∀ (y : Nat) (x : Int),
    AffineBeatty.digitVector (orbit.state y) x ∈ (orbit.branch y).inputs
  output_mem : ∀ (y : Nat) (x : Int),
    AffineBeatty.digitVector (orbit.state (y + 1)) x ∈
      (orbit.branch y).outputs

/-- Vertical digit colors of the canonical diagram of an affine orbit. -/
def orbitDigits {system : AffineSystem} (orbit : ForwardOrbit system)
    (p : Int × Nat) : Nat :=
  (AffineBeatty.digitVector (orbit.state p.2) p.1).code

/-- Horizontal carry colors of the canonical diagram of an affine orbit. -/
def orbitCarries {system : AffineSystem} (orbit : ForwardOrbit system)
    (p : Int × Nat) : Nat :=
  (orbit.branch p.2).branch.carryColor
    (AffineBeatty.canonicalCarry (orbit.branch p.2).branch
      (orbit.state p.2) (orbit.state (p.2 + 1)) p.1)

/-- The canonical local transition at one orbit-space-time cell. -/
def orbitTransition {system : AffineSystem} (orbit : ForwardOrbit system)
    (p : Int × Nat) : Transition :=
  let compiled := orbit.branch p.2
  compiled.branch.transition
    (AffineBeatty.digitVector (orbit.state p.2) p.1)
    (AffineBeatty.digitVector (orbit.state (p.2 + 1)) p.1)
    (AffineBeatty.canonicalCarry compiled.branch
      (orbit.state p.2) (orbit.state (p.2 + 1)) p.1)
    (AffineBeatty.canonicalCarry compiled.branch
      (orbit.state p.2) (orbit.state (p.2 + 1)) (p.1 + 1))

/-- Every canonical orbit transition belongs to the selected compiled branch. -/
theorem orbitTransition_mem_branch {system : AffineSystem}
    (orbit : ForwardOrbit system) (hadmissible : DigitAdmissible orbit)
    (p : Int × Nat) :
    orbitTransition orbit p ∈ (orbit.branch p.2).transducer := by
  rw [CompiledAffineBranch.transducer, hadmissible.canonical_bound p.2]
  exact AffineBeatty.canonical_transition_mem_transducer
    (orbit.branch p.2).branch (orbit.branch p.2).inputs
      (orbit.branch p.2).outputs (orbit.state p.2)
      (orbit.state (p.2 + 1)) (orbit.realizes p.2) p.1
      (hadmissible.input_mem p.2 p.1)
      (hadmissible.output_mem p.2 p.1)

/-- A digit-admissible infinite affine orbit produces an upper-half-plane
diagram of the finite union transducer. -/
theorem isUpperHalfDiagram_of_digitAdmissible
    {system : AffineSystem} (orbit : ForwardOrbit system)
    (hadmissible : DigitAdmissible orbit) :
    system.transducer.IsUpperHalfDiagram
      (orbitDigits orbit) (orbitCarries orbit) := by
  intro p
  refine ⟨orbitTransition orbit p, ?_, ?_, ?_, ?_, ?_⟩
  · exact (system.mem_transducer_iff (orbitTransition orbit p)).2
      ⟨orbit.branch p.2, orbit.branch_mem p.2,
        orbitTransition_mem_branch orbit hadmissible p⟩
  · rfl
  · rfl
  · rfl
  · rfl

/-- Existential form of the constructive affine-transducer direction. -/
theorem hasUpperHalfDiagram_of_digitAdmissible
    {system : AffineSystem} (orbit : ForwardOrbit system)
    (hadmissible : DigitAdmissible orbit) :
    system.transducer.HasUpperHalfDiagram :=
  ⟨orbitDigits orbit, orbitCarries orbit,
    isUpperHalfDiagram_of_digitAdmissible orbit hadmissible⟩

end AffineLimit

end

end Kari
end LeanWang
