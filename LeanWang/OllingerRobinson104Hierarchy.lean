/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ParentPlane

/-!
An infinite desubstitution hierarchy for every valid corrected-Ollinger plane.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Hierarchy

open Desubstitution ParentPlane

/-- An index plane bundled with its matching proof. -/
structure ValidPlane where
  tiling : IndexPlane
  valid : ValidIndexPlane tiling

/-- One recognized desubstitution step from a fine plane to a coarse plane. -/
structure Step (fine : ValidPlane) where
  origin : Int × Int
  coarse : ValidPlane
  phase : thinAt fine.tiling origin = .a
  children : ∀ k : Int × Int,
    IsParentAt fine.tiling origin (coarse.tiling k) k

theorem step_nonempty (fine : ValidPlane) : Nonempty (Step fine) := by
  rcases exists_valid_parentPlane fine.valid with
    ⟨origin, parent, hphase, hvalid, hchildren⟩
  exact ⟨{
    origin := origin
    coarse := ⟨parent, hvalid⟩
    phase := hphase
    children := hchildren
  }⟩

/-- A fixed classical choice of one recognized parent plane. -/
noncomputable def chosenStep (fine : ValidPlane) : Step fine :=
  Classical.choice (step_nonempty fine)

/-- Repeatedly choose recognized parent planes. -/
noncomputable def planeAt (base : ValidPlane) : Nat → ValidPlane
  | 0 => base
  | n + 1 => (chosenStep (planeAt base n)).coarse

/-- Parity origin used between levels `n` and `n + 1`. -/
noncomputable def originAt (base : ValidPlane) (n : Nat) : Int × Int :=
  (chosenStep (planeAt base n)).origin

@[simp]
theorem planeAt_zero (base : ValidPlane) : planeAt base 0 = base :=
  rfl

@[simp]
theorem planeAt_succ (base : ValidPlane) (n : Nat) :
    planeAt base (n + 1) = (chosenStep (planeAt base n)).coarse :=
  rfl

theorem originAt_phase (base : ValidPlane) (n : Nat) :
    thinAt (planeAt base n).tiling (originAt base n) = .a :=
  (chosenStep (planeAt base n)).phase

theorem planeAt_children (base : ValidPlane) (n : Nat) (k : Int × Int) :
    IsParentAt (planeAt base n).tiling (originAt base n)
      ((planeAt base (n + 1)).tiling k) k := by
  exact (chosenStep (planeAt base n)).children k

/-- Proof-facing hierarchy, abstracting away the particular classical choices. -/
structure Tower (base : ValidPlane) where
  plane : Nat → ValidPlane
  origin : Nat → Int × Int
  zero : plane 0 = base
  children : ∀ n k,
    IsParentAt (plane n).tiling (origin n) ((plane (n + 1)).tiling k) k

/-- Every valid corrected-Ollinger plane has an infinite parent hierarchy. -/
noncomputable def tower (base : ValidPlane) : Tower base where
  plane := planeAt base
  origin := originAt base
  zero := planeAt_zero base
  children := planeAt_children base

end Hierarchy
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
