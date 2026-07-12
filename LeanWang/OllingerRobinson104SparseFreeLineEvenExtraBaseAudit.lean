/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAuditData

/-! Proposition-level soundness for the finite even-extra base audit. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraBaseAudit

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch Signals.FreeCellLocal
  BorderCoverageLocalAudit

def Route (parent : Index) (target : Port) : Prop :=
  ∃ start ∈ starts parent,
    Path (searchGrid parent) start.port target
      (Bool.xor start.parity true) ∧
    portPresent (searchGrid parent) target = true

theorem starts_inBounds (parent : Index) :
    ∀ start ∈ starts parent, PortInBounds start.port 65 65 := by
  have checked := startsBounded_complete parent
  simp only [startsBounded, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at checked
  intro start hstart
  exact checked start hstart

theorem candidate_sparse_lower (parent : Index) :
    ∀ candidate ∈ candidates parent,
      32 ≤ (sparsePort candidate.port).x ∧
        32 ≤ (sparsePort candidate.port).y := by
  have checked := candidatesSparseLower_complete parent
  simp only [candidatesSparseLower, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at checked
  intro candidate hcandidate
  exact checked candidate hcandidate

theorem reached_sound {parent : Index} {found : List ReachNode} {target : Port}
    (checked : reached parent found target = true)
    (hfound : found = nodes parent) : Route parent target := by
  simp only [reached, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rw [hfound] at hnode
  rcases exploreFastWeightedReach_sound hnode with
    ⟨start, hstart, path⟩
  refine ⟨start, hstart, ?_, checked.1⟩
  rw [hcurrent] at path
  simpa [hparity] using path

set_option linter.flexible false in
theorem verticalCheck_sound {parent : Index} {found : List ReachNode}
    (checked : verticalCheck parent found = true)
    (hfound : found = nodes parent) :
    ∀ x, 2 ≤ x → x < 64 →
      Signals.verticalInterior?
        (componentAt (searchGrid parent) x 40) (quadrantAt x 40) ≠ none →
      Route parent ⟨x, 40, .south⟩ ∨ Route parent ⟨x, 40, .north⟩ := by
  simp only [verticalCheck, List.all_eq_true, List.mem_range] at checked
  intro x hxLower hxUpper interior
  let delta := x - 2
  have hdelta : delta < 62 := by simp [delta]; omega
  have hx : 2 + delta = x := by simp [delta]; omega
  have covered := checked delta hdelta
  rw [hx] at covered
  have required : (Signals.verticalInterior?
      (componentAt (searchGrid parent) x 40) (quadrantAt x 40)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_sound covered hfound)
  · exact Or.inr (reached_sound covered hfound)

set_option linter.flexible false in
theorem horizontalCheck_sound {parent : Index} {found : List ReachNode}
    (checked : horizontalCheck parent found = true)
    (hfound : found = nodes parent) :
    ∀ y, 2 ≤ y → y < 64 →
      Signals.horizontalInterior?
        (componentAt (searchGrid parent) 40 y) (quadrantAt 40 y) ≠ none →
      Route parent ⟨40, y, .west⟩ ∨ Route parent ⟨40, y, .east⟩ := by
  simp only [horizontalCheck, List.all_eq_true, List.mem_range] at checked
  intro y hyLower hyUpper interior
  let delta := y - 2
  have hdelta : delta < 62 := by simp [delta]; omega
  have hy : 2 + delta = y := by simp [delta]; omega
  have covered := checked delta hdelta
  rw [hy] at covered
  have required : (Signals.horizontalInterior?
      (componentAt (searchGrid parent) 40 y) (quadrantAt 40 y)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_sound covered hfound)
  · exact Or.inr (reached_sound covered hfound)

theorem check_sound {parent : Index} (checked : check parent = true) :
    (∀ x, 2 ≤ x → x < 64 →
      Signals.verticalInterior?
        (componentAt (searchGrid parent) x 40) (quadrantAt x 40) ≠ none →
      Route parent ⟨x, 40, .south⟩ ∨ Route parent ⟨x, 40, .north⟩) ∧
    (∀ y, 2 ≤ y → y < 64 →
      Signals.horizontalInterior?
        (componentAt (searchGrid parent) 40 y) (quadrantAt 40 y) ≠ none →
      Route parent ⟨40, y, .west⟩ ∨ Route parent ⟨40, y, .east⟩) := by
  simp only [check, Bool.and_eq_true] at checked
  exact ⟨verticalCheck_sound checked.1 rfl,
    horizontalCheck_sound checked.2 rfl⟩

end SparseFreeLineEvenExtraBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
