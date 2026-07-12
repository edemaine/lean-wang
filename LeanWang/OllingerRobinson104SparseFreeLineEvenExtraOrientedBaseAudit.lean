/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseStep
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraOrientedBaseAuditCheck

/-! Proposition-level soundness for the oriented even-extra base audit. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraOrientedBaseAudit

open RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch
  Signals.FreeCellLocal BorderGeometry SparseFreeLineEvenExtraBaseAudit
  SparseFreeLineEvenExtraCycleBaseAudit

set_option maxRecDepth 20000

def SubsetRoute (parent : Index) (subset : List WeightedStart)
    (target : Port) : Prop :=
  ∃ start ∈ subset,
    Path (searchGrid parent) start.port target
      (Bool.xor start.parity true) ∧
    portPresent (searchGrid parent) target = true

theorem reached_subset_sound
    {parent : Index} {subset : List WeightedStart} {target : Port}
    (checked : SparseFreeLineEvenExtraCycleBaseAudit.reached parent
      (subsetNodes parent subset) target = true) :
    SubsetRoute parent subset target := by
  simp only [SparseFreeLineEvenExtraCycleBaseAudit.reached,
    Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rcases exploreFastWeightedReach_sound hnode with
    ⟨start, hstart, path⟩
  refine ⟨start, hstart, ?_, checked.1⟩
  rw [hcurrent] at path
  simpa [hparity] using path

set_option linter.flexible false in
theorem verticalSubsetCheck_sound
    {parent : Index} {subset : List WeightedStart}
    (checked : verticalSubsetCheck parent subset = true) :
    ∀ x, 2 ≤ x → x < 64 →
      Signals.verticalInterior?
        (componentAt (searchGrid parent) x 40) (quadrantAt x 40) ≠ none →
      SubsetRoute parent subset ⟨x, 40, .south⟩ ∨
        SubsetRoute parent subset ⟨x, 40, .north⟩ := by
  simp only [verticalSubsetCheck, List.all_eq_true, List.mem_range] at checked
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
  · exact Or.inl (reached_subset_sound covered)
  · exact Or.inr (reached_subset_sound covered)

set_option linter.flexible false in
theorem horizontalSubsetCheck_sound
    {parent : Index} {subset : List WeightedStart}
    (checked : horizontalSubsetCheck parent subset = true) :
    ∀ y, 2 ≤ y → y < 64 →
      Signals.horizontalInterior?
        (componentAt (searchGrid parent) 40 y) (quadrantAt 40 y) ≠ none →
      SubsetRoute parent subset ⟨40, y, .west⟩ ∨
        SubsetRoute parent subset ⟨40, y, .east⟩ := by
  simp only [horizontalSubsetCheck, List.all_eq_true, List.mem_range] at checked
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
  · exact Or.inl (reached_subset_sound covered)
  · exact Or.inr (reached_subset_sound covered)

theorem canonical_check (parent : Index) :
    verticalSubsetCheck (BorderSubstitution.canonicalIndex parent)
        southStarts = true ∧
      horizontalSubsetCheck (BorderSubstitution.canonicalIndex parent)
        westStarts = true := by
  exact oriented_complete (BorderSubstitution.indexState parent)
    (BorderSubstitution.indexState_mem_states parent)

theorem subsetRoute_of_canonicalIndex
    {parent : Index} {subset : List WeightedStart} {target : Port}
    (route : SubsetRoute (BorderSubstitution.canonicalIndex parent)
      subset target) :
    SubsetRoute parent subset target := by
  rcases route with ⟨start, hstart, path, targetLive⟩
  let same :=
    SparseFreeLineEvenExtraBaseStep.sameComponents_searchGrid_canonicalIndex
      parent
  refine ⟨start, hstart,
    SparseFreeLineEvenExtraBaseStep.path_congr_of_sameComponents same path, ?_⟩
  rwa [portPresent_congr same target] at targetLive

theorem auditedVerticalRoutes
    (parent : Index) (x : Nat) (hxLower : 2 ≤ x) (hxUpper : x < 64)
    (interior : Signals.verticalInterior?
      (componentAt (searchGrid parent) x 40) (quadrantAt x 40) ≠ none) :
    SubsetRoute parent southStarts ⟨x, 40, .south⟩ ∨
      SubsetRoute parent southStarts ⟨x, 40, .north⟩ := by
  let same :=
    SparseFreeLineEvenExtraBaseStep.sameComponents_searchGrid_canonicalIndex
      parent
  have canonicalInterior : Signals.verticalInterior?
      (componentAt (searchGrid (BorderSubstitution.canonicalIndex parent)) x 40)
        (quadrantAt x 40) ≠ none := by
    rw [same x 40]
    exact interior
  rcases verticalSubsetCheck_sound (canonical_check parent).1 x hxLower hxUpper
      canonicalInterior with route | route
  · exact Or.inl (subsetRoute_of_canonicalIndex route)
  · exact Or.inr (subsetRoute_of_canonicalIndex route)

theorem auditedHorizontalRoutes
    (parent : Index) (y : Nat) (hyLower : 2 ≤ y) (hyUpper : y < 64)
    (interior : Signals.horizontalInterior?
      (componentAt (searchGrid parent) 40 y) (quadrantAt 40 y) ≠ none) :
    SubsetRoute parent westStarts ⟨40, y, .west⟩ ∨
      SubsetRoute parent westStarts ⟨40, y, .east⟩ := by
  let same :=
    SparseFreeLineEvenExtraBaseStep.sameComponents_searchGrid_canonicalIndex
      parent
  have canonicalInterior : Signals.horizontalInterior?
      (componentAt (searchGrid (BorderSubstitution.canonicalIndex parent)) 40 y)
        (quadrantAt 40 y) ≠ none := by
    rw [same 40 y]
    exact interior
  rcases horizontalSubsetCheck_sound (canonical_check parent).2 y hyLower hyUpper
      canonicalInterior with route | route
  · exact Or.inl (subsetRoute_of_canonicalIndex route)
  · exact Or.inr (subsetRoute_of_canonicalIndex route)

theorem southStart_coordinate {start : WeightedStart}
    (hstart : start ∈ southStarts) : start.port.y = 1 := by
  simpa [southStarts] using (List.mem_filter.1 hstart).2

theorem westStart_coordinate {start : WeightedStart}
    (hstart : start ∈ westStarts) : start.port.x = 1 := by
  simpa [westStarts] using (List.mem_filter.1 hstart).2

end SparseFreeLineEvenExtraOrientedBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
