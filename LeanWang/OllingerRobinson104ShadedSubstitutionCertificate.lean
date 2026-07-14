/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedSubstitutionChecks

/-!
# Certificate for the finite-state red-shade substitution
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSubstitution

open RedShadeGraphRefinement

set_option maxRecDepth 20000

theorem modelNodeValid_of_mem {node : Nat} (hnode : node ∈ reachable) :
    modelNodeValid node = true := by
  have checked := List.all_eq_true.1 reachableClosed_eq_true node hnode
  simp only [Bool.and_eq_true] at checked
  exact checked.1

theorem child_mem_reachable {node child : Nat} (hnode : node ∈ reachable)
    (hchild : child ∈ children node) : child ∈ reachable := by
  have checked := List.all_eq_true.1 reachableClosed_eq_true node hnode
  simp only [Bool.and_eq_true] at checked
  have childrenChecked := checked.2
  exact of_decide_eq_true (List.all_eq_true.1 childrenChecked child hchild)

theorem modelData_isSome_of_mem {node : Nat} (hnode : node ∈ reachable) :
    (modelData node).isSome = true := by
  have valid := modelNodeValid_of_mem hnode
  simp only [modelNodeValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1.1

theorem children_length_of_mem {node : Nat} (hnode : node ∈ reachable) :
    (children node).length = 16 := by
  have valid := modelNodeValid_of_mem hnode
  simp only [modelNodeValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1.2

theorem modelBoundariesValid_of_mem {node : Nat} (hnode : node ∈ reachable) :
    modelBoundariesValid node = true := by
  have valid := modelNodeValid_of_mem hnode
  simp only [modelNodeValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.2

theorem decoratedCompatible_of_mem {first second : Nat}
    (hfirst : first ∈ reachable) (hsecond : second ∈ reachable) :
    match modelData first, modelData second with
    | some firstData, some secondData =>
        decoratedHCompatible firstData secondData = true ∧
          decoratedVCompatible firstData secondData = true
    | _, _ => False := by
  have firstChecked := List.all_eq_true.1 reachablePairsValid_eq_true
    first hfirst
  have pairChecked := List.all_eq_true.1 firstChecked second hsecond
  cases hfirstData : modelData first <;>
    cases hsecondData : modelData second <;>
    simp_all [Bool.and_eq_true]

theorem reachableStructureValid_of_mem {node : Nat}
    (hnode : node ∈ reachable) :
    match modelData node with
    | none => False
    | some data =>
        data.block ∈ validShadeBlocks data.parent ∧
          expansionInternallyValid data = true ∧
          ∀ position, position < 16 → modelChildValid node position = true := by
  have checked := List.all_eq_true.1 reachableStructureValid_eq_true node hnode
  cases hdata : modelData node with
  | none => simp [hdata] at checked
  | some data =>
      simp only [hdata, decide_eq_true_eq, Bool.and_eq_true,
        List.all_eq_true] at checked
      exact ⟨checked.1.1, checked.1.2, fun position hposition =>
        checked.2 position (by simpa using hposition)⟩

theorem modelData_exists_of_mem {node : Nat} (hnode : node ∈ reachable) :
    ∃ data, modelData node = some data := by
  exact Option.isSome_iff_exists.mp (modelData_isSome_of_mem hnode)

theorem modelChildValid_of_mem {node position : Nat}
    (hnode : node ∈ reachable) (hposition : position < 16) :
    modelChildValid node position = true := by
  have checked := List.all_eq_true.1 reachableStructureValid_eq_true node hnode
  cases hdata : modelData node with
  | none => simp [hdata] at checked
  | some data =>
      simp only [hdata, decide_eq_true_eq, Bool.and_eq_true,
        List.all_eq_true] at checked
      exact checked.2 position (by simpa using hposition)

set_option maxHeartbeats 1000000 in
-- Unfolding the proof-bearing finite lookup through four nested options is costly.
theorem modelChild_spec_of_mem {node position : Nat}
    (hnode : node ∈ reachable) (hposition : position < 16) :
    ∃ data child childData block,
      modelData node = some data ∧
      childNode node position = some child ∧
      modelData child = some childData ∧
      data.expansion[position]? = some block ∧
      child ∈ reachable ∧
      childData.parent =
        fineGrid data.parent (position % 4) (position / 4) ∧
      childData.block = block := by
  have checked := modelChildValid_of_mem hnode hposition
  unfold modelChildValid at checked
  cases hdata : modelData node with
  | none => simp [hdata] at checked
  | some data =>
      cases hchild : childNode node position with
      | none => simp [hdata, hchild] at checked
      | some child =>
          cases hchildData : modelData child with
          | none => simp [hdata, hchild, hchildData] at checked
          | some childData =>
              cases hblock : data.expansion[position]? with
              | none => simp [hdata, hchild, hchildData, hblock] at checked
              | some block =>
                  simp only [hdata, hchild, hchildData, hblock,
                    Bool.and_eq_true, decide_eq_true_eq] at checked
                  exact ⟨data, child, childData, block, rfl, rfl,
                    hchildData, hblock, checked.1.1, checked.1.2, checked.2⟩

theorem modelChild_exists_of_mem {node position : Nat}
    (hnode : node ∈ reachable) (hposition : position < 16) :
    ∃ child, childNode node position = some child ∧ child ∈ reachable := by
  rcases modelChild_spec_of_mem hnode hposition with
    ⟨_, child, _, _, _, hchild, _, _, hmem, _, _⟩
  exact ⟨child, hchild, hmem⟩

end ShadedSubstitution
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
