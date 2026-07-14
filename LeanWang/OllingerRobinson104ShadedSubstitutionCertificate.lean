/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedSubstitutionData

/-!
# Certificate for the finite-state red-shade substitution
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSubstitution

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
theorem reachableClosed_eq_true : reachableClosed = true := by
  native_decide

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

end ShadedSubstitution
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
