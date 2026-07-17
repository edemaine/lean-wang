/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderFactorData
import LeanWang.Robinson.Closed104.ShadedSubstitutionSupertiles

/-!
# Certificate for the 16-state selected-border factor
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderFactor

open ShadedSubstitution

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
theorem factorValid_eq_true : factorValid = true := by
  native_decide

theorem patches_length_eq : patches.length = 9 := by
  have valid := factorValid_eq_true
  have parts :
      (decide (patches.length = 9) = true ∧
        decide (classCount = 16) = true) ∧
        reachable.all nodeFactorValid = true := by
    simpa only [factorValid, Bool.and_eq_true] using valid
  exact of_decide_eq_true parts.1.1

theorem classCount_eq : classCount = 16 := by
  have valid := factorValid_eq_true
  have parts :
      (decide (patches.length = 9) = true ∧
        decide (classCount = 16) = true) ∧
        reachable.all nodeFactorValid = true := by
    simpa only [factorValid, Bool.and_eq_true] using valid
  exact of_decide_eq_true parts.1.2

set_option linter.style.nativeDecide false in
theorem seed_class : classOf seedNode = 15 := by
  native_decide

theorem nodeFactorValid_eq_true (node : Node) :
    nodeFactorValid node = true := by
  have valid := factorValid_eq_true
  simp only [factorValid, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at valid
  exact valid.2 node node.property

theorem class_lt (node : Node) : classOf node < 16 := by
  have valid := nodeFactorValid_eq_true node
  have parts :
      (nodeClassValid node = true ∧ nodePatchValid node = true) ∧
        nodeChildrenValid node = true := by
    simpa only [nodeFactorValid, Bool.and_eq_true] using valid
  have classValid := parts.1.1
  rw [nodeClassValid, Bool.and_eq_true, decide_eq_true_eq] at classValid
  exact of_decide_eq_true classValid.2

theorem patch_eq (node : Node) :
    patchData node.data = classPatch (classOf node) := by
  have valid := nodeFactorValid_eq_true node
  have parts :
      (nodeClassValid node = true ∧ nodePatchValid node = true) ∧
        nodeChildrenValid node = true := by
    simpa only [nodeFactorValid, Bool.and_eq_true] using valid
  have patchValid := parts.1.2
  change decide (patch node = some (classPatch (classOf node))) = true at patchValid
  have patchEquality : patch node = some (classPatch (classOf node)) :=
    of_decide_eq_true patchValid
  change (modelData node).map patchData = some (classPatch (classOf node)) at patchEquality
  rw [Node.modelData_data] at patchEquality
  exact Option.some.inj patchEquality

theorem child_class (node : Node) (position : Fin 16) :
    classOf (node.child position) = childClass (classOf node) position := by
  have valid := nodeFactorValid_eq_true node
  have parts :
      (nodeClassValid node = true ∧ nodePatchValid node = true) ∧
        nodeChildrenValid node = true := by
    simpa only [nodeFactorValid, Bool.and_eq_true] using valid
  have childrenValid := parts.2
  rw [nodeChildrenValid] at childrenValid
  have positionMem : position.val ∈ List.range 16 := by
    simpa using position.isLt
  have childValid :=
    (List.all_eq_true.mp childrenValid) position.val positionMem
  rw [Node.childNode_child] at childValid
  exact of_decide_eq_true childValid

end ShadedCarrierBorderFactor
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
