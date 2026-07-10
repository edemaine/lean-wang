/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedCycles

/-!
Finite local expansion rules for corrected-Ollinger red cycles.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedCycles

@[irreducible] def southwestChild (parent : Index) : Index :=
  childBlock parent ⟨0, by decide⟩ ⟨0, by decide⟩

@[irreducible] def southeastChild (parent : Index) : Index :=
  childBlock parent ⟨1, by decide⟩ ⟨0, by decide⟩

@[irreducible] def northwestChild (parent : Index) : Index :=
  childBlock parent ⟨0, by decide⟩ ⟨1, by decide⟩

@[irreducible] def indexThick (index : Index) : Figure16.Thick :=
  (components index).2.1

theorem indexThick_eq (index : Index) :
    indexThick index = (components index).2.1 := by
  unfold indexThick
  rfl

/-- Finite audit of the six local facts that double a red rectangular cycle. -/
def allRedCycleExpansionRulesBool : Bool :=
  (List.finRange 104).all fun parent =>
    decide (
      (indexThick parent = .a → indexThick (southwestChild parent) = .a) ∧
      (indexThick parent = .b → indexThick (southwestChild parent) = .b) ∧
      (indexThick parent = .c → indexThick (southwestChild parent) = .c) ∧
      (indexThick parent = .d → indexThick (southwestChild parent) = .d) ∧
      (indexThick parent = .a →
        hasRedHorizontal (indexThick (southeastChild parent)) = true) ∧
      (indexThick parent = .b →
        hasRedHorizontal (indexThick (southeastChild parent)) = true ∧
        hasRedVertical (indexThick (northwestChild parent)) = true) ∧
      (indexThick parent = .c →
        hasRedVertical (indexThick (northwestChild parent)) = true) ∧
      (hasRedHorizontal (indexThick parent) = true →
        hasRedHorizontal (indexThick (southwestChild parent)) = true ∧
        hasRedHorizontal (indexThick (southeastChild parent)) = true) ∧
      (hasRedVertical (indexThick parent) = true →
        hasRedVertical (indexThick (southwestChild parent)) = true ∧
        hasRedVertical (indexThick (northwestChild parent)) = true))

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allRedCycleExpansionRulesBool_eq_true :
    allRedCycleExpansionRulesBool = true := by
  native_decide

theorem redCycleExpansionRules (parent : Index) :
    (indexThick parent = .a → indexThick (southwestChild parent) = .a) ∧
    (indexThick parent = .b → indexThick (southwestChild parent) = .b) ∧
    (indexThick parent = .c → indexThick (southwestChild parent) = .c) ∧
    (indexThick parent = .d → indexThick (southwestChild parent) = .d) ∧
    (indexThick parent = .a →
      hasRedHorizontal (indexThick (southeastChild parent)) = true) ∧
    (indexThick parent = .b →
      hasRedHorizontal (indexThick (southeastChild parent)) = true ∧
      hasRedVertical (indexThick (northwestChild parent)) = true) ∧
    (indexThick parent = .c →
      hasRedVertical (indexThick (northwestChild parent)) = true) ∧
    (hasRedHorizontal (indexThick parent) = true →
      hasRedHorizontal (indexThick (southwestChild parent)) = true ∧
      hasRedHorizontal (indexThick (southeastChild parent)) = true) ∧
    (hasRedVertical (indexThick parent) = true →
      hasRedVertical (indexThick (southwestChild parent)) = true ∧
      hasRedVertical (indexThick (northwestChild parent)) = true) := by
  have hparent := List.all_eq_true.1 allRedCycleExpansionRulesBool_eq_true
    parent (List.mem_finRange parent)
  exact of_decide_eq_true hparent

theorem southwestChild_thick_a {parent : Index} (h : indexThick parent = .a) :
    indexThick (southwestChild parent) = .a :=
  (redCycleExpansionRules parent).1 h

theorem southwestChild_thick_b {parent : Index} (h : indexThick parent = .b) :
    indexThick (southwestChild parent) = .b :=
  (redCycleExpansionRules parent).2.1 h

theorem southwestChild_thick_c {parent : Index} (h : indexThick parent = .c) :
    indexThick (southwestChild parent) = .c :=
  (redCycleExpansionRules parent).2.2.1 h

theorem southwestChild_thick_d {parent : Index} (h : indexThick parent = .d) :
    indexThick (southwestChild parent) = .d :=
  (redCycleExpansionRules parent).2.2.2.1 h

theorem southeastChild_redHorizontal_of_thick_a {parent : Index}
    (h : indexThick parent = .a) :
    hasRedHorizontal (indexThick (southeastChild parent)) = true :=
  (redCycleExpansionRules parent).2.2.2.2.1 h

theorem southeastChild_redHorizontal_of_thick_b {parent : Index}
    (h : indexThick parent = .b) :
    hasRedHorizontal (indexThick (southeastChild parent)) = true :=
  ((redCycleExpansionRules parent).2.2.2.2.2.1 h).1

theorem northwestChild_redVertical_of_thick_b {parent : Index}
    (h : indexThick parent = .b) :
    hasRedVertical (indexThick (northwestChild parent)) = true :=
  ((redCycleExpansionRules parent).2.2.2.2.2.1 h).2

theorem northwestChild_redVertical_of_thick_c {parent : Index}
    (h : indexThick parent = .c) :
    hasRedVertical (indexThick (northwestChild parent)) = true :=
  (redCycleExpansionRules parent).2.2.2.2.2.2.1 h

theorem redHorizontal_children {parent : Index}
    (h : hasRedHorizontal (indexThick parent) = true) :
    hasRedHorizontal (indexThick (southwestChild parent)) = true ∧
      hasRedHorizontal (indexThick (southeastChild parent)) = true :=
  (redCycleExpansionRules parent).2.2.2.2.2.2.2.1 h

theorem redVertical_children {parent : Index}
    (h : hasRedVertical (indexThick parent) = true) :
    hasRedVertical (indexThick (southwestChild parent)) = true ∧
      hasRedVertical (indexThick (northwestChild parent)) = true :=
  (redCycleExpansionRules parent).2.2.2.2.2.2.2.2 h

end RedCycles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
