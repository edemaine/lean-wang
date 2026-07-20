/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedCycles

/-!
# Local expansion of red cycles

The thick component of each corrected tile describes the red Robinson lines.
After one substitution, the southwest child preserves a parent corner or line,
while the southeast and northwest children supply the next horizontal and
vertical pieces.  These are precisely the local facts needed to double a
rectangular red cycle.

Because there are only 104 parents, the conjunction is checked once by
`native_decide`; the named theorems below are proof-facing projections used by
the coordinate-level expansion in `RedCycleScaling`.
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

/- Finite audit of the local facts that double a red rectangular cycle. -/
set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
private theorem allRedCycleExpansionRules :
    ∀ parent : Index,
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
      hasRedVertical (indexThick (northwestChild parent)) = true) :=
  allRedCycleExpansionRules parent

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
