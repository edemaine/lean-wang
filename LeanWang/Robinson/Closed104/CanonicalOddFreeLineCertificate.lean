/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalOddFreeLineChecks

/-! Proof-facing projections of the odd canonical free-line certificate. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddFreeLineCertificate

open CanonicalOddFreeLineData

private theorem check_of_mem {check : Bool} (hcheck : check ∈ checks) :
    check = true :=
  List.all_eq_true.1 complete_eq_true check hcheck

theorem rowClearComplete_eq_true : rowClearComplete = true :=
  check_of_mem (by simp [checks])

theorem columnClearComplete_eq_true : columnClearComplete = true :=
  check_of_mem (by simp [checks])

theorem stripTransitionsComplete_eq_true : stripTransitionsComplete = true :=
  check_of_mem (by simp [checks])

theorem baseComplete_eq_true : baseComplete = true :=
  check_of_mem (by simp [checks])

theorem rootCycleComplete_eq_true : rootCycleComplete = true :=
  check_of_mem (by simp [checks])

theorem rowEven_clear {node : Nat} (hnode : node ∈ rowEven) :
    CanonicalFreeLine.rawRowClear node 1 = true := by
  have checked := rowClearComplete_eq_true
  simp only [rowClearComplete, Bool.and_eq_true] at checked
  exact List.all_eq_true.1 checked.1 node hnode

theorem rowOdd_clear {node : Nat} (hnode : node ∈ rowOdd) :
    CanonicalFreeLine.rawRowClear node 1 = true := by
  have checked := rowClearComplete_eq_true
  simp only [rowClearComplete, Bool.and_eq_true] at checked
  exact List.all_eq_true.1 checked.2 node hnode

theorem columnEven_clear {node : Nat} (hnode : node ∈ columnEven) :
    CanonicalFreeLine.rawColumnClear node 1 = true := by
  have checked := columnClearComplete_eq_true
  simp only [columnClearComplete, Bool.and_eq_true] at checked
  exact List.all_eq_true.1 checked.1 node hnode

theorem columnOdd_clear {node : Nat} (hnode : node ∈ columnOdd) :
    CanonicalFreeLine.rawColumnClear node 1 = true := by
  have checked := columnClearComplete_eq_true
  simp only [columnClearComplete, Bool.and_eq_true] at checked
  exact List.all_eq_true.1 checked.2 node hnode

private theorem stripTransition_complete (axis : StripAxis)
    {transition : StripTransition} (htransition : transition ∈ stripTransitions) :
    stripTransitionComplete axis transition = true := by
  have checked := stripTransitionsComplete_eq_true
  simp only [stripTransitionsComplete] at checked
  have axisChecked := List.all_eq_true.1 checked axis (by
    cases axis <;> simp)
  exact List.all_eq_true.1 axisChecked transition htransition

theorem interior_child {axis : StripAxis} {transition : StripTransition}
    (htransition : transition ∈ stripTransitions) {node localAlong child : Nat}
    (hnode : node ∈ interiorClass axis transition.source)
    (hlocalAlong : localAlong < 4)
    (hchild : childAtAxis? axis node localAlong transition.localFixed =
      some child) :
    child ∈ interiorClass axis transition.target := by
  have checked := stripTransition_complete axis htransition
  simp only [stripTransitionComplete, Bool.and_eq_true] at checked
  have nodeCheck := List.all_eq_true.1 checked.1.1 node hnode
  have childCheck := List.all_eq_true.1 nodeCheck localAlong (by
    simpa using hlocalAlong)
  rw [hchild] at childCheck
  simpa using childCheck

theorem boundary_child {axis : StripAxis} {transition : StripTransition}
    (htransition : transition ∈ stripTransitions) {node child : Nat}
    (hnode : node ∈ boundaryClass axis transition.source)
    (hchild : childAtAxis? axis node 0 transition.localFixed = some child) :
    child ∈ boundaryClass axis transition.target := by
  have checked := stripTransition_complete axis htransition
  simp only [stripTransitionComplete, Bool.and_eq_true] at checked
  have nodeCheck := List.all_eq_true.1 checked.1.2 node hnode
  rw [hchild] at nodeCheck
  simpa using nodeCheck

theorem boundary_enters {axis : StripAxis} {transition : StripTransition}
    (htransition : transition ∈ stripTransitions) {node localAlong child : Nat}
    (hnode : node ∈ boundaryClass axis transition.source)
    (hlocalAlongPositive : 0 < localAlong) (hlocalAlong : localAlong < 4)
    (hchild : childAtAxis? axis node localAlong transition.localFixed =
      some child) :
    child ∈ interiorClass axis transition.target := by
  have checked := stripTransition_complete axis htransition
  simp only [stripTransitionComplete, Bool.and_eq_true] at checked
  have nodeCheck := List.all_eq_true.1 checked.2 node hnode
  have offsetMem : localAlong - 1 ∈ List.range 3 := by
    simp only [List.mem_range]
    omega
  have childCheck := List.all_eq_true.1 nodeCheck (localAlong - 1) offsetMem
  rw [show localAlong - 1 + 1 = localAlong by omega, hchild] at childCheck
  simpa using childCheck

theorem base_row_interior (x : Nat) (hxLower : 3 ≤ x) (hxUpper : x < 6) :
    optionIn (seedNodeAt? x 4) rowEven = true := by
  have checked := baseComplete_eq_true
  simp only [baseComplete, Bool.and_eq_true] at checked
  have offsetMem : x - 3 ∈ List.range 3 := by
    simp only [List.mem_range]
    omega
  have result := List.all_eq_true.1 checked.1.1.1 (x - 3) offsetMem
  simpa [show x - 3 + 3 = x by omega] using result

theorem base_row_boundary : optionIn (seedNodeAt? 2 4) rowBoundaryEven = true := by
  have checked := baseComplete_eq_true
  simp only [baseComplete, Bool.and_eq_true] at checked
  exact checked.1.1.2

theorem base_column_interior (y : Nat) (hyLower : 3 ≤ y) (hyUpper : y < 6) :
    optionIn (seedNodeAt? 4 y) columnEven = true := by
  have checked := baseComplete_eq_true
  simp only [baseComplete, Bool.and_eq_true] at checked
  have offsetMem : y - 3 ∈ List.range 3 := by
    simp only [List.mem_range]
    omega
  have result := List.all_eq_true.1 checked.1.2 (y - 3) offsetMem
  simpa [show y - 3 + 3 = y by omega] using result

theorem base_column_boundary :
    optionIn (seedNodeAt? 4 2) columnBoundaryEven = true := by
  have checked := baseComplete_eq_true
  simp only [baseComplete, Bool.and_eq_true] at checked
  exact checked.2

theorem rootCycle_light : CanonicalFreeLine.oddRootCycleLight seed = true := by
  simpa [rootCycleComplete] using rootCycleComplete_eq_true

end CanonicalOddFreeLineCertificate
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
