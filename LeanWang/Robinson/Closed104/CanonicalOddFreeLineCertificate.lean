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

theorem rowTransitionsComplete_eq_true : rowTransitionsComplete = true :=
  check_of_mem (by simp [checks])

theorem columnTransitionsComplete_eq_true :
    columnTransitionsComplete = true :=
  check_of_mem (by simp [checks])

theorem rowBoundaryComplete_eq_true : rowBoundaryComplete = true :=
  check_of_mem (by simp [checks])

theorem columnBoundaryComplete_eq_true : columnBoundaryComplete = true :=
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

private theorem row_child_of_check {sources targets : List Nat}
    {childY node childX child : Nat}
    (checked : childrenInRowClass sources targets childY = true)
    (hnode : node ∈ sources) (hchildX : childX < 4)
    (hchild : childAt? node childX childY = some child) :
    child ∈ targets := by
  have nodeCheck := List.all_eq_true.1 checked node hnode
  have childCheck := List.all_eq_true.1 nodeCheck childX (by
    simpa using hchildX)
  rw [hchild] at childCheck
  simpa using childCheck

private theorem column_child_of_check {sources targets : List Nat}
    {childX node childY child : Nat}
    (checked : childrenInColumnClass sources targets childX = true)
    (hnode : node ∈ sources) (hchildY : childY < 4)
    (hchild : childAt? node childX childY = some child) :
    child ∈ targets := by
  have nodeCheck := List.all_eq_true.1 checked node hnode
  have childCheck := List.all_eq_true.1 nodeCheck childY (by
    simpa using hchildY)
  rw [hchild] at childCheck
  simpa using childCheck

theorem rowEven_child_zero {node childX child : Nat}
    (hnode : node ∈ rowEven) (hchildX : childX < 4)
    (hchild : childAt? node childX 0 = some child) : child ∈ rowEven := by
  have checked := rowTransitionsComplete_eq_true
  simp only [rowTransitionsComplete, Bool.and_eq_true] at checked
  exact row_child_of_check checked.1.1 hnode hchildX hchild

theorem rowEven_child_one {node childX child : Nat}
    (hnode : node ∈ rowEven) (hchildX : childX < 4)
    (hchild : childAt? node childX 1 = some child) : child ∈ rowOdd := by
  have checked := rowTransitionsComplete_eq_true
  simp only [rowTransitionsComplete, Bool.and_eq_true] at checked
  exact row_child_of_check checked.1.2 hnode hchildX hchild

theorem rowOdd_child_three {node childX child : Nat}
    (hnode : node ∈ rowOdd) (hchildX : childX < 4)
    (hchild : childAt? node childX 3 = some child) : child ∈ rowOdd := by
  have checked := rowTransitionsComplete_eq_true
  simp only [rowTransitionsComplete, Bool.and_eq_true] at checked
  exact row_child_of_check checked.2 hnode hchildX hchild

theorem columnEven_child_zero {node childY child : Nat}
    (hnode : node ∈ columnEven) (hchildY : childY < 4)
    (hchild : childAt? node 0 childY = some child) : child ∈ columnEven := by
  have checked := columnTransitionsComplete_eq_true
  simp only [columnTransitionsComplete, Bool.and_eq_true] at checked
  exact column_child_of_check checked.1.1 hnode hchildY hchild

theorem columnEven_child_one {node childY child : Nat}
    (hnode : node ∈ columnEven) (hchildY : childY < 4)
    (hchild : childAt? node 1 childY = some child) : child ∈ columnOdd := by
  have checked := columnTransitionsComplete_eq_true
  simp only [columnTransitionsComplete, Bool.and_eq_true] at checked
  exact column_child_of_check checked.1.2 hnode hchildY hchild

theorem columnOdd_child_three {node childY child : Nat}
    (hnode : node ∈ columnOdd) (hchildY : childY < 4)
    (hchild : childAt? node 3 childY = some child) : child ∈ columnOdd := by
  have checked := columnTransitionsComplete_eq_true
  simp only [columnTransitionsComplete, Bool.and_eq_true] at checked
  exact column_child_of_check checked.2 hnode hchildY hchild

private theorem boundary_child_of_check {sources targets : List Nat}
    {childX childY node child : Nat}
    (checked : boundaryChildInClass sources targets childX childY = true)
    (hnode : node ∈ sources)
    (hchild : childAt? node childX childY = some child) :
    child ∈ targets := by
  have nodeCheck := List.all_eq_true.1 checked node hnode
  rw [hchild] at nodeCheck
  simpa using nodeCheck

private theorem row_enters_of_check {sources targets : List Nat}
    {childY node childX child : Nat}
    (checked : rowBoundaryEnters sources targets childY = true)
    (hnode : node ∈ sources) (hchildXLower : 0 < childX)
    (hchildXUpper : childX < 4)
    (hchild : childAt? node childX childY = some child) :
    child ∈ targets := by
  have nodeCheck := List.all_eq_true.1 checked node hnode
  have offsetMem : childX - 1 ∈ List.range 3 := by
    simp only [List.mem_range]
    omega
  have childCheck := List.all_eq_true.1 nodeCheck (childX - 1) offsetMem
  rw [show childX - 1 + 1 = childX by omega, hchild] at childCheck
  simpa using childCheck

private theorem column_enters_of_check {sources targets : List Nat}
    {childX node childY child : Nat}
    (checked : columnBoundaryEnters sources targets childX = true)
    (hnode : node ∈ sources) (hchildYLower : 0 < childY)
    (hchildYUpper : childY < 4)
    (hchild : childAt? node childX childY = some child) :
    child ∈ targets := by
  have nodeCheck := List.all_eq_true.1 checked node hnode
  have offsetMem : childY - 1 ∈ List.range 3 := by
    simp only [List.mem_range]
    omega
  have childCheck := List.all_eq_true.1 nodeCheck (childY - 1) offsetMem
  rw [show childY - 1 + 1 = childY by omega, hchild] at childCheck
  simpa using childCheck

theorem rowBoundaryEven_child_zero {node child : Nat}
    (hnode : node ∈ rowBoundaryEven)
    (hchild : childAt? node 0 0 = some child) :
    child ∈ rowBoundaryEven := by
  have checked := rowBoundaryComplete_eq_true
  simp only [rowBoundaryComplete, Bool.and_eq_true] at checked
  exact boundary_child_of_check checked.1.1.1.1.1 hnode hchild

theorem rowBoundaryEven_child_one {node child : Nat}
    (hnode : node ∈ rowBoundaryEven)
    (hchild : childAt? node 0 1 = some child) :
    child ∈ rowBoundaryOdd := by
  have checked := rowBoundaryComplete_eq_true
  simp only [rowBoundaryComplete, Bool.and_eq_true] at checked
  exact boundary_child_of_check checked.1.1.1.1.2 hnode hchild

theorem rowBoundaryOdd_child_three {node child : Nat}
    (hnode : node ∈ rowBoundaryOdd)
    (hchild : childAt? node 0 3 = some child) :
    child ∈ rowBoundaryOdd := by
  have checked := rowBoundaryComplete_eq_true
  simp only [rowBoundaryComplete, Bool.and_eq_true] at checked
  exact boundary_child_of_check checked.1.1.1.2 hnode hchild

theorem rowBoundaryEven_enters_zero {node childX child : Nat}
    (hnode : node ∈ rowBoundaryEven) (hchildXLower : 0 < childX)
    (hchildXUpper : childX < 4)
    (hchild : childAt? node childX 0 = some child) : child ∈ rowEven := by
  have checked := rowBoundaryComplete_eq_true
  simp only [rowBoundaryComplete, Bool.and_eq_true] at checked
  exact row_enters_of_check checked.1.1.2 hnode hchildXLower hchildXUpper hchild

theorem rowBoundaryEven_enters_one {node childX child : Nat}
    (hnode : node ∈ rowBoundaryEven) (hchildXLower : 0 < childX)
    (hchildXUpper : childX < 4)
    (hchild : childAt? node childX 1 = some child) : child ∈ rowOdd := by
  have checked := rowBoundaryComplete_eq_true
  simp only [rowBoundaryComplete, Bool.and_eq_true] at checked
  exact row_enters_of_check checked.1.2 hnode hchildXLower hchildXUpper hchild

theorem rowBoundaryOdd_enters_three {node childX child : Nat}
    (hnode : node ∈ rowBoundaryOdd) (hchildXLower : 0 < childX)
    (hchildXUpper : childX < 4)
    (hchild : childAt? node childX 3 = some child) : child ∈ rowOdd := by
  have checked := rowBoundaryComplete_eq_true
  simp only [rowBoundaryComplete, Bool.and_eq_true] at checked
  exact row_enters_of_check checked.2 hnode hchildXLower hchildXUpper hchild

theorem columnBoundaryEven_child_zero {node child : Nat}
    (hnode : node ∈ columnBoundaryEven)
    (hchild : childAt? node 0 0 = some child) :
    child ∈ columnBoundaryEven := by
  have checked := columnBoundaryComplete_eq_true
  simp only [columnBoundaryComplete, Bool.and_eq_true] at checked
  exact boundary_child_of_check checked.1.1.1.1.1 hnode hchild

theorem columnBoundaryEven_child_one {node child : Nat}
    (hnode : node ∈ columnBoundaryEven)
    (hchild : childAt? node 1 0 = some child) :
    child ∈ columnBoundaryOdd := by
  have checked := columnBoundaryComplete_eq_true
  simp only [columnBoundaryComplete, Bool.and_eq_true] at checked
  exact boundary_child_of_check checked.1.1.1.1.2 hnode hchild

theorem columnBoundaryOdd_child_three {node child : Nat}
    (hnode : node ∈ columnBoundaryOdd)
    (hchild : childAt? node 3 0 = some child) :
    child ∈ columnBoundaryOdd := by
  have checked := columnBoundaryComplete_eq_true
  simp only [columnBoundaryComplete, Bool.and_eq_true] at checked
  exact boundary_child_of_check checked.1.1.1.2 hnode hchild

theorem columnBoundaryEven_enters_zero {node childY child : Nat}
    (hnode : node ∈ columnBoundaryEven) (hchildYLower : 0 < childY)
    (hchildYUpper : childY < 4)
    (hchild : childAt? node 0 childY = some child) : child ∈ columnEven := by
  have checked := columnBoundaryComplete_eq_true
  simp only [columnBoundaryComplete, Bool.and_eq_true] at checked
  exact column_enters_of_check checked.1.1.2 hnode hchildYLower hchildYUpper hchild

theorem columnBoundaryEven_enters_one {node childY child : Nat}
    (hnode : node ∈ columnBoundaryEven) (hchildYLower : 0 < childY)
    (hchildYUpper : childY < 4)
    (hchild : childAt? node 1 childY = some child) : child ∈ columnOdd := by
  have checked := columnBoundaryComplete_eq_true
  simp only [columnBoundaryComplete, Bool.and_eq_true] at checked
  exact column_enters_of_check checked.1.2 hnode hchildYLower hchildYUpper hchild

theorem columnBoundaryOdd_enters_three {node childY child : Nat}
    (hnode : node ∈ columnBoundaryOdd) (hchildYLower : 0 < childY)
    (hchildYUpper : childY < 4)
    (hchild : childAt? node 3 childY = some child) : child ∈ columnOdd := by
  have checked := columnBoundaryComplete_eq_true
  simp only [columnBoundaryComplete, Bool.and_eq_true] at checked
  exact column_enters_of_check checked.2 hnode hchildYLower hchildYUpper hchild

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
