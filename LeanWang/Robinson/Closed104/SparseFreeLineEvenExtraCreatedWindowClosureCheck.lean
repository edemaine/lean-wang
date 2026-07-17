/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.SparseFreeLineEvenExtraCreatedWindowAudit

/-!
# Closed finite quotient for recursive created-segment windows

Vertical exceptional windows refine at horizontal residues `0..3` and fixed
vertical residue `0`; horizontal windows obey the dual recurrence.  One closure
step expands each 32-state base family to a stable 92-state quotient.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraCreatedWindowClosure

open RedCycles RedShadeGraphRefinement ShadedFreeLineRecurrence
  Signals.FreeCellLocal SparseFreeLineEvenExtraCreatedWindowAudit

def canonicalWindow (window : Window) : Window :=
  window.map BorderSubstitution.canonicalIndex

def refineWindow (window : Window) (residueX residueY : Nat) : Window :=
  let refined := iterateRefine 2 (windowGrid window)
  (List.range 3).flatMap fun y =>
    (List.range 3).map fun x => refined (residueX + x) (residueY + y)

def verticalBaseWindows : List Window :=
  ((List.finRange 104).flatMap fun parent =>
    (List.range 9).map fun delta =>
      canonicalWindow (windowAt parent (4 + delta) 9)).eraseDups

def horizontalBaseWindows : List Window :=
  ((List.finRange 104).flatMap fun parent =>
    (List.range 9).map fun delta =>
      canonicalWindow (windowAt parent 9 (4 + delta))).eraseDups

def closeVertical (windows : List Window) : List Window :=
  (windows ++ windows.flatMap fun window =>
    (List.range 4).map fun residueX =>
      canonicalWindow (refineWindow window residueX 0)).eraseDups

def closeHorizontal (windows : List Window) : List Window :=
  (windows ++ windows.flatMap fun window =>
    (List.range 4).map fun residueY =>
      canonicalWindow (refineWindow window 0 residueY)).eraseDups

def verticalClosed : List Window := closeVertical verticalBaseWindows

def horizontalClosed : List Window := closeHorizontal horizontalBaseWindows

set_option linter.style.nativeDecide false in
theorem vertical_closed : closeVertical verticalClosed = verticalClosed := by
  native_decide

set_option linter.style.nativeDecide false in
theorem horizontal_closed : closeHorizontal horizontalClosed = horizontalClosed := by
  native_decide

def verticalCases : List (Window × Nat) :=
  (verticalClosed.flatMap fun window =>
    let p := windowGrid window 1 1
    ([4, 5] : List Nat).filterMap fun x =>
      let required := (Signals.verticalInterior?
        (componentAt (fineGrid p) x 0) (quadrantAt x 0)).isSome
      if required && !SparseFreeLineLocalStates.verticalAncestorAt 0 0 p x then
        some (window, x)
      else none).eraseDups

def horizontalCases : List (Window × Nat) :=
  (horizontalClosed.flatMap fun window =>
    let p := windowGrid window 1 1
    ([4, 5] : List Nat).filterMap fun y =>
      let required := (Signals.horizontalInterior?
        (componentAt (fineGrid p) 0 y) (quadrantAt 0 y)).isSome
      if required && !SparseFreeLineLocalStates.horizontalAncestorAt 0 0 p y then
        some (window, y)
      else none).eraseDups

set_option linter.style.nativeDecide false in
theorem vertical_routes_complete :
    verticalCases.all
      SparseFreeLineEvenExtraCreatedWindowAudit.verticalCaseCheck = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem horizontal_routes_complete :
    horizontalCases.all
      SparseFreeLineEvenExtraCreatedWindowAudit.horizontalCaseCheck = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem quotient_lengths :
    verticalBaseWindows.length = 36 ∧ verticalClosed.length = 104 ∧
      verticalCases.length = 104 ∧ horizontalBaseWindows.length = 36 ∧
      horizontalClosed.length = 104 ∧ horizontalCases.length = 104 := by
  native_decide

end SparseFreeLineEvenExtraCreatedWindowClosure
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
