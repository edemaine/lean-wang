/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCreatedPositions

/-!
# Finite neighboring-window routes for created exceptional segments

The exceptional sparse row and column can create live segments only at local
coordinates `4` and `5`.  A single macrocell does not connect all such
segments to its red cycle.  This audit searches the surrounding `3 x 3`
coarse-cell window and checks the finitely many distinct created obligations.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraCreatedWindowAudit

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  RedShadeGraphWeightedSearch RedShadeGraphTranslation
  ShadedFreeLineProjectionSourceLists ShadedFreeLineRecurrence
  Signals.FreeCellLocal
  SparseFreeLineLocalStates SparseFreeLineEvenExtraCreatedPositions

abbrev Window := List Index

def windowGrid (window : Window) (x y : Nat) : Index :=
  (window[y * 3 + x]?).getD 0

def windowAt (parent : Index) (blockX blockY : Nat) : Window :=
  let grid := localGrid .even 1 parent
  (List.range 3).flatMap fun y =>
    (List.range 3).map fun x => grid (blockX - 1 + x) (blockY - 1 + y)

def cellCycleStarts (x y : Nat) : List WeightedStart :=
  (cyclePorts (4 * x + 1) (4 * x + 3)
    (4 * y + 1) (4 * y + 3)).map fun port => ⟨port, false⟩

def windowStarts (_window : Window) : List WeightedStart :=
  (List.range 3).flatMap fun y =>
    (List.range 3).flatMap fun x => cellCycleStarts x y

def windowNodes (window : Window) : List ReachNode :=
  exploreFastWeightedReach (iterateRefine 2 (windowGrid window)) 24 24 20000
    (windowStarts window)

def reached (window : Window) (nodes : List ReachNode) (target : Port) : Bool :=
  portPresent (iterateRefine 2 (windowGrid window)) target &&
    nodes.any fun node => node.parity && decide (node.current = target)

def verticalCases : List (Window × Nat) :=
  ((List.finRange 104).flatMap fun parent =>
    (List.range 8).flatMap fun delta =>
      let blockX := 4 + delta
      let p := localGrid .even 1 parent blockX 9
      ([4, 5] : List Nat).filterMap fun x =>
        let required := (Signals.verticalInterior?
          (componentAt (fineGrid p) x 0) (quadrantAt x 0)).isSome
        if required && !verticalAncestorAt 0 0 p x then
          some (windowAt parent blockX 9, x)
        else none).eraseDups

def verticalCaseCheck (entry : Window × Nat) : Bool :=
  let window := entry.1
  let x := entry.2
  let nodes := windowNodes window
  reached window nodes ⟨8 + x, 8, .south⟩ ||
    reached window nodes ⟨8 + x, 8, .north⟩

theorem verticalCaseCheck_eq (entry : Window × Nat) :
    verticalCaseCheck entry =
      (reached entry.1 (windowNodes entry.1) ⟨8 + entry.2, 8, .south⟩ ||
       reached entry.1 (windowNodes entry.1) ⟨8 + entry.2, 8, .north⟩) := rfl

def horizontalCases : List (Window × Nat) :=
  ((List.finRange 104).flatMap fun parent =>
    (List.range 8).flatMap fun delta =>
      let blockY := 4 + delta
      let p := localGrid .even 1 parent 9 blockY
      ([4, 5] : List Nat).filterMap fun y =>
        let required := (Signals.horizontalInterior?
          (componentAt (fineGrid p) 0 y) (quadrantAt 0 y)).isSome
        if required && !horizontalAncestorAt 0 0 p y then
          some (windowAt parent 9 blockY, y)
        else none).eraseDups

def horizontalCaseCheck (entry : Window × Nat) : Bool :=
  let window := entry.1
  let y := entry.2
  let nodes := windowNodes window
  reached window nodes ⟨8, 8 + y, .west⟩ ||
    reached window nodes ⟨8, 8 + y, .east⟩

theorem horizontalCaseCheck_eq (entry : Window × Nat) :
    horizontalCaseCheck entry =
      (reached entry.1 (windowNodes entry.1) ⟨8, 8 + entry.2, .west⟩ ||
       reached entry.1 (windowNodes entry.1) ⟨8, 8 + entry.2, .east⟩) := rfl

set_option linter.style.nativeDecide false in
theorem vertical_complete : verticalCases.all verticalCaseCheck = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem horizontal_complete : horizontalCases.all horizontalCaseCheck = true := by
  native_decide

end SparseFreeLineEvenExtraCreatedWindowAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
