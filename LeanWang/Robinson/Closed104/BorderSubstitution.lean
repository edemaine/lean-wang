/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedBoards

/-!
# The thin/thick border factor substitution

The red-border geometry ignores the black layer. The thick child still depends
on the parent thin component through Figure 16's first L2 summand, so the exact
factor state is the parent thin/thick pair. This module proves agreement of the
factor substitution with the 104-symbol substitution at every depth.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace BorderSubstitution

open RedCycles

set_option maxRecDepth 20000

abbrev State := Figure16.Thin × Figure16.Thick

def indexState (index : Index) : State :=
  ((components index).1, (components index).2.1)

def representative (state : State) : Index :=
  ((List.finRange 104).find? fun index => decide (indexState index = state)).getD 0

def states : List State :=
  ((List.finRange 104).map indexState).eraseDups

set_option linter.style.nativeDecide false in
theorem states_length : states.length = 56 := by
  native_decide

theorem indexState_mem_states (index : Index) : indexState index ∈ states := by
  simp [states]

def canonicalIndex (index : Index) : Index :=
  representative (indexState index)

set_option linter.style.nativeDecide false in
theorem indexState_canonicalIndex (index : Index) :
    indexState (canonicalIndex index) = indexState index := by
  revert index
  native_decide

theorem indexThick_canonicalIndex (index : Index) :
    RedCycles.indexThick (canonicalIndex index) = RedCycles.indexThick index := by
  have state := congrArg Prod.snd (indexState_canonicalIndex index)
  simpa [indexState, RedCycles.indexThick_eq] using state

def canonicalizeGrid (grid : Nat → Nat → Index) : Nat → Nat → Index :=
  fun x y => canonicalIndex (grid x y)

theorem indexThick_canonicalizeGrid (grid : Nat → Nat → Index)
    (x y : Nat) :
    RedCycles.indexThick (canonicalizeGrid grid x y) =
      RedCycles.indexThick (grid x y) :=
  indexThick_canonicalIndex (grid x y)

def child (state : State) (quadrant : Quadrant) : State :=
  indexState (childIndex (representative state) quadrant)

set_option linter.style.nativeDecide false in
theorem indexState_childIndex (parent : Index) (quadrant : Quadrant) :
    indexState (childIndex parent quadrant) =
      child (indexState parent) quadrant := by
  cases quadrant <;> revert parent <;> native_decide

def refineGrid (grid : Nat → Nat → State) : Nat → Nat → State :=
  fun x y => child (grid (x / 2) (y / 2))
    (quadrantOfOffset (parityOffset x) (parityOffset y))

def ofIndexGrid (grid : Nat → Nat → Index) : Nat → Nat → State :=
  fun x y => indexState (grid x y)

theorem ofIndexGrid_refineIndexGrid (grid : Nat → Nat → Index) :
    ofIndexGrid (refineIndexGrid grid) = refineGrid (ofIndexGrid grid) := by
  funext x y
  exact indexState_childIndex _ _

def iterateRefine : Nat → (Nat → Nat → State) → Nat → Nat → State
  | 0, grid => grid
  | depth + 1, grid => refineGrid (iterateRefine depth grid)

theorem ofIndexGrid_iterateRefine (depth : Nat)
    (grid : Nat → Nat → Index) :
    ofIndexGrid (RedCycles.iterateRefine depth grid) =
      iterateRefine depth (ofIndexGrid grid) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change ofIndexGrid
          (refineIndexGrid (RedCycles.iterateRefine depth grid)) =
        refineGrid (iterateRefine depth (ofIndexGrid grid))
      rw [ofIndexGrid_refineIndexGrid, ih]

end BorderSubstitution
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
