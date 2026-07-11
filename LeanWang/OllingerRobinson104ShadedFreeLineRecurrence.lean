/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineGraphBase

/-!
The semantic Figure 18 free-line recurrence.

This module fixes the exact proposition propagated by Robinson's periodicity
argument. The finite graph audit proves depth one. One whole-pattern successor
lemma will therefore imply free grids of unbounded size at every depth.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineRecurrence

open RedCycles RedShadeCycles RedShadePaths ShadedFreeGrid ShadedFreeLineGraphBase
  ShadedFreeLineOffsets ShadedPlaneSignalGrid Signals.FreeCellLocal

set_option maxRecDepth 100000

inductive Phase where
  | even
  | odd
deriving DecidableEq, Repr

def Phase.factor : Phase → Nat
  | .even => 1
  | .odd => 2

def Phase.extra : Phase → Nat
  | .even => 0
  | .odd => 1

def scale (phase : Phase) (depth : Nat) : Nat :=
  phase.factor * 4 ^ depth

def refinementDepth (phase : Phase) (depth : Nat) : Nat :=
  2 * depth + phase.extra + 2

def localGrid (phase : Phase) (depth : Nat) (parent : Index) : Nat → Nat → Index :=
  iterateRefine (refinementDepth phase depth) (fun _ _ => parent)

def west (phase : Phase) (depth : Nat) : Nat := scale phase depth

def east (phase : Phase) (depth : Nat) : Nat := 3 * scale phase depth

def quarterStart (phase : Phase) (depth : Nat) : Nat :=
  quarterWest (west phase depth)

def offsetAt (phase : Phase) (depth : Nat)
    (index : Fin (freeOffsets depth).length) : Nat :=
  phase.factor * offsetAtDepth depth index

/-- Every recursive candidate row and column is semantically free. -/
def OffsetsFree (phase : Phase) (depth : Nat) (parent : Index)
    (stateGrid : Nat → Nat → RedShades.State) : Prop :=
  (∀ index : Fin (freeOffsets depth).length,
    IsFreeColumn (localGrid phase depth parent) stateGrid
      (west phase depth) (east phase depth)
      (quarterStart phase depth + offsetAt phase depth index)) ∧
  (∀ index : Fin (freeOffsets depth).length,
    IsFreeRow (localGrid phase depth parent) stateGrid
      (west phase depth) (east phase depth)
      (quarterStart phase depth + offsetAt phase depth index))

/-- Uniform recurrence claim at one depth. -/
def Holds (phase : Phase) (depth : Nat) : Prop :=
  ∀ (parent : Index) (stateGrid : Nat → Nat → RedShades.State),
    ValidShadeGrid (localGrid phase depth parent) stateGrid →
    CycleShade stateGrid (west phase depth) (east phase depth)
      (west phase depth) (east phase depth) .light →
    OffsetsFree phase depth parent stateGrid

set_option maxHeartbeats 1000000 in
-- Normalizing the translated audited grid through the abstract recurrence coordinates.
/-- The exhaustive first-level graph certificates establish the recurrence base. -/
theorem holds_even_one : Holds .even 1 := by
  intro parent stateGrid valid shaded
  let grid : Nat → Nat → Index := fun _ _ => parent
  have hshift : RefinementTranslation.shiftGrid grid 0 0 = grid := by
    funext x y
    simp [RefinementTranslation.shiftGrid, grid]
  have localValid : ValidShadeGrid
      (iterateRefine 4 (RefinementTranslation.shiftGrid grid 0 0)) stateGrid := by
    rw [hshift]
    simpa [localGrid, refinementDepth, Phase.extra, grid] using valid
  have localShaded : CycleShade stateGrid 4 12 4 12 .light := by
    simpa [west, east, scale, Phase.factor] using shaded
  constructor
  · intro index
    have free := freeColumn_offsetAtDepth_one_shift grid 0 0 rfl
      localValid localShaded index
    rw [hshift] at free
    simpa [localGrid, refinementDepth, quarterStart, west, east, scale,
      offsetAt, Phase.factor, Phase.extra, quarterWest, grid]
      using free
  · intro index
    have free := freeRow_offsetAtDepth_one_shift grid 0 0 rfl
      localValid localShaded index
    rw [hshift] at free
    simpa [localGrid, refinementDepth, quarterStart, west, east, scale,
      offsetAt, Phase.factor, Phase.extra, quarterWest, grid]
      using free

/-- Semantic offsets package into the ordered grid used by routing. -/
def freeGridOfOffsetsFree
    {phase : Phase} {depth : Nat} {parent : Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (free : OffsetsFree phase depth parent stateGrid) :
    FreeGrid (localGrid phase depth parent) stateGrid
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (freeOffsets depth).length where
  columnAt := fun index => quarterStart phase depth + offsetAt phase depth index
  rowAt := fun index => quarterStart phase depth + offsetAt phase depth index
  column_strictMono := by
    intro first second hlt
    have hmono := offsetAtDepth_strictMono depth hlt
    cases phase <;> simp [offsetAt, Phase.factor] <;> omega
  row_strictMono := by
    intro first second hlt
    have hmono := offsetAtDepth_strictMono depth hlt
    cases phase <;> simp [offsetAt, Phase.factor] <;> omega
  column_west := by
    intro index
    have hpositive := (offsetAtDepth_bounds depth index).1
    cases phase <;>
      simp [quarterStart, west, scale, offsetAt, Phase.factor, quarterWest] <;>
      omega
  column_east := by
    intro index
    have hbound := offsetAtDepth_lt_last depth index
    rw [pow_succ] at hbound
    cases phase <;>
      simp [quarterStart, west, east, scale, offsetAt, Phase.factor,
        quarterWest, quarterEast] <;>
      omega
  row_south := by
    intro index
    have hpositive := (offsetAtDepth_bounds depth index).1
    cases phase <;>
      simp [quarterStart, west, scale, offsetAt, Phase.factor,
        quarterWest, quarterSouth] <;>
      omega
  row_north := by
    intro index
    have hbound := offsetAtDepth_lt_last depth index
    rw [pow_succ] at hbound
    cases phase <;>
      simp [quarterStart, west, east, scale, offsetAt, Phase.factor,
        quarterWest, quarterNorth] <;>
      omega
  freeColumn := free.1
  freeRow := free.2

/-- Robinson periodicity at one step is the sole remaining recurrence lemma. -/
def PeriodicStep : Prop :=
  ∀ phase depth, 1 ≤ depth → Holds phase depth → Holds phase (depth + 1)

set_option maxHeartbeats 1000000 in
-- Unfolding the higher-order `Holds` predicate through the dependent induction.
theorem holds_all (phase : Phase) (base : Holds phase 1)
    (step : PeriodicStep) :
    ∀ depth, 1 ≤ depth → Holds phase depth := by
  intro depth hdepth
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hdepth
  induction extra with
  | zero => simpa using base
  | succ extra ih =>
      rw [show 1 + (extra + 1) = (1 + extra) + 1 by omega]
      exact step phase (1 + extra) (by omega) (ih (by omega))

end ShadedFreeLineRecurrence
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
