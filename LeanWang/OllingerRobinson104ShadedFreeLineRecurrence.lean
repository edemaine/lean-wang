/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineGraphBase
import LeanWang.OllingerRobinson104ShadedFreeLinePatternRefinement

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
  ShadedFreeLineGraph ShadedFreeLinePatternRefinement
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

def lineCoordinate (phase : Phase) (depth offset : Nat) : Nat :=
  quarterStart phase depth + phase.factor * offset

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

/-- Row and column paths retained for the recursive geometric argument. -/
def GraphHolds (phase : Phase) (depth : Nat) : Prop :=
  ∀ parent : Index,
    (∀ offset ∈ freeOffsets depth,
      RowCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset)) ∧
    (∀ offset ∈ freeOffsets depth,
      ColumnCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset))

theorem two_pow_refinementLevel_eq_scale (phase : Phase) (depth : Nat) :
    2 ^ (2 * depth + phase.extra) = scale phase depth := by
  cases phase
  · simp [Phase.extra, scale, Phase.factor, pow_mul]
  · rw [show 2 * depth + Phase.odd.extra = 2 * depth + 1 by rfl,
      pow_add, pow_mul]
    simp [scale, Phase.factor, mul_comm]

theorem canonicalCycle (phase : Phase) (depth : Nat) (parent : Index) :
    OrientedRedCycles.CycleOn (localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth) := by
  have cycle := OrientedRedBoardTranslations.at_scale
    (fun _ _ => parent) (2 * depth + phase.extra) 0 0
  rw [two_pow_refinementLevel_eq_scale] at cycle
  simpa [localGrid, refinementDepth, west, east, mul_comm] using cycle

/-- Retained graph certificates imply the semantic free-line invariant. -/
theorem holds_of_graphHolds {phase : Phase} {depth : Nat}
    (graph : GraphHolds phase depth) : Holds phase depth := by
  intro parent stateGrid valid shaded
  have cycle := canonicalCycle phase depth parent
  have certificates := graph parent
  constructor
  · intro index
    apply isFreeColumn_of_certificate valid cycle shaded
    simpa [lineCoordinate, offsetAt] using
      certificates.2 (offsetAtDepth depth index) (offsetAtDepth_mem depth index)
  · intro index
    apply isFreeRow_of_certificate valid cycle shaded
    simpa [lineCoordinate, offsetAt] using
      certificates.1 (offsetAtDepth depth index) (offsetAtDepth_mem depth index)

/-- The checked even base retains the paths needed by later refinements. -/
theorem graphHolds_even_one : GraphHolds .even 1 := by
  intro parent
  constructor
  · intro offset mem
    simpa [localGrid, ShadedFreeLineGraphBase.localGrid,
      refinementDepth, Phase.extra, west, east, scale,
      Phase.factor, lineCoordinate, quarterStart, quarterWest] using
      ShadedFreeLineGraphBase.rowCertificate parent mem
  · intro offset mem
    simpa [localGrid, ShadedFreeLineGraphBase.localGrid,
      refinementDepth, Phase.extra, west, east, scale,
      Phase.factor, lineCoordinate, quarterStart, quarterWest] using
      ShadedFreeLineGraphBase.columnCertificate parent mem

/-- The exhaustive first-level graph certificates establish the recurrence base. -/
theorem holds_even_one : Holds .even 1 :=
  holds_of_graphHolds graphHolds_even_one

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

/-- Graph-level recurrence, before shade semantics are discarded. -/
def GraphPeriodicStep : Prop :=
  ∀ phase depth, GraphHolds phase depth → GraphHolds phase (depth + 1)

theorem scale_succ (phase : Phase) (depth : Nat) :
    scale phase (depth + 1) = 4 * scale phase depth := by
  simp [scale, pow_succ]
  ac_rfl

theorem west_succ (phase : Phase) (depth : Nat) :
    west phase (depth + 1) = 4 * west phase depth := by
  simp [west, scale_succ]

theorem east_succ (phase : Phase) (depth : Nat) :
    east phase (depth + 1) = 4 * east phase depth := by
  rw [east, east, scale_succ]
  ac_rfl

theorem localGrid_succ (phase : Phase) (depth : Nat) (parent : Index) :
    localGrid phase (depth + 1) parent =
      iterateRefine 2 (localGrid phase depth parent) := by
  unfold localGrid
  rw [show refinementDepth phase (depth + 1) =
      2 + refinementDepth phase depth by
    simp [refinementDepth]
    omega]
  exact (PlaneRedBoards.iterateRefine_add 2
    (refinementDepth phase depth) (fun _ _ => parent)).symm

/-- Concrete whole-pattern projections are exactly the remaining graph step. -/
def ProjectionStep : Prop :=
  ∀ phase depth parent,
    (∀ offset ∈ freeOffsets depth,
      RowCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset)) →
    (∀ offset ∈ freeOffsets depth,
      ColumnCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset)) →
    PatternProjection (localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (freeOffsets (depth + 1)) (lineCoordinate phase (depth + 1))

theorem graphPeriodicStep_of_projectionStep
    (projection : ProjectionStep) : GraphPeriodicStep := by
  intro phase depth graph parent
  have old := graph parent
  have projected := projection phase depth parent old.1 old.2
  have certificates := certificates_of_projection projected
  constructor
  · intro offset mem
    simpa [localGrid_succ, west_succ, east_succ] using
      certificates.1 offset mem
  · intro offset mem
    simpa [localGrid_succ, west_succ, east_succ] using
      certificates.2 offset mem

theorem graphHolds_from (phase : Phase) (baseDepth : Nat)
    (base : GraphHolds phase baseDepth) (step : GraphPeriodicStep) :
    ∀ extra, GraphHolds phase (baseDepth + extra) := by
  intro extra
  induction extra with
  | zero => simpa
  | succ extra ih =>
      rw [show baseDepth + (extra + 1) = (baseDepth + extra) + 1 by omega]
      exact step phase (baseDepth + extra) ih

end ShadedFreeLineRecurrence
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
