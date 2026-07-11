/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineGraphBase
import LeanWang.OllingerRobinson104ShadedFreeLineOddBase
import LeanWang.OllingerRobinson104SparseFreeLineOffsets

/-!
# Reduced graph recurrence for unbounded free grids

This recurrence retains both children of its unique even offset and only the
second child of every odd offset.  It is sufficient for the scaffold theorem
and discards the one coupled odd-child case from the exact recurrence.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineRecurrence

open RedCycles RedShadeCycles RedShadePaths ShadedFreeLineGraph
  ShadedFreeLinePatternRefinement ShadedFreeGrid ShadedFreeLineRecurrence
  ShadedPlaneSignalGrid SparseFreeLineOffsets

set_option maxRecDepth 20000

/-- Live graph certificates for the reduced offset family at one scale. -/
def GraphHolds (phase : Phase) (depth : Nat) : Prop :=
  ∀ parent : Index,
    (∀ offset ∈ offsets depth,
      LiveRowCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset)) ∧
    (∀ offset ∈ offsets depth,
      LiveColumnCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset))

theorem graphHolds_of_full
    {phase : Phase} {depth : Nat}
    (full : ShadedFreeLineRecurrence.GraphHolds phase depth) :
    GraphHolds phase depth := by
  intro parent
  have certificates := full parent
  constructor
  · intro offset hoffset
    exact certificates.1 offset (offsets_mem_freeOffsets depth offset hoffset)
  · intro offset hoffset
    exact certificates.2 offset (offsets_mem_freeOffsets depth offset hoffset)

/-- The checked even base restricts to the reduced family. -/
theorem graphHolds_even_one : GraphHolds .even 1 :=
  graphHolds_of_full ShadedFreeLineRecurrence.graphHolds_even_one

/-- The checked odd base restricts to the reduced family. -/
theorem graphHolds_odd_zero : GraphHolds .odd 0 :=
  graphHolds_of_full ShadedFreeLineOddBase.graphHolds_odd_zero

/-- The sole remaining graph obligation for the reduced recurrence. -/
def ProjectionStep : Prop :=
  ∀ phase depth parent,
    (∀ offset ∈ offsets depth,
      LiveRowCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset)) →
    (∀ offset ∈ offsets depth,
      LiveColumnCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset)) →
    (∀ offset ∈ offsets (depth + 1),
      LiveRowCertificate (localGrid phase (depth + 1) parent)
        (west phase (depth + 1)) (east phase (depth + 1))
        (west phase (depth + 1)) (east phase (depth + 1))
        (lineCoordinate phase (depth + 1) offset)) ∧
    (∀ offset ∈ offsets (depth + 1),
      LiveColumnCertificate (localGrid phase (depth + 1) parent)
        (west phase (depth + 1)) (east phase (depth + 1))
        (west phase (depth + 1)) (east phase (depth + 1))
        (lineCoordinate phase (depth + 1) offset))

/-- Every retained child inherits row and column certificates from its parent line. -/
def ChildStep : Prop :=
  ∀ phase depth parent offset child,
    offset ∈ offsets depth →
    child ∈ children offset →
    LiveRowCertificate (localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth offset) →
    LiveColumnCertificate (localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth offset) →
    LiveRowCertificate (localGrid phase (depth + 1) parent)
      (west phase (depth + 1)) (east phase (depth + 1))
      (west phase (depth + 1)) (east phase (depth + 1))
      (lineCoordinate phase (depth + 1) child) ∧
    LiveColumnCertificate (localGrid phase (depth + 1) parent)
      (west phase (depth + 1)) (east phase (depth + 1))
      (west phase (depth + 1)) (east phase (depth + 1))
      (lineCoordinate phase (depth + 1) child)

/-- The main child of every retained line. -/
def MainChildStep : Prop :=
  ∀ phase depth parent offset,
    offset ∈ offsets depth →
    LiveRowCertificate (localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth offset) →
    LiveColumnCertificate (localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth offset) →
    LiveRowCertificate (localGrid phase (depth + 1) parent)
      (west phase (depth + 1)) (east phase (depth + 1))
      (west phase (depth + 1)) (east phase (depth + 1))
      (lineCoordinate phase (depth + 1) (mainChild offset)) ∧
    LiveColumnCertificate (localGrid phase (depth + 1) parent)
      (west phase (depth + 1)) (east phase (depth + 1))
      (west phase (depth + 1)) (east phase (depth + 1))
      (lineCoordinate phase (depth + 1) (mainChild offset))

/-- The second child of the unique even line. -/
def ExtraChildStep : Prop :=
  ∀ phase depth parent offset,
    offset ∈ offsets depth →
    offset % 2 = 0 →
    LiveRowCertificate (localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth offset) →
    LiveColumnCertificate (localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth offset) →
    LiveRowCertificate (localGrid phase (depth + 1) parent)
      (west phase (depth + 1)) (east phase (depth + 1))
      (west phase (depth + 1)) (east phase (depth + 1))
      (lineCoordinate phase (depth + 1) (extraChild offset)) ∧
    LiveColumnCertificate (localGrid phase (depth + 1) parent)
      (west phase (depth + 1)) (east phase (depth + 1))
      (west phase (depth + 1)) (east phase (depth + 1))
      (lineCoordinate phase (depth + 1) (extraChild offset))

/-- The extra-child obligation specialized to the unique even pivot. -/
def PivotExtraStep : Prop :=
  ∀ phase depth parent,
    LiveRowCertificate (localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth (pivot depth)) →
    LiveColumnCertificate (localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth (pivot depth)) →
    LiveRowCertificate (localGrid phase (depth + 1) parent)
      (west phase (depth + 1)) (east phase (depth + 1))
      (west phase (depth + 1)) (east phase (depth + 1))
      (lineCoordinate phase (depth + 1) (extraChild (pivot depth))) ∧
    LiveColumnCertificate (localGrid phase (depth + 1) parent)
      (west phase (depth + 1)) (east phase (depth + 1))
      (west phase (depth + 1)) (east phase (depth + 1))
      (lineCoordinate phase (depth + 1) (extraChild (pivot depth)))

theorem extraChildStep_of_pivot (extra : PivotExtraStep) : ExtraChildStep := by
  intro phase depth parent offset hold heven row column
  have hoffset := even_offset_eq_pivot depth hold heven
  subst offset
  exact extra phase depth parent row column

theorem childStep_of_main_of_extra
    (main : MainChildStep) (extra : ExtraChildStep) : ChildStep := by
  intro phase depth parent offset child hold hchild row column
  rcases mem_children_cases hchild with rfl | ⟨heven, rfl⟩
  · exact main phase depth parent offset hold row column
  · exact extra phase depth parent offset hold heven row column

theorem projectionStep_of_childStep (childrenProject : ChildStep) :
    ProjectionStep := by
  intro phase depth parent rows columns
  constructor
  · intro offset hoffset
    rcases mem_offsets_succ_cases depth hoffset with
      ⟨oldOffset, hold, hchild⟩
    exact (childrenProject phase depth parent oldOffset offset hold hchild
      (rows oldOffset hold) (columns oldOffset hold)).1
  · intro offset hoffset
    rcases mem_offsets_succ_cases depth hoffset with
      ⟨oldOffset, hold, hchild⟩
    exact (childrenProject phase depth parent oldOffset offset hold hchild
      (rows oldOffset hold) (columns oldOffset hold)).2

theorem graphHolds_succ (step : ProjectionStep)
    {phase : Phase} {depth : Nat} (holds : GraphHolds phase depth) :
    GraphHolds phase (depth + 1) := by
  intro parent
  exact step phase depth parent (holds parent).1 (holds parent).2

theorem graphHolds_from (step : ProjectionStep) (phase : Phase)
    (baseDepth : Nat) (base : GraphHolds phase baseDepth) :
    ∀ extra, GraphHolds phase (baseDepth + extra) := by
  intro extra
  induction extra with
  | zero => simpa
  | succ extra ih =>
      rw [show baseDepth + (extra + 1) = (baseDepth + extra) + 1 by omega]
      exact graphHolds_succ step ih

/-- A sparse projection gives arbitrarily many certified lines in both phases. -/
theorem graphHolds_unbounded (step : ProjectionStep) (size : Nat) :
    GraphHolds .even (1 + size) ∧ GraphHolds .odd size := by
  constructor
  · exact graphHolds_from step .even 1 graphHolds_even_one size
  · simpa using graphHolds_from step .odd 0 graphHolds_odd_zero size

/-- Sparse graph certificates yield an ordered semantic free grid on a light board. -/
def freeGridOfGraphHolds
    {phase : Phase} {depth : Nat} (graph : GraphHolds phase depth)
    (parent : Index) {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid phase depth parent) stateGrid)
    (shaded : CycleShade stateGrid
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth) .light) :
    FreeGrid (localGrid phase depth parent) stateGrid
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth) (offsets depth).length where
  columnAt := fun index => lineCoordinate phase depth (offsetAt depth index)
  rowAt := fun index => lineCoordinate phase depth (offsetAt depth index)
  column_strictMono := by
    intro first second hlt
    have hmono := offsetAt_strictMono depth hlt
    cases phase <;> simp [lineCoordinate, Phase.factor] <;> omega
  row_strictMono := by
    intro first second hlt
    have hmono := offsetAt_strictMono depth hlt
    cases phase <;> simp [lineCoordinate, Phase.factor] <;> omega
  column_west := by
    intro index
    have hpositive := (offsetAt_full_bounds depth index).1
    cases phase <;>
      simp [lineCoordinate, quarterStart, west, scale, Phase.factor,
        quarterWest] <;> omega
  column_east := by
    intro index
    have hbound := (offsetAt_full_bounds depth index).2
    rw [pow_succ] at hbound
    cases phase <;>
      simp [lineCoordinate, quarterStart, west, east, scale, Phase.factor,
        quarterWest, quarterEast] <;> omega
  row_south := by
    intro index
    have hpositive := (offsetAt_full_bounds depth index).1
    cases phase <;>
      simp [lineCoordinate, quarterStart, west, scale, Phase.factor,
        quarterWest, quarterSouth] <;> omega
  row_north := by
    intro index
    have hbound := (offsetAt_full_bounds depth index).2
    rw [pow_succ] at hbound
    cases phase <;>
      simp [lineCoordinate, quarterStart, west, east, scale, Phase.factor,
        quarterWest, quarterNorth] <;> omega
  freeColumn := by
    intro index
    have certificates := graph parent
    apply isFreeColumn_of_certificate valid (canonicalCycle phase depth parent) shaded
    exact (certificates.2 (offsetAt depth index) (offsetAt_mem depth index)).toColumnCertificate
  freeRow := by
    intro index
    have certificates := graph parent
    apply isFreeRow_of_certificate valid (canonicalCycle phase depth parent) shaded
    exact (certificates.1 (offsetAt depth index) (offsetAt_mem depth index)).toRowCertificate

def unboundedFreeGrids (step : ProjectionStep) (size : Nat)
    (evenParent oddParent : Index)
    {evenState oddState : Nat → Nat → RedShades.State}
    (evenValid : ValidShadeGrid (localGrid .even (1 + size) evenParent) evenState)
    (oddValid : ValidShadeGrid (localGrid .odd size oddParent) oddState)
    (evenShaded : CycleShade evenState
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)) .light)
    (oddShaded : CycleShade oddState
      (west .odd size) (east .odd size)
      (west .odd size) (east .odd size) .light) :
    FreeGrid (localGrid .even (1 + size) evenParent) evenState
        (west .even (1 + size)) (east .even (1 + size))
        (west .even (1 + size)) (east .even (1 + size)) (size + 2) ×
      FreeGrid (localGrid .odd size oddParent) oddState
        (west .odd size) (east .odd size)
        (west .odd size) (east .odd size) (size + 1) := by
  have graphs := graphHolds_unbounded step size
  constructor
  · have grid := freeGridOfGraphHolds graphs.1 evenParent evenValid evenShaded
    rw [offsets_length, show 1 + size + 1 = size + 2 by omega] at grid
    exact grid
  · have grid := freeGridOfGraphHolds graphs.2 oddParent oddValid oddShaded
    rw [offsets_length] at grid
    exact grid

end SparseFreeLineRecurrence
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
