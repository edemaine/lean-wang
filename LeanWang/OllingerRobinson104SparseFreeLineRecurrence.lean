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

This recurrence retains only `depth + 1` even offsets.  It is sufficient for
the scaffold theorem and avoids the one coupled odd-child case needed by the
exact `2^(depth+2)-2`-line recurrence.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineRecurrence

open RedCycles ShadedFreeLineGraph ShadedFreeLinePatternRefinement
  ShadedFreeLineRecurrence SparseFreeLineOffsets

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

end SparseFreeLineRecurrence
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
