/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenOddLocalStep
import LeanWang.OllingerRobinson104SparseFreeLineOddExtraStep

/-!
# Assembling the sparse free-line projection step

Every retained child is local except the odd-phase pivot extra and the
even-phase main child of the preceding pivot extra. The latter is the only
branch allowed to use the complete old sparse pattern.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineProjectionStep

open RedCycles ShadedFreeLineGraph ShadedFreeLinePatternRefinement
  ShadedFreeLineRecurrence
  SparseFreeLineOffsets SparseFreeLineRecurrence
  SparseFreeLineLocalRecurrence SparseFreeLineEvenOddLocalStep

set_option maxRecDepth 20000

theorem evenOddMainChild_of_pattern
    (remaining : EvenExtraMainStep) :
    ∀ depth parent offset,
      offset ∈ offsets depth →
      offset % 2 = 1 →
      (∀ oldOffset ∈ offsets depth,
        LiveRowCertificate (localGrid .even depth parent)
          (west .even depth) (east .even depth)
          (west .even depth) (east .even depth)
          (lineCoordinate .even depth oldOffset)) →
      (∀ oldOffset ∈ offsets depth,
        LiveColumnCertificate (localGrid .even depth parent)
          (west .even depth) (east .even depth)
          (west .even depth) (east .even depth)
          (lineCoordinate .even depth oldOffset)) →
      LiveRowCertificate (localGrid .even (depth + 1) parent)
          (west .even (depth + 1)) (east .even (depth + 1))
          (west .even (depth + 1)) (east .even (depth + 1))
          (lineCoordinate .even (depth + 1) (mainChild offset)) ∧
        LiveColumnCertificate (localGrid .even (depth + 1) parent)
          (west .even (depth + 1)) (east .even (depth + 1))
          (west .even (depth + 1)) (east .even (depth + 1))
          (lineCoordinate .even (depth + 1) (mainChild offset)) := by
  intro depth parent offset hold hodd rows columns
  cases depth with
  | zero =>
      simp only [offsets_zero, List.mem_singleton] at hold
      subst offset
      norm_num at hodd
  | succ depth =>
      rcases odd_mem_offsets_succ_cases depth hold hodd with hmod | hextra
      · exact SparseFreeLineEvenOddLocalStep.mainChildStep depth parent hmod
          (rows offset hold) (columns offset hold)
      · subst offset
        simpa [Nat.add_assoc] using remaining depth parent rows columns

theorem childStep_of_pattern
    (evenExtra : EvenExtraMainStep) (oddExtra : OddPivotExtraStep)
    (phase : Phase) (depth : Nat) (parent : Index)
    (rows : ∀ offset ∈ offsets depth,
      LiveRowCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset))
    (columns : ∀ offset ∈ offsets depth,
      LiveColumnCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset))
    {offset child : Nat} (hold : offset ∈ offsets depth)
    (hchild : child ∈ children offset) :
    LiveRowCertificate (localGrid phase (depth + 1) parent)
        (west phase (depth + 1)) (east phase (depth + 1))
        (west phase (depth + 1)) (east phase (depth + 1))
        (lineCoordinate phase (depth + 1) child) ∧
      LiveColumnCertificate (localGrid phase (depth + 1) parent)
        (west phase (depth + 1)) (east phase (depth + 1))
        (west phase (depth + 1)) (east phase (depth + 1))
        (lineCoordinate phase (depth + 1) child) := by
  rcases mem_children_cases hchild with hmain | ⟨heven, hextra⟩
  · subst child
    by_cases hoffsetEven : offset % 2 = 0
    · exact evenMainChildStep phase depth parent offset hold hoffsetEven
        (rows offset hold) (columns offset hold)
    · have hoffsetOdd : offset % 2 = 1 := by omega
      cases phase
      · exact evenOddMainChild_of_pattern evenExtra depth parent offset hold
          hoffsetOdd rows columns
      · exact oddMainChildStep_of_odd depth parent offset hold hoffsetOdd
          (rows offset hold) (columns offset hold)
  · subst child
    have hpivot := even_offset_eq_pivot depth hold heven
    subst offset
    cases phase
    · exact evenPivotExtraStep depth parent
        (rows (pivot depth) (pivot_mem_offsets depth))
        (columns (pivot depth) (pivot_mem_offsets depth))
    · exact oddExtra depth parent
        (rows (pivot depth) (pivot_mem_offsets depth))
        (columns (pivot depth) (pivot_mem_offsets depth))

/-- The sparse recurrence reduces to its one truthful whole-pattern branch. -/
theorem projectionStep
    (evenExtra : EvenExtraMainStep) (oddExtra : OddPivotExtraStep) :
    SparseFreeLineRecurrence.ProjectionStep := by
  intro phase depth parent rows columns
  constructor
  · intro child hchild
    rcases mem_offsets_succ_cases depth hchild with
      ⟨offset, hold, hchildOf⟩
    exact (childStep_of_pattern evenExtra oddExtra phase depth parent
      rows columns hold hchildOf).1
  · intro child hchild
    rcases mem_offsets_succ_cases depth hchild with
      ⟨offset, hold, hchildOf⟩
    exact (childStep_of_pattern evenExtra oddExtra phase depth parent
      rows columns hold hchildOf).2

end SparseFreeLineProjectionStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
