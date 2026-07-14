/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderCoverageLocalAudit

/-!
# Finite row and column states for sparse free-line refinement

The last vertical bit of a substituted symbol determines one of two finite row
classes; the analogous horizontal bit determines a column class.  These
classes are sufficient for the local sparse, near, and exit projections used
by the reduced Robinson free-line recurrence.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineLocalStates

open RedCycles RedShadeGraph RedShadeGraphRefinement Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- All symbols that can occur after taking a child in a fixed vertical half. -/
def rowChildren (vertical : Fin 2) : List Index :=
  (List.finRange 104).flatMap fun parent =>
    [childBlock parent 0 vertical, childBlock parent 1 vertical]

/-- All symbols that can occur after taking a child in a fixed horizontal half. -/
def columnChildren (horizontal : Fin 2) : List Index :=
  (List.finRange 104).flatMap fun parent =>
    [childBlock parent horizontal 0, childBlock parent horizontal 1]

theorem child_mem_rowChildren (parent : Index) (horizontal vertical : Fin 2) :
    childBlock parent horizontal vertical ∈ rowChildren vertical := by
  simp only [rowChildren, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false]
  refine ⟨parent, by simp, ?_⟩
  fin_cases horizontal <;> simp

theorem child_mem_columnChildren (parent : Index) (horizontal vertical : Fin 2) :
    childBlock parent horizontal vertical ∈ columnChildren horizontal := by
  simp only [columnChildren, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false]
  refine ⟨parent, by simp, ?_⟩
  fin_cases vertical <;> simp

/-- The final vertical address bit classifies every nontrivially refined symbol. -/
theorem iterateRefine_succ_mem_rowChildren (depth : Nat)
    (grid : Nat → Nat → Index) (x y : Nat) :
    iterateRefine (depth + 1) grid x y ∈ rowChildren (parityOffset y) := by
  change childBlock
      (iterateRefine depth grid (x / 2) (y / 2))
      (parityOffset x) (parityOffset y) ∈ rowChildren (parityOffset y)
  exact child_mem_rowChildren _ _ _

/-- The final horizontal address bit classifies every nontrivially refined symbol. -/
theorem iterateRefine_succ_mem_columnChildren (depth : Nat)
    (grid : Nat → Nat → Index) (x y : Nat) :
    iterateRefine (depth + 1) grid x y ∈ columnChildren (parityOffset x) := by
  change childBlock
      (iterateRefine depth grid (x / 2) (y / 2))
      (parityOffset x) (parityOffset y) ∈ columnChildren (parityOffset x)
  exact child_mem_columnChildren _ _ _

/-- A target vertical segment has a sparse old segment in the same macrocell. -/
def verticalAncestorAt (sourceY targetY : Nat) (parent : Index)
    (targetX : Nat) : Bool :=
  !(Signals.verticalInterior? (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome ||
    (List.range 2).any fun sourceX =>
      decide (sparseCoordinate sourceX = targetX) &&
        (Signals.verticalInterior?
          (componentAt (coarseGrid parent) sourceX sourceY)
          (quadrantAt sourceX sourceY)).isSome

/-- A target horizontal segment has a sparse old segment in the same macrocell. -/
def horizontalAncestorAt (sourceX targetX : Nat) (parent : Index)
    (targetY : Nat) : Bool :=
  !(Signals.horizontalInterior? (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome ||
    (List.range 2).any fun sourceY =>
      decide (sparseCoordinate sourceY = targetY) &&
        (Signals.horizontalInterior?
          (componentAt (coarseGrid parent) sourceX sourceY)
          (quadrantAt sourceX sourceY)).isSome

/-- A target vertical segment is the live north exit of a sparse old segment. -/
def verticalNorthAncestorAt (sourceY targetY : Nat) (parent : Index)
    (targetX : Nat) : Bool :=
  !(Signals.verticalInterior? (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome ||
    (List.range 2).any fun sourceX =>
      decide (sparseCoordinate sourceX = targetX) &&
        (Signals.verticalInterior?
          (componentAt (coarseGrid parent) sourceX sourceY)
          (quadrantAt sourceX sourceY)).isSome &&
        decide (portPresent (coarseGrid parent)
          ⟨sourceX, sourceY, .north⟩ = true) &&
        decide (portPresent (fineGrid parent)
          ⟨targetX, targetY, .north⟩ = true)

/-- A target horizontal segment is the live east exit of a sparse old segment. -/
def horizontalEastAncestorAt (sourceX targetX : Nat) (parent : Index)
    (targetY : Nat) : Bool :=
  !(Signals.horizontalInterior? (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome ||
    (List.range 2).any fun sourceY =>
      decide (sparseCoordinate sourceY = targetY) &&
        (Signals.horizontalInterior?
          (componentAt (coarseGrid parent) sourceX sourceY)
          (quadrantAt sourceX sourceY)).isSome &&
        decide (portPresent (coarseGrid parent)
          ⟨sourceX, sourceY, .east⟩ = true) &&
        decide (portPresent (fineGrid parent)
          ⟨targetX, targetY, .east⟩ = true)

def verticalCheck (sourceY targetY : Nat) (parent : Index) : Bool :=
  (List.range 8).all (verticalAncestorAt sourceY targetY parent)

def horizontalCheck (sourceX targetX : Nat) (parent : Index) : Bool :=
  (List.range 8).all (horizontalAncestorAt sourceX targetX parent)

def verticalNorthCheck (sourceY targetY : Nat) (parent : Index) : Bool :=
  (List.range 8).all (verticalNorthAncestorAt sourceY targetY parent)

def horizontalEastCheck (sourceX targetX : Nat) (parent : Index) : Bool :=
  (List.range 8).all (horizontalEastAncestorAt sourceX targetX parent)

set_option linter.flexible false in
theorem verticalCheck_sound {sourceY targetY : Nat} {parent : Index}
    (checked : verticalCheck sourceY targetY parent = true) :
    ∀ targetX, targetX < 8 →
      Signals.verticalInterior?
        (componentAt (fineGrid parent) targetX targetY)
        (quadrantAt targetX targetY) ≠ none →
      ∃ sourceX, sourceX < 2 ∧ sparseCoordinate sourceX = targetX ∧
        Signals.verticalInterior?
          (componentAt (coarseGrid parent) sourceX sourceY)
          (quadrantAt sourceX sourceY) ≠ none := by
  simp only [verticalCheck, List.all_eq_true, List.mem_range] at checked
  intro targetX htarget interior
  have covered := checked targetX htarget
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [verticalAncestorAt, required, Bool.not_true, Bool.false_or,
    List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at covered
  rcases covered with ⟨sourceX, hsource, coordinate, source⟩
  exact ⟨sourceX, hsource, coordinate,
    Option.isSome_iff_ne_none.mp source⟩

set_option linter.flexible false in
theorem horizontalCheck_sound {sourceX targetX : Nat} {parent : Index}
    (checked : horizontalCheck sourceX targetX parent = true) :
    ∀ targetY, targetY < 8 →
      Signals.horizontalInterior?
        (componentAt (fineGrid parent) targetX targetY)
        (quadrantAt targetX targetY) ≠ none →
      ∃ sourceY, sourceY < 2 ∧ sparseCoordinate sourceY = targetY ∧
        Signals.horizontalInterior?
          (componentAt (coarseGrid parent) sourceX sourceY)
          (quadrantAt sourceX sourceY) ≠ none := by
  simp only [horizontalCheck, List.all_eq_true, List.mem_range] at checked
  intro targetY htarget interior
  have covered := checked targetY htarget
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [horizontalAncestorAt, required, Bool.not_true, Bool.false_or,
    List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at covered
  rcases covered with ⟨sourceY, hsource, coordinate, source⟩
  exact ⟨sourceY, hsource, coordinate,
    Option.isSome_iff_ne_none.mp source⟩

set_option linter.flexible false in
theorem verticalNorthCheck_sound {sourceY targetY : Nat} {parent : Index}
    (checked : verticalNorthCheck sourceY targetY parent = true) :
    ∀ targetX, targetX < 8 →
      Signals.verticalInterior?
        (componentAt (fineGrid parent) targetX targetY)
        (quadrantAt targetX targetY) ≠ none →
      ∃ sourceX, sourceX < 2 ∧ sparseCoordinate sourceX = targetX ∧
        Signals.verticalInterior?
          (componentAt (coarseGrid parent) sourceX sourceY)
          (quadrantAt sourceX sourceY) ≠ none ∧
        portPresent (coarseGrid parent) ⟨sourceX, sourceY, .north⟩ = true ∧
        portPresent (fineGrid parent) ⟨targetX, targetY, .north⟩ = true := by
  simp only [verticalNorthCheck, List.all_eq_true, List.mem_range] at checked
  intro targetX htarget interior
  have covered := checked targetX htarget
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [verticalNorthAncestorAt, required, Bool.not_true, Bool.false_or,
    List.any_eq_true, List.mem_range] at covered
  rcases covered with ⟨sourceX, hsource, hall⟩
  have clean : ((sparseCoordinate sourceX = targetX ∧
      (Signals.verticalInterior?
        (componentAt (coarseGrid parent) sourceX sourceY)
        (quadrantAt sourceX sourceY)).isSome = true) ∧
      portPresent (coarseGrid parent) ⟨sourceX, sourceY, .north⟩ = true) ∧
      portPresent (fineGrid parent) ⟨targetX, targetY, .north⟩ = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hall
  rcases clean with ⟨⟨⟨coordinate, source⟩, oldLive⟩, targetLive⟩
  exact ⟨sourceX, hsource, coordinate,
    Option.isSome_iff_ne_none.mp source, oldLive, targetLive⟩

set_option linter.flexible false in
theorem horizontalEastCheck_sound {sourceX targetX : Nat} {parent : Index}
    (checked : horizontalEastCheck sourceX targetX parent = true) :
    ∀ targetY, targetY < 8 →
      Signals.horizontalInterior?
        (componentAt (fineGrid parent) targetX targetY)
        (quadrantAt targetX targetY) ≠ none →
      ∃ sourceY, sourceY < 2 ∧ sparseCoordinate sourceY = targetY ∧
        Signals.horizontalInterior?
          (componentAt (coarseGrid parent) sourceX sourceY)
          (quadrantAt sourceX sourceY) ≠ none ∧
        portPresent (coarseGrid parent) ⟨sourceX, sourceY, .east⟩ = true ∧
        portPresent (fineGrid parent) ⟨targetX, targetY, .east⟩ = true := by
  simp only [horizontalEastCheck, List.all_eq_true, List.mem_range] at checked
  intro targetY htarget interior
  have covered := checked targetY htarget
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [horizontalEastAncestorAt, required, Bool.not_true, Bool.false_or,
    List.any_eq_true, List.mem_range] at covered
  rcases covered with ⟨sourceY, hsource, hall⟩
  have clean : ((sparseCoordinate sourceY = targetY ∧
      (Signals.horizontalInterior?
        (componentAt (coarseGrid parent) sourceX sourceY)
        (quadrantAt sourceX sourceY)).isSome = true) ∧
      portPresent (coarseGrid parent) ⟨sourceX, sourceY, .east⟩ = true) ∧
      portPresent (fineGrid parent) ⟨targetX, targetY, .east⟩ = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hall
  rcases clean with ⟨⟨⟨coordinate, source⟩, oldLive⟩, targetLive⟩
  exact ⟨sourceY, hsource, coordinate,
    Option.isSome_iff_ne_none.mp source, oldLive, targetLive⟩

set_option linter.style.nativeDecide false in
/-- Lower-row symbols preserve source row `0` at the sparse target row. -/
theorem lowerRow_sparse_zero :
    ∀ parent ∈ rowChildren 0, verticalCheck 0 0 parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Lower-row symbols preserve source row `1` at the sparse target row. -/
theorem lowerRow_sparse_one :
    ∀ parent ∈ rowChildren 0, verticalCheck 1 1 parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Lower-row symbols project source row `1` to the adjacent near row. -/
theorem lowerRow_near :
    ∀ parent ∈ rowChildren 0, verticalCheck 1 2 parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Upper-row symbols project source row `1` to the macrocell exit row. -/
theorem upperRow_exit :
    ∀ parent ∈ rowChildren 1, verticalCheck 1 7 parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Upper-row exits retain both the old and refined north endpoints. -/
theorem upperRow_northExit :
    ∀ parent ∈ rowChildren 1, verticalNorthCheck 1 7 parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Left-column symbols preserve source column `0` at the sparse target column. -/
theorem leftColumn_sparse_zero :
    ∀ parent ∈ columnChildren 0, horizontalCheck 0 0 parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Left-column symbols preserve source column `1` at the sparse target column. -/
theorem leftColumn_sparse_one :
    ∀ parent ∈ columnChildren 0, horizontalCheck 1 1 parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Left-column symbols project source column `1` to the adjacent near column. -/
theorem leftColumn_near :
    ∀ parent ∈ columnChildren 0, horizontalCheck 1 2 parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Right-column symbols project source column `1` to the macrocell exit column. -/
theorem rightColumn_exit :
    ∀ parent ∈ columnChildren 1, horizontalCheck 1 7 parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Right-column exits retain both the old and refined east endpoints. -/
theorem rightColumn_eastExit :
    ∀ parent ∈ columnChildren 1, horizontalEastCheck 1 7 parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The four nontrivial local route classes have bounded even paths. -/
theorem boundedRouteClasses :
    (∀ parent ∈ rowChildren 0,
      BorderCoverageLocalAudit.alignedRowCheck parent 1 2 = true) ∧
    (∀ parent ∈ rowChildren 1,
      BorderCoverageLocalAudit.alignedRowCheck parent 1 7 = true) ∧
    (∀ parent ∈ columnChildren 0,
      BorderCoverageLocalAudit.alignedColumnCheck parent 1 2 = true) ∧
    (∀ parent ∈ columnChildren 1,
      BorderCoverageLocalAudit.alignedColumnCheck parent 1 7 = true) := by
  native_decide

end SparseFreeLineLocalStates
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
