/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13Data

/-!
Finite recognizability checks for the audited Figure 16 substitution.

Unlike `Figure16.Symbol.tileSet`, which only checks the internal seams of the
displayed substitution blocks, this file works with the actual 368 Figure 18
quarter-sites built from the 92 Figure 13 tiles.  A child site's quadrant fixes
its offset inside a `2 x 2` substituted parent.  We can therefore enumerate the
parent sites whose audited expansion produces that child and test whether the
parent is locally recognizable.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace LayeredFigure18ScaffoldData
namespace ConcreteData

/-- Horizontal offset selected by a child Figure 18 quadrant. -/
def childColumn (site : Figure18Site) : Fin 2 :=
  quadrantColumn site.quadrant

/-- Vertical offset selected by a child Figure 18 quadrant. -/
def childRow (site : Figure18Site) : Fin 2 :=
  quadrantRow site.quadrant

/-- Does the audited Figure 16 expansion of `source` produce `target`? -/
def expandsToBool (source target : Figure18Site) : Bool :=
  siteMatchesSymbolsBool
    ((thinBlockAtSite source).entry (childColumn target) (childRow target))
    ((thickBlockAtSite source).entry (childColumn target) (childRow target))
    ((blackBlockAtSite source).entry (childColumn target) (childRow target))
    target.quadrant target

/-- All audited parent sites whose Figure 16 expansion produces `target`. -/
def parentCandidates (target : Figure18Site) : List Figure18Site :=
  Figure18Site.all.filter fun source => expandsToBool source target

/-- Number of audited parent sites producing a target site. -/
def parentCandidateCount (target : Figure18Site) : Nat :=
  (parentCandidates target).length

/-- Diagnostic list of targets that do not have exactly one audited parent. -/
def nonUniqueParentTargets : List (Figure18Site × Nat) :=
  (Figure18Site.all.filter fun target => parentCandidateCount target != 1).map
    fun target => (target, parentCandidateCount target)

theorem mem_parentCandidates_iff {source target : Figure18Site} :
    source ∈ parentCandidates target ↔
      expandsToBool source target = true := by
  simp [parentCandidates, Figure18Site.mem_all]

/-- Canonical parent site used to test a parent tile index. -/
def parentIndexSite (index : Fin 92) : Figure18Site where
  index := index
  quadrant := .southwest

/-- Does the audited expansion of a parent tile index produce `target`? -/
def parentIndexExpandsToBool (index : Fin 92) (target : Figure18Site) : Bool :=
  expandsToBool (parentIndexSite index) target

/-- Parent Figure 13 tile indices whose audited expansion produces `target`. -/
def parentIndexCandidates (target : Figure18Site) : List (Fin 92) :=
  (List.finRange 92).filter fun index => parentIndexExpandsToBool index target

def parentIndexCandidateCount (target : Figure18Site) : Nat :=
  (parentIndexCandidates target).length

theorem mem_parentIndexCandidates_iff {index : Fin 92} {target : Figure18Site} :
    index ∈ parentIndexCandidates target ↔
      expandsToBool (parentIndexSite index) target = true := by
  simp [parentIndexCandidates, parentIndexExpandsToBool]

/-- Histogram of radius-zero parent-index candidate counts. -/
def parentIndexCandidateCountHistogram : List (Nat × Nat) :=
  (List.range 93).filterMap fun count =>
    let targets := Figure18Site.all.filter fun target =>
      parentIndexCandidateCount target == count
    if targets.isEmpty then none else some (count, targets.length)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem parentIndexCandidateCountHistogram_eq :
    parentIndexCandidateCountHistogram =
      [(1, 20), (2, 82), (3, 51), (4, 36), (5, 15),
        (7, 28), (8, 48), (24, 48), (40, 40)] := by
  native_decide

/-- Radius-zero parent-index recognition fails for the audited substitution. -/
def allTargetsHaveUniqueParentIndexBool : Bool :=
  Figure18Site.all.all fun target =>
    decide (parentIndexCandidateCount target = 1)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allTargetsHaveUniqueParentIndexBool_eq_false :
    allTargetsHaveUniqueParentIndexBool = false := by
  native_decide

/-- Despite the ambiguity, every child site has at least one parent index. -/
def allTargetsHaveParentIndexBool : Bool :=
  Figure18Site.all.all fun target =>
    !(parentIndexCandidates target).isEmpty

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allTargetsHaveParentIndexBool_eq_true :
    allTargetsHaveParentIndexBool = true := by
  native_decide

theorem parentIndexCandidates_ne_nil (target : Figure18Site) :
    parentIndexCandidates target ≠ [] := by
  have htarget := List.all_eq_true.1 allTargetsHaveParentIndexBool_eq_true
    target (Figure18Site.mem_all target)
  intro hnil
  simp [hnil] at htarget

end ConcreteData
end LayeredFigure18ScaffoldData
end Figure13Layers
end OllingerRobinson
end LeanWang
