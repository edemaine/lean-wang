/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.Data

/-!
The corrected 104-tile component alphabet underlying the Ollinger substitution.

The alphabet is transcribed directly in `LeanWang.Robinson.Closed104.Data`. This module
audits its size and duplicate freedom, then proves that every parent/quadrant
pair has a unique substitution child in the same alphabet.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
@[simp]
theorem alphabet_length : alphabet.length = 104 := by
  native_decide

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem alphabet_nodup : alphabet.Nodup := by
  native_decide

/-- Index type for the corrected component alphabet. -/
abbrev Index := Fin 104

/-- Component triple at a corrected Figure 13 tile index. -/
def components (index : Index) : Components :=
  alphabet[index.val]'(by simp [index.isLt])

/-- Corrected child indices matching one parent/quadrant substitution cell. -/
def childCandidates (parent : Index) (quadrant : Quadrant) : List Index :=
  (List.finRange 104).filter fun child =>
    componentTripleChildMatchesBool (components parent) quadrant (components child)

theorem mem_childCandidates_iff
    {parent child : Index} {quadrant : Quadrant} :
    child ∈ childCandidates parent quadrant ↔
      componentTripleChildMatchesBool
        (components parent) quadrant (components child) = true := by
  simp [childCandidates]

/-- Every corrected parent/quadrant cell has exactly one child tile. -/
def allChildrenUniqueBool : Bool :=
  (List.finRange 104).all fun parent =>
    Quadrant.all.all fun quadrant =>
      decide ((childCandidates parent quadrant).length = 1)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allChildrenUniqueBool_eq_true :
    allChildrenUniqueBool = true := by
  native_decide

theorem childCandidates_length_eq_one
    (parent : Index) (quadrant : Quadrant) :
    (childCandidates parent quadrant).length = 1 := by
  have hparent := List.all_eq_true.1 allChildrenUniqueBool_eq_true
    parent (List.mem_finRange parent)
  have hquadrant := List.all_eq_true.1 hparent quadrant (Quadrant.mem_all quadrant)
  exact of_decide_eq_true hquadrant

/-- Executable Figure 16 substitution on the corrected tile alphabet. -/
def childIndex (parent : Index) (quadrant : Quadrant) : Index :=
  (childCandidates parent quadrant).headD parent

theorem childCandidates_eq_singleton
    (parent : Index) (quadrant : Quadrant) :
    childCandidates parent quadrant = [childIndex parent quadrant] := by
  have hlength := childCandidates_length_eq_one parent quadrant
  cases h : childCandidates parent quadrant with
  | nil =>
      simp [h] at hlength
  | cons child tail =>
      cases tail with
      | nil =>
          simp [childIndex, h]
      | cons other tail =>
          simp [h] at hlength

theorem childIndex_matches (parent : Index) (quadrant : Quadrant) :
    componentTripleChildMatchesBool
      (components parent) quadrant (components (childIndex parent quadrant)) = true := by
  rw [← mem_childCandidates_iff]
  simp [childCandidates_eq_singleton]

theorem eq_childIndex_of_matches
    {parent child : Index} {quadrant : Quadrant}
    (hmatches : componentTripleChildMatchesBool
      (components parent) quadrant (components child) = true) :
    child = childIndex parent quadrant := by
  have hmem : child ∈ childCandidates parent quadrant :=
    mem_childCandidates_iff.2 hmatches
  simpa [childCandidates_eq_singleton] using hmem

/-- The `2 x 2` corrected child-index block of one parent tile. -/
def childBlock (parent : Index) : Fin 2 → Fin 2 → Index :=
  fun i j => childIndex parent (quadrantOfOffset i j)

theorem childBlock_matches (parent : Index) (i j : Fin 2) :
    componentTripleChildMatchesBool (components parent) (quadrantOfOffset i j)
      (components (childBlock parent i j)) = true :=
  childIndex_matches parent (quadrantOfOffset i j)

end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
