/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.FiniteRecognizability

/-!
Proposition-level local recognizability for the corrected Ollinger tiles.

A valid `4 x 4` index neighborhood whose southwest central tile has thin phase
`a` determines a unique parent for its central `2 x 2` block. The finite search
and this geometric interface are kept separate so later desubstitution proofs
do not depend on executable-list details.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace LocalRecognizability

open FiniteRecognizability

def offset0 : Fin 2 := ⟨0, by decide⟩
def offset1 : Fin 2 := ⟨1, by decide⟩

structure IndexRow4 where
  x0 : Index
  x1 : Index
  x2 : Index
  x3 : Index

namespace IndexRow4

def codes (row : IndexRow4) : List Nat :=
  [row.x0.val, row.x1.val, row.x2.val, row.x3.val]

def HValid (row : IndexRow4) : Prop :=
  WangTile.HMatches (tile (components row.x0)) (tile (components row.x1)) ∧
    WangTile.HMatches (tile (components row.x1)) (tile (components row.x2)) ∧
    WangTile.HMatches (tile (components row.x2)) (tile (components row.x3))

theorem codes_mem_fourRows {row : IndexRow4} (hrow : row.HValid) :
    row.codes ∈ fourRows := by
  exact indexRow_mem_fourRows row.x0 row.x1 row.x2 row.x3
    hrow.1 hrow.2.1 hrow.2.2

def VCompatible (lower upper : IndexRow4) : Prop :=
  WangTile.VMatches (tile (components lower.x0)) (tile (components upper.x0)) ∧
    WangTile.VMatches (tile (components lower.x1)) (tile (components upper.x1)) ∧
    WangTile.VMatches (tile (components lower.x2)) (tile (components upper.x2)) ∧
    WangTile.VMatches (tile (components lower.x3)) (tile (components upper.x3))

theorem codes_vCompatible {lower upper : IndexRow4}
    (hrows : VCompatible lower upper) :
    rowsVCompatible vFollowerTable lower.codes upper.codes = true := by
  exact indexRows_vCompatible
    lower.x0 lower.x1 lower.x2 lower.x3
    upper.x0 upper.x1 upper.x2 upper.x3
    hrows.1 hrows.2.1 hrows.2.2.1 hrows.2.2.2

end IndexRow4

/-- A valid `4 x 4` neighborhood with the central southwest phase fixed. -/
structure Neighborhood where
  south : IndexRow4
  middleSouth : IndexRow4
  middleNorth : IndexRow4
  north : IndexRow4
  south_h : south.HValid
  middleSouth_h : middleSouth.HValid
  middleNorth_h : middleNorth.HValid
  north_h : north.HValid
  south_middle_v : south.VCompatible middleSouth
  middle_v : middleSouth.VCompatible middleNorth
  middle_north_v : middleNorth.VCompatible north
  centerThin : (components middleSouth.x1).1 = .a

namespace Neighborhood

theorem centerEastThin (N : Neighborhood) :
    (components N.middleSouth.x2).1 = .c := by
  calc
    (components N.middleSouth.x2).1 =
        phaseEast (components N.middleSouth.x1).1 :=
      thin_eq_thinEast_of_hMatches N.middleSouth_h.2.1
    _ = .c := by rw [N.centerThin]; rfl

theorem centerNorthThin (N : Neighborhood) :
    (components N.middleNorth.x1).1 = .d := by
  calc
    (components N.middleNorth.x1).1 =
        phaseNorth (components N.middleSouth.x1).1 :=
      thin_eq_thinNorth_of_vMatches N.middle_v.2.1
    _ = .d := by rw [N.centerThin]; rfl

theorem centerNortheastThin (N : Neighborhood) :
    (components N.middleNorth.x2).1 = .b := by
  calc
    (components N.middleNorth.x2).1 =
        phaseNorth (components N.middleSouth.x2).1 :=
      thin_eq_thinNorth_of_vMatches N.middle_v.2.2.1
    _ = .b := by rw [N.centerEastThin]; rfl

theorem middleSouth_mem (N : Neighborhood) :
    N.middleSouth.codes ∈ southCentralRows := by
  rw [mem_southCentralRows_iff]
  exact ⟨N.middleSouth.codes_mem_fourRows N.middleSouth_h,
    by simp [IndexRow4.codes, rowCell, N.centerThin],
    by simp [IndexRow4.codes, rowCell, N.centerEastThin]⟩

theorem middleNorth_mem (N : Neighborhood) :
    N.middleNorth.codes ∈ northCentralRows := by
  rw [mem_northCentralRows_iff]
  exact ⟨N.middleNorth.codes_mem_fourRows N.middleNorth_h,
    by simp [IndexRow4.codes, rowCell, N.centerNorthThin],
    by simp [IndexRow4.codes, rowCell, N.centerNortheastThin]⟩

theorem middle_mem_extendable (N : Neighborhood) :
    (N.middleSouth.codes, N.middleNorth.codes) ∈
      extendableCentralRowPairs := by
  exact middle_mem_extendableCentralRowPairs
    (N.south.codes_mem_fourRows N.south_h)
    N.middleSouth_mem N.middleNorth_mem
    (N.north.codes_mem_fourRows N.north_h)
    (IndexRow4.codes_vCompatible N.south_middle_v)
    (IndexRow4.codes_vCompatible N.middle_v)
    (IndexRow4.codes_vCompatible N.middle_north_v)

/-- The central `2 x 2` block has a unique Figure 16 substitution parent. -/
theorem existsUnique_centerParent (N : Neighborhood) :
    ∃! parent : Index,
      childCodeBlock parent =
        (N.middleSouth.x1.val, N.middleSouth.x2.val,
          N.middleNorth.x1.val, N.middleNorth.x2.val) := by
  simpa [centralCodeBlock, IndexRow4.codes, rowCell] using
    existsUnique_parent_of_mem_extendableCentralRowPairs N.middle_mem_extendable

def IsCenterParent (N : Neighborhood) (parent : Index) : Prop :=
  childBlock parent offset0 offset0 = N.middleSouth.x1 ∧
    childBlock parent offset1 offset0 = N.middleSouth.x2 ∧
    childBlock parent offset0 offset1 = N.middleNorth.x1 ∧
    childBlock parent offset1 offset1 = N.middleNorth.x2

theorem childCodeBlock_eq_center_iff (N : Neighborhood) (parent : Index) :
    childCodeBlock parent =
        (N.middleSouth.x1.val, N.middleSouth.x2.val,
          N.middleNorth.x1.val, N.middleNorth.x2.val) ↔
      N.IsCenterParent parent := by
  simp [childCodeBlock, IsCenterParent, offset0, offset1, Fin.ext_iff]

/-- Index-level form of local recognizability. -/
theorem existsUnique_centerParentIndex (N : Neighborhood) :
    ∃! parent : Index, N.IsCenterParent parent := by
  rcases N.existsUnique_centerParent with ⟨parent, hparent, hunique⟩
  refine ⟨parent, (N.childCodeBlock_eq_center_iff parent).1 hparent, ?_⟩
  intro other hother
  exact hunique other ((N.childCodeBlock_eq_center_iff other).2 hother)

end Neighborhood

end LocalRecognizability
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
