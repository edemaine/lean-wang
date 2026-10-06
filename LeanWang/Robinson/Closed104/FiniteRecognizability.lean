/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.FiniteRecognizability.HorizontalFollowers
import LeanWang.Robinson.Closed104.FiniteRecognizability.VerticalFollowers
import LeanWang.Robinson.Closed104.FiniteRecognizability.ParentCertificates

/-!
Executable `4 x 4` recognizability audit from Proposition 8.

The search works directly with the finite corrected-tile type `Index`.
Horizontal and vertical follower tables are computed once, after which the
row dynamic program uses only finite list lookup and membership.

The audited statement is local recognizability: in every valid `4 x 4`
neighborhood whose central `2 x 2` thin phases are `a,c/d,b`, that central
block is the child block of exactly one corrected tile.  The outer row and
column provide one-cell context, so this finite condition applies to a window
cut from any full-plane tiling.

The executable part proceeds in three stages.  It enumerates all legal rows of
length four, combines four vertically compatible rows while fixing the central
phase pattern, and compares the middle block against the 104 possible parent
child blocks.  `auditCorrect` checks both the search diagnostics and absence of
any extendable middle pair with a non-unique parent.  The final theorems turn
membership in these lists back into ordinary Wang matching hypotheses.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace FiniteRecognizability

/- The dynamic program above produces every horizontally valid length-four
row.  The next stage filters possible middle rows by thin-layer phase and asks
whether they admit one compatible row both below and above. -/

theorem indexRow_mem_fourRows (a b c d : Index)
    (hab : WangTile.HMatches (tile (components a)) (tile (components b)))
    (hbc : WangTile.HMatches (tile (components b)) (tile (components c)))
    (hcd : WangTile.HMatches (tile (components c)) (tile (components d))) :
    [a, b, c, d] ∈ fourRows := by
  rw [fourRows_correct]
  apply cons_mem_compatibleRows (mem_indices a)
  apply cons_mem_rowTailsAfter ((mem_hFollowersAt_iff a b).2 hab)
  apply cons_mem_rowTailsAfter ((mem_hFollowersAt_iff b c).2 hbc)
  apply cons_mem_rowTailsAfter ((mem_hFollowersAt_iff c d).2 hcd)
  simp [rowTailsAfter]

theorem indexRows_vCompatible (a b c d e f g h : Index)
    (hae : WangTile.VMatches (tile (components a)) (tile (components e)))
    (hbf : WangTile.VMatches (tile (components b)) (tile (components f)))
    (hcg : WangTile.VMatches (tile (components c)) (tile (components g)))
    (hdh : WangTile.VMatches (tile (components d)) (tile (components h))) :
    rowsVCompatible vFollowerTable [a, b, c, d] [e, f, g, h] = true := by
  simp [rowsVCompatible, (mem_vFollowersAt_iff a e).2 hae,
    (mem_vFollowersAt_iff b f).2 hbf,
    (mem_vFollowersAt_iff c g).2 hcg,
    (mem_vFollowersAt_iff d h).2 hdh]

theorem mem_southCentralRows_iff {row : List Index} :
    row ∈ southCentralRows ↔
      row ∈ fourRows ∧
        (components (rowCell row 1)).1 = .a ∧
        (components (rowCell row 2)).1 = .c := by
  rw [southCentralRows_correct]
  simp [southPhase]

theorem mem_northCentralRows_iff {row : List Index} :
    row ∈ northCentralRows ↔
      row ∈ fourRows ∧
        (components (rowCell row 1)).1 = .d ∧
        (components (rowCell row 2)).1 = .b := by
  rw [northCentralRows_correct]
  simp [northPhase]

private theorem mem_centralRowPairs_iff {middle : List Index × List Index} :
    middle ∈ centralRowPairs ↔
      middle.1 ∈ southCentralRows ∧
        middle.2 ∈ northCentralRows ∧
        rowsVCompatible vFollowerTable middle.1 middle.2 = true := by
  rcases middle with ⟨south, north⟩
  rw [centralRowPairs_correct]
  simp

private theorem centralRowPairExtendable_eq_true_iff
    {middle : List Index × List Index} :
    centralRowPairExtendable middle = true ↔
      (∃ south ∈ fourRows,
        rowsVCompatible vFollowerTable south middle.1 = true) ∧
      (∃ north ∈ fourRows,
        rowsVCompatible vFollowerTable middle.2 north = true) := by
  simp [centralRowPairExtendable, List.any_eq_true]

private theorem mem_extendableCentralRowPairs_iff
    {middle : List Index × List Index} :
    middle ∈ extendableCentralRowPairs ↔
      middle ∈ centralRowPairs ∧ centralRowPairExtendable middle = true := by
  rw [extendableCentralRowPairs_correct]
  simp

theorem middle_mem_extendableCentralRowPairs
    {south middleSouth middleNorth north : List Index}
    (hsouth : south ∈ fourRows)
    (hmiddleSouth : middleSouth ∈ southCentralRows)
    (hmiddleNorth : middleNorth ∈ northCentralRows)
    (hnorth : north ∈ fourRows)
    (hsm : rowsVCompatible vFollowerTable south middleSouth = true)
    (hmm : rowsVCompatible vFollowerTable middleSouth middleNorth = true)
    (hmn : rowsVCompatible vFollowerTable middleNorth north = true) :
    (middleSouth, middleNorth) ∈ extendableCentralRowPairs := by
  rw [mem_extendableCentralRowPairs_iff, mem_centralRowPairs_iff,
    centralRowPairExtendable_eq_true_iff]
  exact ⟨⟨hmiddleSouth, hmiddleNorth, hmm⟩,
    ⟨⟨south, hsouth, hsm⟩, ⟨north, hnorth, hmn⟩⟩⟩

def nonUniqueExtendableCentralRowPairs : List (List Index × List Index) :=
  extendableCentralRowPairs.filter fun middle =>
    decide ((centerParentCandidates middle).length ≠ 1)

def diagnostics : Nat × Nat × Nat × Nat :=
  (indices.length, fourRows.length, centralRowPairs.length,
    extendableCentralRowPairs.length)

set_option maxRecDepth 20000 in
private theorem auditCorrect :
    diagnostics = (104, 5440, 468, 328) ∧
      nonUniqueExtendableCentralRowPairs = [] := by
  constructor
  · decide +kernel
  · simp only [nonUniqueExtendableCentralRowPairs, List.filter_eq_nil_iff,
      decide_eq_true_eq]
    intro middle member
    simp [centerParentCandidates_length_eq_one_of_mem member]

theorem diagnostics_eq : diagnostics = (104, 5440, 468, 328) :=
  auditCorrect.1

private theorem nonUniqueExtendableCentralRowPairs_eq_nil :
    nonUniqueExtendableCentralRowPairs = [] :=
  auditCorrect.2

private theorem centerParentCandidates_length_eq_one
    {middle : List Index × List Index}
    (hmiddle : middle ∈ extendableCentralRowPairs) :
    (centerParentCandidates middle).length = 1 := by
  by_contra hlength
  have hmem : middle ∈ nonUniqueExtendableCentralRowPairs := by
    simp [nonUniqueExtendableCentralRowPairs, hmiddle, hlength]
  rw [nonUniqueExtendableCentralRowPairs_eq_nil] at hmem
  simp at hmem

/-- Every extendable well-behaved center has a unique substitution parent. -/
theorem existsUnique_parent_of_mem_extendableCentralRowPairs
    {middle : List Index × List Index}
    (hmiddle : middle ∈ extendableCentralRowPairs) :
    ∃! parent : Index, childIndexBlock parent = centralIndexBlock middle := by
  have hlength := centerParentCandidates_length_eq_one hmiddle
  cases hlist : centerParentCandidates middle with
  | nil =>
      simp [hlist] at hlength
  | cons parent tail =>
      cases tail with
      | nil =>
          refine ⟨parent, ?_, ?_⟩
          · exact mem_centerParentCandidates_iff.1 (by simp [hlist])
          · intro other hother
            have hmem := mem_centerParentCandidates_iff.2 hother
            simpa [hlist] using hmem
      | cons other tail =>
          simp [hlist] at hlength

end FiniteRecognizability
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
