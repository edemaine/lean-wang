/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.Recognizability

/-!
Executable `4 x 4` recognizability audit from Proposition 8.

The search works directly with the finite corrected-tile type `Index`.
Horizontal and vertical follower tables are computed once, after which the
row dynamic program uses only finite list lookup and membership.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace FiniteRecognizability

def indices : List Index := List.finRange 104

theorem mem_indices (index : Index) : index ∈ indices := by
  simp [indices]

private def rawHFollowers (left : Index) : List Index :=
  indices.filter fun right =>
    decide (WangTile.HMatches (tile (components left)) (tile (components right)))

private def rawVFollowers (lower : Index) : List Index :=
  indices.filter fun upper =>
    decide (WangTile.VMatches (tile (components lower)) (tile (components upper)))

def hFollowerTable : List (List Index) := indices.map rawHFollowers
def vFollowerTable : List (List Index) := indices.map rawVFollowers

def followersAt (table : List (List Index)) (index : Index) : List Index :=
  table[index.val]?.getD []

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
private theorem followerTablesCorrect : ∀ left right : Index,
    (right ∈ followersAt hFollowerTable left ↔
      WangTile.HMatches (tile (components left)) (tile (components right))) ∧
    (right ∈ followersAt vFollowerTable left ↔
      WangTile.VMatches (tile (components left)) (tile (components right))) := by
  native_decide

theorem mem_hFollowersAt_iff (left right : Index) :
    right ∈ followersAt hFollowerTable left ↔
      WangTile.HMatches (tile (components left)) (tile (components right)) :=
  (followerTablesCorrect left right).1

theorem mem_vFollowersAt_iff (lower upper : Index) :
    upper ∈ followersAt vFollowerTable lower ↔
      WangTile.VMatches (tile (components lower)) (tile (components upper)) :=
  (followerTablesCorrect lower upper).2

def rowTailsAfter (table : List (List Index))
    (left : Index) : Nat → List (List Index)
  | 0 => [[]]
  | n + 1 =>
      (followersAt table left).flatMap fun right =>
        (rowTailsAfter table right n).map fun tail => right :: tail

def compatibleRows (table : List (List Index)) : Nat → List (List Index)
  | 0 => [[]]
  | n + 1 =>
      indices.flatMap fun first =>
        (rowTailsAfter table first n).map fun tail => first :: tail

theorem cons_mem_rowTailsAfter
    {table : List (List Index)} {left right : Index}
    {n : Nat} {tail : List Index}
    (hright : right ∈ followersAt table left)
    (htail : tail ∈ rowTailsAfter table right n) :
    right :: tail ∈ rowTailsAfter table left (n + 1) := by
  simp [rowTailsAfter, hright, htail]

theorem cons_mem_compatibleRows
    {table : List (List Index)} {first : Index}
    {n : Nat} {tail : List Index}
    (hfirst : first ∈ indices)
    (htail : tail ∈ rowTailsAfter table first n) :
    first :: tail ∈ compatibleRows table (n + 1) := by
  simp [compatibleRows, hfirst, htail]

def fourRows : List (List Index) := compatibleRows hFollowerTable 4

theorem indexRow_mem_fourRows (a b c d : Index)
    (hab : WangTile.HMatches (tile (components a)) (tile (components b)))
    (hbc : WangTile.HMatches (tile (components b)) (tile (components c)))
    (hcd : WangTile.HMatches (tile (components c)) (tile (components d))) :
    [a, b, c, d] ∈ fourRows := by
  apply cons_mem_compatibleRows (mem_indices a)
  apply cons_mem_rowTailsAfter ((mem_hFollowersAt_iff a b).2 hab)
  apply cons_mem_rowTailsAfter ((mem_hFollowersAt_iff b c).2 hbc)
  apply cons_mem_rowTailsAfter ((mem_hFollowersAt_iff c d).2 hcd)
  simp [rowTailsAfter]

def rowsVCompatible (table : List (List Index))
    (lower upper : List Index) : Bool :=
  (lower.zip upper).all fun pair =>
    decide (pair.2 ∈ followersAt table pair.1)

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

def rowCell (row : List Index) (i : Nat) : Index :=
  row[i]?.getD ⟨0, by decide⟩

def southCentralRows : List (List Index) :=
  fourRows.filter fun row =>
    decide ((components (rowCell row 1)).1 = .a) &&
      decide ((components (rowCell row 2)).1 = .c)

def northCentralRows : List (List Index) :=
  fourRows.filter fun row =>
    decide ((components (rowCell row 1)).1 = .d) &&
      decide ((components (rowCell row 2)).1 = .b)

def centralRowPairs : List (List Index × List Index) :=
  southCentralRows.flatMap fun south =>
    (northCentralRows.filter fun north =>
      rowsVCompatible vFollowerTable south north).map fun north => (south, north)

def centralRowPairExtendable (middle : List Index × List Index) : Bool :=
  (fourRows.any fun south =>
    rowsVCompatible vFollowerTable south middle.1) &&
  (fourRows.any fun north =>
    rowsVCompatible vFollowerTable middle.2 north)

def extendableCentralRowPairs : List (List Index × List Index) :=
  centralRowPairs.filter centralRowPairExtendable

theorem mem_southCentralRows_iff {row : List Index} :
    row ∈ southCentralRows ↔
      row ∈ fourRows ∧
        (components (rowCell row 1)).1 = .a ∧
        (components (rowCell row 2)).1 = .c := by
  simp [southCentralRows]

theorem mem_northCentralRows_iff {row : List Index} :
    row ∈ northCentralRows ↔
      row ∈ fourRows ∧
        (components (rowCell row 1)).1 = .d ∧
        (components (rowCell row 2)).1 = .b := by
  simp [northCentralRows]

theorem mem_centralRowPairs_iff {middle : List Index × List Index} :
    middle ∈ centralRowPairs ↔
      middle.1 ∈ southCentralRows ∧
        middle.2 ∈ northCentralRows ∧
        rowsVCompatible vFollowerTable middle.1 middle.2 = true := by
  rcases middle with ⟨south, north⟩
  simp [centralRowPairs]

theorem centralRowPairExtendable_eq_true_iff
    {middle : List Index × List Index} :
    centralRowPairExtendable middle = true ↔
      (∃ south ∈ fourRows,
        rowsVCompatible vFollowerTable south middle.1 = true) ∧
      (∃ north ∈ fourRows,
        rowsVCompatible vFollowerTable middle.2 north = true) := by
  simp [centralRowPairExtendable, List.any_eq_true]

theorem mem_extendableCentralRowPairs_iff
    {middle : List Index × List Index} :
    middle ∈ extendableCentralRowPairs ↔
      middle ∈ centralRowPairs ∧ centralRowPairExtendable middle = true := by
  simp [extendableCentralRowPairs]

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

abbrev IndexBlock := Index × Index × Index × Index

def childIndexBlock (parent : Index) : IndexBlock :=
  (childBlock parent ⟨0, by decide⟩ ⟨0, by decide⟩,
    childBlock parent ⟨1, by decide⟩ ⟨0, by decide⟩,
    childBlock parent ⟨0, by decide⟩ ⟨1, by decide⟩,
    childBlock parent ⟨1, by decide⟩ ⟨1, by decide⟩)

def parentIndexBlocks : List (Index × IndexBlock) :=
  indices.map fun parent => (parent, childIndexBlock parent)

def centralIndexBlock (middle : List Index × List Index) : IndexBlock :=
  (rowCell middle.1 1, rowCell middle.1 2,
    rowCell middle.2 1, rowCell middle.2 2)

def centerParentCandidates (middle : List Index × List Index) : List Index :=
  (parentIndexBlocks.filter fun entry =>
    entry.2 == centralIndexBlock middle).map Prod.fst

theorem mem_centerParentCandidates_iff {middle : List Index × List Index}
    {parent : Index} :
    parent ∈ centerParentCandidates middle ↔
      childIndexBlock parent = centralIndexBlock middle := by
  simp [centerParentCandidates, parentIndexBlocks, indices]

def badExtendableCentralRowPairs : List (List Index × List Index) :=
  extendableCentralRowPairs.filter fun middle =>
    (centerParentCandidates middle).isEmpty

def nonUniqueExtendableCentralRowPairs : List (List Index × List Index) :=
  extendableCentralRowPairs.filter fun middle =>
    decide ((centerParentCandidates middle).length ≠ 1)

def diagnostics : Nat × Nat × Nat × Nat × Nat :=
  (indices.length, fourRows.length, centralRowPairs.length,
    extendableCentralRowPairs.length, badExtendableCentralRowPairs.length)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
private theorem auditCorrect :
    diagnostics = (104, 5440, 468, 328, 0) ∧
      badExtendableCentralRowPairs = [] ∧
      nonUniqueExtendableCentralRowPairs = [] := by
  native_decide

theorem diagnostics_eq : diagnostics = (104, 5440, 468, 328, 0) :=
  auditCorrect.1

/-- Proposition 8's finite test: every extendable well-behaved center is a
substitution image. -/
theorem badExtendableCentralRowPairs_eq_nil :
    badExtendableCentralRowPairs = [] :=
  auditCorrect.2.1

theorem nonUniqueExtendableCentralRowPairs_eq_nil :
    nonUniqueExtendableCentralRowPairs = [] :=
  auditCorrect.2.2

theorem centerParentCandidates_length_eq_one
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
