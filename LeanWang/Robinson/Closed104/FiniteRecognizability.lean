/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.Recognizability

/-!
Executable `4 x 4` recognizability audit from Proposition 8.

The 104 distinct corrected Wang tiles are represented by small natural-number
codes. Horizontal and vertical follower tables are computed once, after which
the row dynamic program uses only finite list lookup and membership.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace FiniteRecognizability

def tiles : TileSet := tileSet

def indexCandidates (tile : WangTile) : List Index :=
  (List.finRange 104).filter fun index => Closed104.tile (components index) == tile

def indexOfTile (tile : WangTile) : Index :=
  (indexCandidates tile).headD ⟨0, by decide⟩

/-- One corrected index representative for each distinct stable Wang tile. -/
def representatives : List Index := tiles.map indexOfTile

def codes : List Nat := List.range representatives.length

def indexAtCode (code : Nat) : Index :=
  representatives[code]?.getD ⟨0, by decide⟩

def tileAtCode (code : Nat) : WangTile :=
  Closed104.tile (components (indexAtCode code))

def thinAtCode (code : Nat) : Figure16.Thin :=
  (components (indexAtCode code)).1

def thinTable : List Figure16.Thin := codes.map thinAtCode

def thinAt (table : List Figure16.Thin) (code : Nat) : Figure16.Thin :=
  table[code]?.getD .a

def allIndexValuesInCodesBool : Bool :=
  (List.finRange 104).all fun index => decide (index.val ∈ codes)

def allIndexAtCodesCorrectBool : Bool :=
  (List.finRange 104).all fun index => decide (indexAtCode index.val = index)

def allTileAtCodesCorrectBool : Bool :=
  (List.finRange 104).all fun index =>
    decide (tileAtCode index.val = Closed104.tile (components index))

def allThinAtCodesCorrectBool : Bool :=
  (List.finRange 104).all fun index =>
    decide (thinAt thinTable index.val = (components index).1)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem finiteCodeInterfaceCorrect :
    allIndexValuesInCodesBool = true ∧
      allIndexAtCodesCorrectBool = true ∧
      allTileAtCodesCorrectBool = true ∧
      allThinAtCodesCorrectBool = true := by
  native_decide

theorem index_val_mem_codes (index : Index) : index.val ∈ codes := by
  have h := List.all_eq_true.1 finiteCodeInterfaceCorrect.1
    index (List.mem_finRange index)
  exact of_decide_eq_true h

@[simp]
theorem indexAtCode_val (index : Index) : indexAtCode index.val = index := by
  have h := List.all_eq_true.1 finiteCodeInterfaceCorrect.2.1
    index (List.mem_finRange index)
  exact of_decide_eq_true h

@[simp]
theorem tileAtCode_val (index : Index) :
    tileAtCode index.val = Closed104.tile (components index) := by
  have h := List.all_eq_true.1 finiteCodeInterfaceCorrect.2.2.1
    index (List.mem_finRange index)
  exact of_decide_eq_true h

@[simp]
theorem thinAtCode_val (index : Index) :
    thinAt thinTable index.val = (components index).1 := by
  have h := List.all_eq_true.1 finiteCodeInterfaceCorrect.2.2.2
    index (List.mem_finRange index)
  exact of_decide_eq_true h

private def rawHFollowers (left : Nat) : List Nat :=
  codes.filter fun right =>
    decide (WangTile.HMatches (tileAtCode left) (tileAtCode right))

private def rawVFollowers (lower : Nat) : List Nat :=
  codes.filter fun upper =>
    decide (WangTile.VMatches (tileAtCode lower) (tileAtCode upper))

def hFollowerTable : List (List Nat) := codes.map rawHFollowers
def vFollowerTable : List (List Nat) := codes.map rawVFollowers

def followersAt (table : List (List Nat)) (code : Nat) : List Nat :=
  table[code]?.getD []

def allHFollowerEntriesCorrectBool : Bool :=
  (List.finRange 104).all fun left =>
    (List.finRange 104).all fun right =>
      decide (right.val ∈ followersAt hFollowerTable left.val ↔
        WangTile.HMatches (Closed104.tile (components left))
          (Closed104.tile (components right)))

def allVFollowerEntriesCorrectBool : Bool :=
  (List.finRange 104).all fun lower =>
    (List.finRange 104).all fun upper =>
      decide (upper.val ∈ followersAt vFollowerTable lower.val ↔
        WangTile.VMatches (Closed104.tile (components lower))
          (Closed104.tile (components upper)))

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allHFollowerEntriesCorrectBool_eq_true :
    allHFollowerEntriesCorrectBool = true := by
  native_decide

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allVFollowerEntriesCorrectBool_eq_true :
    allVFollowerEntriesCorrectBool = true := by
  native_decide

theorem mem_hFollowersAt_iff (left right : Index) :
    right.val ∈ followersAt hFollowerTable left.val ↔
      WangTile.HMatches (Closed104.tile (components left))
        (Closed104.tile (components right)) := by
  have hleft := List.all_eq_true.1 allHFollowerEntriesCorrectBool_eq_true
    left (List.mem_finRange left)
  have hright := List.all_eq_true.1 hleft right (List.mem_finRange right)
  exact of_decide_eq_true hright

theorem mem_vFollowersAt_iff (lower upper : Index) :
    upper.val ∈ followersAt vFollowerTable lower.val ↔
      WangTile.VMatches (Closed104.tile (components lower))
        (Closed104.tile (components upper)) := by
  have hlower := List.all_eq_true.1 allVFollowerEntriesCorrectBool_eq_true
    lower (List.mem_finRange lower)
  have hupper := List.all_eq_true.1 hlower upper (List.mem_finRange upper)
  exact of_decide_eq_true hupper

def rowTailsAfter (table : List (List Nat)) (left : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
      (followersAt table left).flatMap fun right =>
        (rowTailsAfter table right n).map fun tail => right :: tail

def compatibleRows (table : List (List Nat)) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
      codes.flatMap fun first =>
        (rowTailsAfter table first n).map fun tail => first :: tail

theorem cons_mem_rowTailsAfter
    {table : List (List Nat)} {left right n : Nat} {tail : List Nat}
    (hright : right ∈ followersAt table left)
    (htail : tail ∈ rowTailsAfter table right n) :
    right :: tail ∈ rowTailsAfter table left (n + 1) := by
  simp [rowTailsAfter, hright, htail]

theorem cons_mem_compatibleRows
    {table : List (List Nat)} {first n : Nat} {tail : List Nat}
    (hfirst : first ∈ codes)
    (htail : tail ∈ rowTailsAfter table first n) :
    first :: tail ∈ compatibleRows table (n + 1) := by
  simp [compatibleRows, hfirst, htail]

def fourRows : List (List Nat) := compatibleRows hFollowerTable 4

theorem indexRow_mem_fourRows (a b c d : Index)
    (hab : WangTile.HMatches (Closed104.tile (components a))
      (Closed104.tile (components b)))
    (hbc : WangTile.HMatches (Closed104.tile (components b))
      (Closed104.tile (components c)))
    (hcd : WangTile.HMatches (Closed104.tile (components c))
      (Closed104.tile (components d))) :
    [a.val, b.val, c.val, d.val] ∈ fourRows := by
  apply cons_mem_compatibleRows (index_val_mem_codes a)
  apply cons_mem_rowTailsAfter ((mem_hFollowersAt_iff a b).2 hab)
  apply cons_mem_rowTailsAfter ((mem_hFollowersAt_iff b c).2 hbc)
  apply cons_mem_rowTailsAfter ((mem_hFollowersAt_iff c d).2 hcd)
  simp [rowTailsAfter]

def rowsVCompatible (table : List (List Nat)) (lower upper : List Nat) : Bool :=
  (lower.zip upper).all fun pair =>
    decide (pair.2 ∈ followersAt table pair.1)

theorem indexRows_vCompatible (a b c d e f g h : Index)
    (hae : WangTile.VMatches (Closed104.tile (components a))
      (Closed104.tile (components e)))
    (hbf : WangTile.VMatches (Closed104.tile (components b))
      (Closed104.tile (components f)))
    (hcg : WangTile.VMatches (Closed104.tile (components c))
      (Closed104.tile (components g)))
    (hdh : WangTile.VMatches (Closed104.tile (components d))
      (Closed104.tile (components h))) :
    rowsVCompatible vFollowerTable [a.val, b.val, c.val, d.val]
      [e.val, f.val, g.val, h.val] = true := by
  simp [rowsVCompatible, (mem_vFollowersAt_iff a e).2 hae,
    (mem_vFollowersAt_iff b f).2 hbf,
    (mem_vFollowersAt_iff c g).2 hcg,
    (mem_vFollowersAt_iff d h).2 hdh]

def rowCell (row : List Nat) (i : Nat) : Nat := row[i]?.getD 0

def southCentralRows : List (List Nat) :=
  let table := thinTable
  fourRows.filter fun row =>
    decide (thinAt table (rowCell row 1) = .a) &&
      decide (thinAt table (rowCell row 2) = .c)

def northCentralRows : List (List Nat) :=
  let table := thinTable
  fourRows.filter fun row =>
    decide (thinAt table (rowCell row 1) = .d) &&
      decide (thinAt table (rowCell row 2) = .b)

def centralRowPairs : List (List Nat × List Nat) :=
  let table := vFollowerTable
  southCentralRows.flatMap fun south =>
    (northCentralRows.filter fun north => rowsVCompatible table south north).map
      fun north => (south, north)

def centralRowPairExtendable
    (table : List (List Nat)) (middle : List Nat × List Nat) : Bool :=
  (fourRows.any fun south => rowsVCompatible table south middle.1) &&
    (fourRows.any fun north => rowsVCompatible table middle.2 north)

def extendableCentralRowPairs : List (List Nat × List Nat) :=
  let table := vFollowerTable
  centralRowPairs.filter (centralRowPairExtendable table)

theorem mem_southCentralRows_iff {row : List Nat} :
    row ∈ southCentralRows ↔
      row ∈ fourRows ∧
        thinAt thinTable (rowCell row 1) = .a ∧
        thinAt thinTable (rowCell row 2) = .c := by
  simp [southCentralRows]

theorem mem_northCentralRows_iff {row : List Nat} :
    row ∈ northCentralRows ↔
      row ∈ fourRows ∧
        thinAt thinTable (rowCell row 1) = .d ∧
        thinAt thinTable (rowCell row 2) = .b := by
  simp [northCentralRows]

theorem mem_centralRowPairs_iff {middle : List Nat × List Nat} :
    middle ∈ centralRowPairs ↔
      middle.1 ∈ southCentralRows ∧
        middle.2 ∈ northCentralRows ∧
        rowsVCompatible vFollowerTable middle.1 middle.2 = true := by
  rcases middle with ⟨south, north⟩
  simp [centralRowPairs]

theorem centralRowPairExtendable_eq_true_iff
    {middle : List Nat × List Nat} :
    centralRowPairExtendable vFollowerTable middle = true ↔
      (∃ south ∈ fourRows,
        rowsVCompatible vFollowerTable south middle.1 = true) ∧
      (∃ north ∈ fourRows,
        rowsVCompatible vFollowerTable middle.2 north = true) := by
  simp [centralRowPairExtendable, List.any_eq_true]

theorem mem_extendableCentralRowPairs_iff
    {middle : List Nat × List Nat} :
    middle ∈ extendableCentralRowPairs ↔
      middle ∈ centralRowPairs ∧
        centralRowPairExtendable vFollowerTable middle = true := by
  simp [extendableCentralRowPairs]

theorem middle_mem_extendableCentralRowPairs
    {south middleSouth middleNorth north : List Nat}
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

def codeOfIndex (index : Index) : Nat :=
  codes.find? (fun code => tileAtCode code == Closed104.tile (components index)) |>.getD 0

def allCodeOfIndexCorrectBool : Bool :=
  (List.finRange 104).all fun index => decide (codeOfIndex index = index.val)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allCodeOfIndexCorrectBool_eq_true :
    allCodeOfIndexCorrectBool = true := by
  native_decide

@[simp]
theorem codeOfIndex_eq_val (index : Index) : codeOfIndex index = index.val := by
  have h := List.all_eq_true.1 allCodeOfIndexCorrectBool_eq_true
    index (List.mem_finRange index)
  exact of_decide_eq_true h

abbrev CodeBlock := Nat × Nat × Nat × Nat

def childCodeBlock (parent : Index) : CodeBlock :=
  (codeOfIndex (childBlock parent ⟨0, by decide⟩ ⟨0, by decide⟩),
    codeOfIndex (childBlock parent ⟨1, by decide⟩ ⟨0, by decide⟩),
    codeOfIndex (childBlock parent ⟨0, by decide⟩ ⟨1, by decide⟩),
    codeOfIndex (childBlock parent ⟨1, by decide⟩ ⟨1, by decide⟩))

def parentCodeBlocks : List (Index × CodeBlock) :=
  (List.finRange 104).map fun parent => (parent, childCodeBlock parent)

def centralCodeBlock (middle : List Nat × List Nat) : CodeBlock :=
  (rowCell middle.1 1, rowCell middle.1 2,
    rowCell middle.2 1, rowCell middle.2 2)

def centerParentCandidates (middle : List Nat × List Nat) : List Index :=
  (parentCodeBlocks.filter fun entry => entry.2 == centralCodeBlock middle).map Prod.fst

theorem mem_centerParentCandidates_iff {middle : List Nat × List Nat}
    {parent : Index} :
    parent ∈ centerParentCandidates middle ↔
      childCodeBlock parent = centralCodeBlock middle := by
  simp [centerParentCandidates, parentCodeBlocks]

def badExtendableCentralRowPairs : List (List Nat × List Nat) :=
  let blocks := parentCodeBlocks
  extendableCentralRowPairs.filter fun middle =>
    (blocks.filter fun entry => entry.2 == centralCodeBlock middle).isEmpty

def nonUniqueExtendableCentralRowPairs : List (List Nat × List Nat) :=
  extendableCentralRowPairs.filter fun middle =>
    decide ((centerParentCandidates middle).length ≠ 1)

def diagnostics : Nat × Nat × Nat × Nat × Nat :=
  (codes.length, fourRows.length, centralRowPairs.length,
    extendableCentralRowPairs.length, badExtendableCentralRowPairs.length)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem diagnostics_eq :
    diagnostics = (104, 5440, 468, 328, 0) := by
  native_decide

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
/-- Proposition 8's finite test: every extendable well-behaved center is a substitution image. -/
theorem badExtendableCentralRowPairs_eq_nil :
    badExtendableCentralRowPairs = [] := by
  native_decide

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem nonUniqueExtendableCentralRowPairs_eq_nil :
    nonUniqueExtendableCentralRowPairs = [] := by
  native_decide

theorem centerParentCandidates_length_eq_one
    {middle : List Nat × List Nat}
    (hmiddle : middle ∈ extendableCentralRowPairs) :
    (centerParentCandidates middle).length = 1 := by
  by_contra hlength
  have hmem : middle ∈ nonUniqueExtendableCentralRowPairs := by
    simp [nonUniqueExtendableCentralRowPairs, hmiddle, hlength]
  rw [nonUniqueExtendableCentralRowPairs_eq_nil] at hmem
  simp at hmem

/-- Every extendable well-behaved center has a unique substitution parent. -/
theorem existsUnique_parent_of_mem_extendableCentralRowPairs
    {middle : List Nat × List Nat}
    (hmiddle : middle ∈ extendableCentralRowPairs) :
    ∃! parent : Index, childCodeBlock parent = centralCodeBlock middle := by
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
