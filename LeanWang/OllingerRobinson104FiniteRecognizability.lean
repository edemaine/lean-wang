/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104Recognizability

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

def fourRows : List (List Nat) := compatibleRows hFollowerTable 4

def rowsVCompatible (table : List (List Nat)) (lower upper : List Nat) : Bool :=
  (lower.zip upper).all fun pair =>
    decide (pair.2 ∈ followersAt table pair.1)

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

def codeOfIndex (index : Index) : Nat :=
  codes.find? (fun code => tileAtCode code == Closed104.tile (components index)) |>.getD 0

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

end FiniteRecognizability
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
