/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/
import LeanWang.Machine
import Mathlib.Data.Nat.Pairing

/-!
Finite Wang-tile data for the machine space-time construction.

The construction here uses local-history tiles. A tile records a `2 × 3` window:
three cells in one machine row and the corresponding three cells in the next row.
Horizontal matching overlaps two columns of both rows, while vertical matching
overlaps the next-row triple with the previous-row triple of the tile above.
-/

namespace LeanWang

/-- A cell in a machine configuration row. -/
inductive MachineCell where
  | plain (symbol : Nat)
  | head (state symbol : Nat)
deriving DecidableEq, Repr

namespace MachineCell

def symbol : MachineCell → Nat
  | plain a => a
  | head _ a => a

def isHead : MachineCell → Bool
  | plain _ => false
  | head _ _ => true

/-- Encode machine cells as Wang colors. -/
def code : MachineCell → Nat
  | plain a => 2 * a
  | head q a => 2 * Nat.pair q a + 1

end MachineCell

namespace ID

/-- Read one configuration position as a row cell for the space-time diagram. -/
def cellAt (c : ID) (i : Int) : MachineCell :=
  if i = c.head then
    MachineCell.head c.state (c.tape i)
  else
    MachineCell.plain (c.tape i)

@[simp]
theorem cellAt_head (c : ID) :
    c.cellAt c.head = MachineCell.head c.state (c.tape c.head) := by
  simp [cellAt]

theorem cellAt_of_ne {c : ID} {i : Int} (hi : i ≠ c.head) :
    c.cellAt i = MachineCell.plain (c.tape i) := by
  simp [cellAt, hi]

end ID

namespace Machine

/-- Cell in the space-time diagram after `time` steps at tape position `pos`. -/
def runCell (M : Machine) (time : Nat) (pos : Int) : MachineCell :=
  (M.runEmpty time).cellAt pos

@[simp]
theorem runCell_zero_head (M : Machine) :
    M.runCell 0 0 = MachineCell.head M.start M.blank := by
  simp [runCell, initialID, ID.cellAt]

theorem runCell_zero_of_ne {M : Machine} {pos : Int} (hpos : pos ≠ 0) :
    M.runCell 0 pos = MachineCell.plain M.blank := by
  simp [runCell, initialID, ID.cellAt, hpos]

end Machine

/-- A finite list of row cells generated from a machine's finite supports. -/
def machineCells (M : Machine) : List MachineCell :=
  (M.symbols.map MachineCell.plain) ++
    (M.states.filter (· ≠ M.halt)).flatMap fun q =>
      M.symbols.map fun a => MachineCell.head q a

/-- Pair two cell colors into one Wang color. -/
def pairCellColor (a b : MachineCell) : Nat :=
  Nat.pair a.code b.code

/-- Encode a row triple as one Wang color. -/
def tripleCellColor (a b c : MachineCell) : Nat :=
  Nat.pair a.code (Nat.pair b.code c.code)

/-- Encode the two-column overlap of two consecutive local-history tiles. -/
def overlapCellColor (prev₀ prev₁ next₀ next₁ : MachineCell) : Nat :=
  Nat.pair (pairCellColor prev₀ prev₁) (pairCellColor next₀ next₁)

/--
The local one-step update for the center cell of a three-cell window.

The result is `none` when the window asks for an impossible local update, for
example when a transition would enter the halting state. Halting cells are not
part of `machineCells`, so a global tiling cannot contain a halting head.
-/
def localNextCell? (M : Machine) (left center right : MachineCell) : Option MachineCell :=
  match left, center, right with
  | _, MachineCell.head q a, _ =>
      if _h : q = M.halt then
        none
      else
        let (write, _q', _move) := M.step q a
        some (MachineCell.plain write)
  | MachineCell.head q a, MachineCell.plain b, _ =>
      if _h : q = M.halt then
        none
      else
        let (_write, q', move) := M.step q a
        match move with
        | Move.right => if q' = M.halt then none else some (MachineCell.head q' b)
        | Move.left => some (MachineCell.plain b)
  | _, MachineCell.plain b, MachineCell.head q a =>
      if _h : q = M.halt then
        none
      else
        let (_write, q', move) := M.step q a
        match move with
        | Move.left => if q' = M.halt then none else some (MachineCell.head q' b)
        | Move.right => some (MachineCell.plain b)
  | _, MachineCell.plain b, _ =>
      some (MachineCell.plain b)

/-- A local `2 × 3` machine-history block. -/
structure MachineHistoryTile where
  prevLeft : MachineCell
  prevCenter : MachineCell
  prevRight : MachineCell
  nextLeft : MachineCell
  nextCenter : MachineCell
  nextRight : MachineCell
deriving DecidableEq, Repr

namespace MachineHistoryTile

/-- Convert a local-history block to the corresponding Wang tile. -/
def toWangTile (t : MachineHistoryTile) : WangTile where
  n := tripleCellColor t.nextLeft t.nextCenter t.nextRight
  s := tripleCellColor t.prevLeft t.prevCenter t.prevRight
  e := overlapCellColor t.prevCenter t.prevRight t.nextCenter t.nextRight
  w := overlapCellColor t.prevLeft t.prevCenter t.nextLeft t.nextCenter

@[simp]
theorem toWangTile_n (t : MachineHistoryTile) :
    t.toWangTile.n = tripleCellColor t.nextLeft t.nextCenter t.nextRight :=
  rfl

@[simp]
theorem toWangTile_s (t : MachineHistoryTile) :
    t.toWangTile.s = tripleCellColor t.prevLeft t.prevCenter t.prevRight :=
  rfl

@[simp]
theorem toWangTile_e (t : MachineHistoryTile) :
    t.toWangTile.e = overlapCellColor t.prevCenter t.prevRight t.nextCenter t.nextRight :=
  rfl

@[simp]
theorem toWangTile_w (t : MachineHistoryTile) :
    t.toWangTile.w = overlapCellColor t.prevLeft t.prevCenter t.nextLeft t.nextCenter :=
  rfl

theorem hMatches_toWangTile_iff (left right : MachineHistoryTile) :
    WangTile.HMatches left.toWangTile right.toWangTile ↔
      overlapCellColor left.prevCenter left.prevRight left.nextCenter left.nextRight =
        overlapCellColor right.prevLeft right.prevCenter right.nextLeft right.nextCenter := by
  rfl

theorem vMatches_toWangTile_iff (lower upper : MachineHistoryTile) :
    WangTile.VMatches lower.toWangTile upper.toWangTile ↔
      tripleCellColor lower.nextLeft lower.nextCenter lower.nextRight =
        tripleCellColor upper.prevLeft upper.prevCenter upper.prevRight := by
  rfl

end MachineHistoryTile

/-- All locally valid history blocks over the finite cell support of `M`. -/
def machineHistoryTiles (M : Machine) : List MachineHistoryTile := do
  let cells := machineCells M
  let prevLeft ← cells
  let prevCenter ← cells
  let prevRight ← cells
  let nextLeft ← cells
  let nextCenter ← cells
  let nextRight ← cells
  if localNextCell? M prevLeft prevCenter prevRight = some nextCenter then
    pure { prevLeft, prevCenter, prevRight, nextLeft, nextCenter, nextRight }
  else
    []

/-- The Wang tiles produced from a concrete machine by the local-history construction. -/
def machineTiles (M : Machine) : TileSet :=
  (machineHistoryTiles M).map MachineHistoryTile.toWangTile

def initialPrevLeft (M : Machine) : MachineCell :=
  MachineCell.plain M.blank

def initialPrevCenter (M : Machine) : MachineCell :=
  MachineCell.head M.start M.blank

def initialPrevRight (M : Machine) : MachineCell :=
  MachineCell.plain M.blank

def initialNextLeft (M : Machine) : MachineCell :=
  (localNextCell? M (MachineCell.plain M.blank) (MachineCell.plain M.blank)
    (MachineCell.head M.start M.blank)).getD (MachineCell.plain M.blank)

def initialNextCenter (M : Machine) : MachineCell :=
  (localNextCell? M (MachineCell.plain M.blank) (MachineCell.head M.start M.blank)
    (MachineCell.plain M.blank)).getD (MachineCell.plain M.blank)

def initialNextRight (M : Machine) : MachineCell :=
  (localNextCell? M (MachineCell.head M.start M.blank) (MachineCell.plain M.blank)
    (MachineCell.plain M.blank)).getD (MachineCell.plain M.blank)

/-- The local-history block forced at the lower-left corner. -/
def initialHistoryTile (M : Machine) : MachineHistoryTile where
  prevLeft := initialPrevLeft M
  prevCenter := initialPrevCenter M
  prevRight := initialPrevRight M
  nextLeft := initialNextLeft M
  nextCenter := initialNextCenter M
  nextRight := initialNextRight M

/-- The distinguished lower-left tile forcing the empty-input initial configuration. -/
def machineSeed (M : Machine) : WangTile :=
  (initialHistoryTile M).toWangTile

@[simp]
theorem machineSeed_eq (M : Machine) :
    machineSeed M = (initialHistoryTile M).toWangTile :=
  rfl

end LeanWang
