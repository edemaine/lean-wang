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

/-- A machine cell is supported by a machine's finite symbol and state sets. -/
def Mem (M : Machine) : MachineCell → Prop
  | plain a => a ∈ M.symbols
  | head q a => q ∈ M.states ∧ q ≠ M.halt ∧ a ∈ M.symbols

/-- Encode machine cells as Wang colors. -/
def code : MachineCell → Nat
  | plain a => Nat.pair 0 a
  | head q a => Nat.pair 1 (Nat.pair q a)

theorem code_injective : Function.Injective code := by
  intro c d h
  cases c with
  | plain a =>
      cases d with
      | plain b =>
          have hb : a = b := (Nat.pair_eq_pair.mp h).2
          simp [hb]
      | head q b =>
          have htag : 0 = 1 := (Nat.pair_eq_pair.mp h).1
          cases htag
  | head q a =>
      cases d with
      | plain b =>
          have htag : 1 = 0 := (Nat.pair_eq_pair.mp h).1
          cases htag
      | head r b =>
          have hpair : Nat.pair q a = Nat.pair r b := (Nat.pair_eq_pair.mp h).2
          rcases Nat.pair_eq_pair.mp hpair with ⟨hq, ha⟩
          simp [hq, ha]

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

@[simp]
theorem plain_mem_machineCells_iff (M : Machine) (a : Nat) :
    MachineCell.plain a ∈ machineCells M ↔ a ∈ M.symbols := by
  simp [machineCells]

@[simp]
theorem head_mem_machineCells_iff (M : Machine) (q a : Nat) :
    MachineCell.head q a ∈ machineCells M ↔
      q ∈ M.states ∧ q ≠ M.halt ∧ a ∈ M.symbols := by
  simp [machineCells, and_assoc]

theorem mem_machineCells_iff (M : Machine) (c : MachineCell) :
    c ∈ machineCells M ↔ c.Mem M := by
  cases c <;> simp [MachineCell.Mem]

theorem mem_machineCells_of_mem {M : Machine} {c : MachineCell} :
    c.Mem M → c ∈ machineCells M :=
  (mem_machineCells_iff M c).2

theorem mem_of_mem_machineCells {M : Machine} {c : MachineCell} :
    c ∈ machineCells M → c.Mem M :=
  (mem_machineCells_iff M c).1

/-- Pair two cell colors into one Wang color. -/
def pairCellColor (a b : MachineCell) : Nat :=
  Nat.pair a.code b.code

theorem pairCellColor_eq_iff {a b c d : MachineCell} :
    pairCellColor a b = pairCellColor c d ↔ a = c ∧ b = d := by
  unfold pairCellColor
  rw [Nat.pair_eq_pair]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨MachineCell.code_injective ha, MachineCell.code_injective hb⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Encode a row triple as one Wang color. -/
def tripleCellColor (a b c : MachineCell) : Nat :=
  Nat.pair a.code (Nat.pair b.code c.code)

theorem tripleCellColor_eq_iff {a b c d e f : MachineCell} :
    tripleCellColor a b c = tripleCellColor d e f ↔ a = d ∧ b = e ∧ c = f := by
  unfold tripleCellColor
  rw [Nat.pair_eq_pair, Nat.pair_eq_pair]
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨MachineCell.code_injective ha,
      MachineCell.code_injective hb, MachineCell.code_injective hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩

/-- Encode the two-column overlap of two consecutive local-history tiles. -/
def overlapCellColor (prev₀ prev₁ next₀ next₁ : MachineCell) : Nat :=
  Nat.pair (pairCellColor prev₀ prev₁) (pairCellColor next₀ next₁)

theorem overlapCellColor_eq_iff {a b c d e f g h : MachineCell} :
    overlapCellColor a b c d = overlapCellColor e f g h ↔
      a = e ∧ b = f ∧ c = g ∧ d = h := by
  unfold overlapCellColor
  rw [Nat.pair_eq_pair, pairCellColor_eq_iff, pairCellColor_eq_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    exact ⟨ha, hb, hc, hd⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩

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

set_option linter.flexible false in
theorem localNextCell?_mem {M : Machine} {left center right next : MachineCell}
    (hleft : left.Mem M) (hcenter : center.Mem M) (hright : right.Mem M)
    (hnext : localNextCell? M left center right = some next) :
    next.Mem M := by
  cases left with
  | plain la =>
      cases center with
      | plain ca =>
          cases right with
          | plain ra =>
              simp [localNextCell?] at hnext
              cases hnext
              exact hcenter
          | head rq ra =>
              simp [localNextCell?, MachineCell.Mem] at hcenter hright hnext ⊢
              by_cases hrq : rq = M.halt
              · simp [hrq] at hnext
              · simp [hrq] at hnext
                rcases hright with ⟨hrqState, _hrqHalt, hraSym⟩
                rcases hstep : M.step rq ra with ⟨write, q', move⟩
                simp [hstep] at hnext
                cases move with
                | left =>
                    by_cases hq' : q' = M.halt
                    · rw [if_pos hq'] at hnext
                      cases hnext
                    · rw [if_neg hq'] at hnext
                      cases hnext
                      exact ⟨by simpa [hstep] using M.step_state_mem rq ra hrqState hraSym,
                        hq', hcenter⟩
                | right =>
                    cases hnext
                    exact hcenter
      | head cq ca =>
          cases right with
          | plain ra =>
              simp [localNextCell?, MachineCell.Mem] at hcenter hnext ⊢
              rcases hcenter with ⟨hcqState, hcqHalt, hcaSym⟩
              simp [hcqHalt] at hnext
              rcases hstep : M.step cq ca with ⟨write, q', move⟩
              simp [hstep] at hnext
              cases hnext
              simpa [hstep, MachineCell.Mem] using M.step_symbol_mem cq ca hcqState hcaSym
          | head rq ra =>
              simp [localNextCell?, MachineCell.Mem] at hcenter hnext ⊢
              rcases hcenter with ⟨hcqState, hcqHalt, hcaSym⟩
              simp [hcqHalt] at hnext
              rcases hstep : M.step cq ca with ⟨write, q', move⟩
              simp [hstep] at hnext
              cases hnext
              simpa [hstep, MachineCell.Mem] using M.step_symbol_mem cq ca hcqState hcaSym
  | head lq la =>
      cases center with
      | plain ca =>
          cases right with
          | plain ra =>
              simp [localNextCell?, MachineCell.Mem] at hleft hcenter hnext ⊢
              rcases hleft with ⟨hlqState, hlqHalt, hlaSym⟩
              simp [hlqHalt] at hnext
              rcases hstep : M.step lq la with ⟨write, q', move⟩
              simp [hstep] at hnext
              cases move with
              | left =>
                  cases hnext
                  exact hcenter
              | right =>
                  by_cases hq' : q' = M.halt
                  · rw [if_pos hq'] at hnext
                    cases hnext
                  · rw [if_neg hq'] at hnext
                    cases hnext
                    exact ⟨by simpa [hstep] using M.step_state_mem lq la hlqState hlaSym,
                      hq', hcenter⟩
          | head rq ra =>
              simp [localNextCell?, MachineCell.Mem] at hleft hcenter hnext ⊢
              rcases hleft with ⟨hlqState, hlqHalt, hlaSym⟩
              simp [hlqHalt] at hnext
              rcases hstep : M.step lq la with ⟨write, q', move⟩
              simp [hstep] at hnext
              cases move with
              | left =>
                  cases hnext
                  exact hcenter
              | right =>
                  by_cases hq' : q' = M.halt
                  · rw [if_pos hq'] at hnext
                    cases hnext
                  · rw [if_neg hq'] at hnext
                    cases hnext
                    exact ⟨by simpa [hstep] using M.step_state_mem lq la hlqState hlaSym,
                      hq', hcenter⟩
      | head cq ca =>
          cases right with
          | plain ra =>
              simp [localNextCell?, MachineCell.Mem] at hcenter hnext ⊢
              rcases hcenter with ⟨hcqState, hcqHalt, hcaSym⟩
              simp [hcqHalt] at hnext
              rcases hstep : M.step cq ca with ⟨write, q', move⟩
              simp [hstep] at hnext
              cases hnext
              simpa [hstep, MachineCell.Mem] using M.step_symbol_mem cq ca hcqState hcaSym
          | head rq ra =>
              simp [localNextCell?, MachineCell.Mem] at hcenter hnext ⊢
              rcases hcenter with ⟨hcqState, hcqHalt, hcaSym⟩
              simp [hcqHalt] at hnext
              rcases hstep : M.step cq ca with ⟨write, q', move⟩
              simp [hstep] at hnext
              cases hnext
              simpa [hstep, MachineCell.Mem] using M.step_symbol_mem cq ca hcqState hcaSym

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

theorem mem_machineHistoryTiles_iff (M : Machine) (t : MachineHistoryTile) :
    t ∈ machineHistoryTiles M ↔
      t.prevLeft ∈ machineCells M ∧
      t.prevCenter ∈ machineCells M ∧
      t.prevRight ∈ machineCells M ∧
      t.nextLeft ∈ machineCells M ∧
      t.nextCenter ∈ machineCells M ∧
      t.nextRight ∈ machineCells M ∧
      localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter := by
  cases t
  simp [machineHistoryTiles]

theorem mem_machineHistoryTiles_of_supported {M : Machine} {t : MachineHistoryTile}
    (hprevLeft : t.prevLeft.Mem M) (hprevCenter : t.prevCenter.Mem M)
    (hprevRight : t.prevRight.Mem M) (hnextLeft : t.nextLeft.Mem M)
    (hnextCenter : t.nextCenter.Mem M) (hnextRight : t.nextRight.Mem M)
    (hlocal : localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter) :
    t ∈ machineHistoryTiles M := by
  rw [mem_machineHistoryTiles_iff]
  exact ⟨mem_machineCells_of_mem hprevLeft,
    mem_machineCells_of_mem hprevCenter,
    mem_machineCells_of_mem hprevRight,
    mem_machineCells_of_mem hnextLeft,
    mem_machineCells_of_mem hnextCenter,
    mem_machineCells_of_mem hnextRight,
    hlocal⟩

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
