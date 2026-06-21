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
  | boundary
  | plain (symbol : Nat)
  | head (state symbol : Nat)
deriving DecidableEq, Repr

namespace MachineCell

def symbol : MachineCell → Nat
  | boundary => 0
  | plain a => a
  | head _ a => a

def isHead : MachineCell → Bool
  | boundary => false
  | plain _ => false
  | head _ _ => true

/-- A machine cell is supported by a machine's finite symbol and state sets. -/
def Mem (M : Machine) : MachineCell → Prop
  | boundary => True
  | plain a => a ∈ M.symbols
  | head q a => q ∈ M.states ∧ q ≠ M.halt ∧ a ∈ M.symbols

/-- Encode machine cells as Wang colors. -/
def code : MachineCell → Nat
  | boundary => Nat.pair 2 0
  | plain a => Nat.pair 0 a
  | head q a => Nat.pair 1 (Nat.pair q a)

theorem code_injective : Function.Injective code := by
  intro c d h
  cases c with
  | boundary =>
      cases d with
      | boundary => rfl
      | plain b =>
          have htag : 2 = 0 := (Nat.pair_eq_pair.mp h).1
          cases htag
      | head q b =>
          have htag : 2 = 1 := (Nat.pair_eq_pair.mp h).1
          cases htag
  | plain a =>
      cases d with
      | boundary =>
          have htag : 0 = 2 := (Nat.pair_eq_pair.mp h).1
          cases htag
      | plain b =>
          have hb : a = b := (Nat.pair_eq_pair.mp h).2
          simp [hb]
      | head q b =>
          have htag : 0 = 1 := (Nat.pair_eq_pair.mp h).1
          cases htag
  | head q a =>
      cases d with
      | boundary =>
          have htag : 1 = 2 := (Nat.pair_eq_pair.mp h).1
          cases htag
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
def cellAt (c : ID) (i : Nat) : MachineCell :=
  if i = c.head then
    MachineCell.head c.state (c.tape i)
  else
    MachineCell.plain (c.tape i)

@[simp]
theorem cellAt_head (c : ID) :
    c.cellAt c.head = MachineCell.head c.state (c.tape c.head) := by
  simp [cellAt]

theorem cellAt_of_ne {c : ID} {i : Nat} (hi : i ≠ c.head) :
    c.cellAt i = MachineCell.plain (c.tape i) := by
  simp [cellAt, hi]

/-- The cell immediately left of a position, using a boundary marker at `0`. -/
def cellAtLeft (c : ID) : Nat → MachineCell
  | 0 => MachineCell.boundary
  | i + 1 => c.cellAt i

@[simp]
theorem cellAtLeft_zero (c : ID) :
    c.cellAtLeft 0 = MachineCell.boundary :=
  rfl

@[simp]
theorem cellAtLeft_succ (c : ID) (i : Nat) :
    c.cellAtLeft (i + 1) = c.cellAt i :=
  rfl

/-- A machine configuration uses only the finite supports declared by `M`. -/
def Mem (M : Machine) (c : ID) : Prop :=
  c.state ∈ M.states ∧ ∀ i : Nat, c.tape i ∈ M.symbols

theorem cellAt_mem {M : Machine} {c : ID} (hc : c.Mem M)
    (hstate : c.state ≠ M.halt) (i : Nat) :
    (c.cellAt i).Mem M := by
  by_cases hi : i = c.head
  · subst i
    simp [cellAt, MachineCell.Mem, hc.1, hstate, hc.2]
  · simp [cellAt, hi, MachineCell.Mem, hc.2]

theorem cellAtLeft_mem {M : Machine} {c : ID} (hc : c.Mem M)
    (hstate : c.state ≠ M.halt) (i : Nat) :
    (c.cellAtLeft i).Mem M := by
  cases i with
  | zero =>
      simp [cellAtLeft, MachineCell.Mem]
  | succ i =>
      simpa [cellAtLeft] using cellAt_mem hc hstate i

end ID

namespace Machine

/-- Cell in the space-time diagram after `time` steps at tape position `pos`. -/
def runCell (M : Machine) (time : Nat) (pos : Nat) : MachineCell :=
  (M.runEmpty time).cellAt pos

/-- Left neighbor for a one-sided space-time row, using the boundary marker at `0`. -/
def runCellLeft (M : Machine) (time pos : Nat) : MachineCell :=
  (M.runEmpty time).cellAtLeft pos

@[simp]
theorem runCell_zero_head (M : Machine) :
    M.runCell 0 0 = MachineCell.head M.start M.blank := by
  simp [runCell, initialID, ID.cellAt]

theorem runCell_zero_of_ne {M : Machine} {pos : Nat} (hpos : pos ≠ 0) :
    M.runCell 0 pos = MachineCell.plain M.blank := by
  simp [runCell, initialID, ID.cellAt, hpos]

theorem initialID_mem (M : Machine) :
    M.initialID.Mem M := by
  constructor
  · exact M.start_mem
  · intro _
    exact M.blank_mem

theorem nextID_mem {M : Machine} {c : ID} (hc : c.Mem M) :
    (M.nextID c).Mem M := by
  by_cases hhalt : c.state = M.halt
  · simpa [nextID, hhalt] using hc
  · rw [nextID, if_neg hhalt]
    rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
    constructor
    · simpa [hstep] using M.step_state_mem c.state (c.tape c.head) hc.1 (hc.2 c.head)
    · intro i
      by_cases hi : i = c.head
      · simp [hi]
        simpa [hstep] using M.step_symbol_mem c.state (c.tape c.head) hc.1 (hc.2 c.head)
      · simp [hi, hc.2 i]

theorem runEmpty_mem (M : Machine) (n : Nat) :
    (M.runEmpty n).Mem M := by
  induction n with
  | zero =>
      simpa using M.initialID_mem
  | succ n ih =>
      rw [runEmpty_succ]
      exact nextID_mem ih

theorem runEmpty_state_ne_halt_of_not_halts {M : Machine}
    (h : ¬ M.HaltsEmpty) (n : Nat) :
    (M.runEmpty n).state ≠ M.halt := by
  intro hn
  exact h ⟨n, hn⟩

theorem runCell_mem_of_not_halts {M : Machine} (h : ¬ M.HaltsEmpty)
    (time pos : Nat) :
    (M.runCell time pos).Mem M := by
  exact ID.cellAt_mem (M.runEmpty_mem time)
    (M.runEmpty_state_ne_halt_of_not_halts h time) pos

theorem runCellLeft_mem_of_not_halts {M : Machine} (h : ¬ M.HaltsEmpty)
    (time pos : Nat) :
    (M.runCellLeft time pos).Mem M := by
  exact ID.cellAtLeft_mem (M.runEmpty_mem time)
    (M.runEmpty_state_ne_halt_of_not_halts h time) pos

end Machine

/-- A finite list of row cells generated from a machine's finite supports. -/
def machineCells (M : Machine) : List MachineCell :=
  MachineCell.boundary :: (M.symbols.map MachineCell.plain) ++
    (M.states.filter (· ≠ M.halt)).flatMap fun q =>
      M.symbols.map fun a => MachineCell.head q a

@[simp]
theorem boundary_mem_machineCells (M : Machine) :
    MachineCell.boundary ∈ machineCells M := by
  simp [machineCells]

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
  | _, MachineCell.boundary, _ => none
  | _, MachineCell.head q a, _ =>
      if _h : q = M.halt then
        none
      else
        let (write, q', move) := M.step q a
        match left, move with
        | MachineCell.boundary, Move.left =>
            if q' = M.halt then none else some (MachineCell.head q' write)
        | _, _ => some (MachineCell.plain write)
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
  | MachineCell.boundary, MachineCell.plain b, _ =>
      some (MachineCell.plain b)
  | _, MachineCell.plain b, _ =>
      some (MachineCell.plain b)

namespace Machine

theorem localNextCell?_at_head {M : Machine} {c : ID}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).2.1 ≠ M.halt) :
    localNextCell? M (c.cellAtLeft c.head) (c.cellAt c.head) (c.cellAt (c.head + 1)) =
      some ((M.nextID c).cellAt c.head) := by
  rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
  cases hhead : c.head with
  | zero =>
      cases move with
      | left =>
          have hstep0 : M.step c.state (c.tape 0) = (write, state', Move.left) := by
            simpa [hhead] using hstep
          have hstate' : state' ≠ M.halt := by
            simpa [hstep] using hnextState
          simp [ID.cellAt, Machine.nextID, hstate, hhead, hstep0,
            localNextCell?, Move.apply, hstate']
      | right =>
          have hstep0 : M.step c.state (c.tape 0) = (write, state', Move.right) := by
            simpa [hhead] using hstep
          simp [ID.cellAt, Machine.nextID, hstate, hhead, hstep0,
            localNextCell?, Move.apply]
  | succ pred =>
      cases move with
      | left =>
          have hstepPred :
              M.step c.state (c.tape (pred + 1)) = (write, state', Move.left) := by
            simpa [hhead] using hstep
          simp [ID.cellAt, ID.cellAtLeft, Machine.nextID, hstate, hhead, hstepPred,
            localNextCell?, Move.apply]
      | right =>
          have hstepPred :
              M.step c.state (c.tape (pred + 1)) = (write, state', Move.right) := by
            simpa [hhead] using hstep
          simp [ID.cellAt, ID.cellAtLeft, Machine.nextID, hstate, hhead, hstepPred,
            localNextCell?, Move.apply]

theorem localNextCell?_left_of_head {M : Machine} {c : ID} {pos : Nat}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).2.1 ≠ M.halt)
    (hhead : c.head = pos + 1) :
    localNextCell? M (c.cellAtLeft pos) (c.cellAt pos) (c.cellAt (pos + 1)) =
      some ((M.nextID c).cellAt pos) := by
  rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
  cases hpos : pos with
  | zero =>
      cases move with
      | left =>
          have hstep0 : M.step c.state (c.tape 1) = (write, state', Move.left) := by
            simpa [hhead, hpos] using hstep
          have hstate' : state' ≠ M.halt := by
            simpa [hstep] using hnextState
          simp [ID.cellAt, ID.cellAtLeft, Machine.nextID, hstate, hhead, hpos,
            hstep0, localNextCell?, Move.apply, hstate']
      | right =>
          have hstep0 : M.step c.state (c.tape 1) = (write, state', Move.right) := by
            simpa [hhead, hpos] using hstep
          simp [ID.cellAt, ID.cellAtLeft, Machine.nextID, hstate, hhead, hpos,
            hstep0, localNextCell?, Move.apply]
  | succ pred =>
      cases move with
      | left =>
          have hstepPred :
              M.step c.state (c.tape (pred + 1 + 1)) = (write, state', Move.left) := by
            simpa [hhead, hpos] using hstep
          have hpred : pred ≠ pred + 1 + 1 := by
            exact Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide : 0 < 1 + 1))
          have hstate' : state' ≠ M.halt := by
            simpa [hstep] using hnextState
          simp [ID.cellAt, ID.cellAtLeft, Machine.nextID, hstate, hhead, hpos,
            hstepPred, localNextCell?, Move.apply, hpred, hstate']
      | right =>
          have hstepPred :
              M.step c.state (c.tape (pred + 1 + 1)) = (write, state', Move.right) := by
            simpa [hhead, hpos] using hstep
          have hpred : pred ≠ pred + 1 + 1 := by
            exact Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide : 0 < 1 + 1))
          simp [ID.cellAt, ID.cellAtLeft, Machine.nextID, hstate, hhead, hpos,
            hstepPred, localNextCell?, Move.apply, hpred]

theorem localNextCell?_right_of_head {M : Machine} {c : ID}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).2.1 ≠ M.halt) :
    localNextCell? M (c.cellAtLeft (c.head + 1)) (c.cellAt (c.head + 1))
        (c.cellAt (c.head + 1 + 1)) =
      some ((M.nextID c).cellAt (c.head + 1)) := by
  rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
  cases hhead : c.head with
  | zero =>
      cases move with
      | left =>
          have hstep0 : M.step c.state (c.tape 0) = (write, state', Move.left) := by
            simpa [hhead] using hstep
          simp [ID.cellAt, ID.cellAtLeft, Machine.nextID, hstate, hhead, hstep0,
            localNextCell?, Move.apply]
      | right =>
          have hstep0 : M.step c.state (c.tape 0) = (write, state', Move.right) := by
            simpa [hhead] using hstep
          have hstate' : state' ≠ M.halt := by
            simpa [hstep] using hnextState
          simp [ID.cellAt, ID.cellAtLeft, Machine.nextID, hstate, hhead, hstep0,
            localNextCell?, Move.apply, hstate']
  | succ pred =>
      cases move with
      | left =>
          have hstepPred :
              M.step c.state (c.tape (pred + 1)) = (write, state', Move.left) := by
            simpa [hhead] using hstep
          have hpred : pred + 1 + 1 ≠ pred := by
            exact Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide : 0 < 1 + 1))
          simp [ID.cellAt, ID.cellAtLeft, Machine.nextID, hstate, hhead, hstepPred,
            localNextCell?, Move.apply, hpred]
      | right =>
          have hstepPred :
              M.step c.state (c.tape (pred + 1)) = (write, state', Move.right) := by
            simpa [hhead] using hstep
          have hstate' : state' ≠ M.halt := by
            simpa [hstep] using hnextState
          simp [ID.cellAt, ID.cellAtLeft, Machine.nextID, hstate, hhead, hstepPred,
            localNextCell?, Move.apply, hstate']

theorem localNextCell?_away_from_head {M : Machine} {c : ID} {pos : Nat}
    (hstate : c.state ≠ M.halt)
    (hcenter : pos ≠ c.head)
    (hrightOld : pos + 1 ≠ c.head)
    (hleftOld : c.head + 1 ≠ pos) :
    localNextCell? M (c.cellAtLeft pos) (c.cellAt pos) (c.cellAt (pos + 1)) =
      some ((M.nextID c).cellAt pos) := by
  rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
  cases hpos : pos with
  | zero =>
      cases hhead : c.head with
      | zero =>
          omega
      | succ pred =>
          cases move <;>
            (simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID, localNextCell?,
              Move.apply]
             try omega)
  | succ posPred =>
      cases hhead : c.head with
      | zero =>
          cases move <;>
            simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID, localNextCell?,
              Move.apply]
      | succ headPred =>
          have hleftCell : posPred ≠ headPred + 1 := by omega
          have hcenterCell : posPred ≠ headPred := by omega
          have hrightCell : posPred + 1 + 1 ≠ headPred + 1 := by omega
          have hnewLeft : posPred + 1 ≠ headPred := by omega
          have hnewRight : posPred + 1 ≠ headPred + 1 + 1 := by omega
          cases move <;>
            simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID, localNextCell?,
              Move.apply]

theorem localNextCell?_cellAt {M : Machine} {c : ID} {pos : Nat}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).2.1 ≠ M.halt) :
    localNextCell? M (c.cellAtLeft pos) (c.cellAt pos) (c.cellAt (pos + 1)) =
      some ((M.nextID c).cellAt pos) := by
  by_cases hcenter : pos = c.head
  · subst pos
    exact localNextCell?_at_head hstate hnextState
  · by_cases hleft : c.head = pos + 1
    · exact localNextCell?_left_of_head hstate hnextState hleft
    · by_cases hright : pos = c.head + 1
      · subst pos
        exact localNextCell?_right_of_head hstate hnextState
      · exact localNextCell?_away_from_head hstate hcenter (by
          intro h
          exact hleft h.symm) (by
          intro h
          exact hright h.symm)

end Machine

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

theorem hMatches_toWangTile_iff_cells (left right : MachineHistoryTile) :
    WangTile.HMatches left.toWangTile right.toWangTile ↔
      left.prevCenter = right.prevLeft ∧
        left.prevRight = right.prevCenter ∧
        left.nextCenter = right.nextLeft ∧
        left.nextRight = right.nextCenter := by
  rw [hMatches_toWangTile_iff, overlapCellColor_eq_iff]

theorem vMatches_toWangTile_iff (lower upper : MachineHistoryTile) :
    WangTile.VMatches lower.toWangTile upper.toWangTile ↔
      tripleCellColor lower.nextLeft lower.nextCenter lower.nextRight =
        tripleCellColor upper.prevLeft upper.prevCenter upper.prevRight := by
  rfl

theorem vMatches_toWangTile_iff_cells (lower upper : MachineHistoryTile) :
    WangTile.VMatches lower.toWangTile upper.toWangTile ↔
      lower.nextLeft = upper.prevLeft ∧
        lower.nextCenter = upper.prevCenter ∧
        lower.nextRight = upper.prevRight := by
  rw [vMatches_toWangTile_iff, tripleCellColor_eq_iff]

theorem toWangTile_injective : Function.Injective toWangTile := by
  intro t u h
  have hs : tripleCellColor t.prevLeft t.prevCenter t.prevRight =
      tripleCellColor u.prevLeft u.prevCenter u.prevRight := by
    simpa [toWangTile] using congrArg WangTile.s h
  have hn : tripleCellColor t.nextLeft t.nextCenter t.nextRight =
      tripleCellColor u.nextLeft u.nextCenter u.nextRight := by
    simpa [toWangTile] using congrArg WangTile.n h
  rw [tripleCellColor_eq_iff] at hs hn
  cases t
  cases u
  simp_all

theorem toWangTile_eq_iff {t u : MachineHistoryTile} :
    t.toWangTile = u.toWangTile ↔ t = u := by
  constructor
  · intro h
    exact toWangTile_injective h
  · intro h
    rw [h]

end MachineHistoryTile

/-- The local-history block cut from two consecutive rows of an actual machine run. -/
def runHistoryTile (M : Machine) (time pos : Nat) : MachineHistoryTile where
  prevLeft := M.runCellLeft time pos
  prevCenter := M.runCell time pos
  prevRight := M.runCell time (pos + 1)
  nextLeft := M.runCellLeft (time + 1) pos
  nextCenter := M.runCell (time + 1) pos
  nextRight := M.runCell (time + 1) (pos + 1)

theorem runHistoryTile_cells_mem_of_not_halts {M : Machine} (h : ¬ M.HaltsEmpty)
    (time pos : Nat) :
    (runHistoryTile M time pos).prevLeft.Mem M ∧
      (runHistoryTile M time pos).prevCenter.Mem M ∧
      (runHistoryTile M time pos).prevRight.Mem M ∧
      (runHistoryTile M time pos).nextLeft.Mem M ∧
      (runHistoryTile M time pos).nextCenter.Mem M ∧
      (runHistoryTile M time pos).nextRight.Mem M := by
  simp [runHistoryTile, M.runCellLeft_mem_of_not_halts h,
    M.runCell_mem_of_not_halts h]

theorem runHistoryTile_hMatches (M : Machine) (time pos : Nat) :
    WangTile.HMatches (runHistoryTile M time pos).toWangTile
      (runHistoryTile M time (pos + 1)).toWangTile := by
  simp [WangTile.HMatches, MachineHistoryTile.toWangTile,
    runHistoryTile, Machine.runCellLeft, Machine.runCell, Machine.runEmpty_succ]

theorem runHistoryTile_vMatches (M : Machine) (time pos : Nat) :
    WangTile.VMatches (runHistoryTile M time pos).toWangTile
      (runHistoryTile M (time + 1) pos).toWangTile := by
  simp [WangTile.VMatches, MachineHistoryTile.toWangTile, runHistoryTile]

theorem runHistoryTile_local_of_not_halts {M : Machine} (h : ¬ M.HaltsEmpty)
    (time pos : Nat) :
    localNextCell? M (runHistoryTile M time pos).prevLeft
        (runHistoryTile M time pos).prevCenter
        (runHistoryTile M time pos).prevRight =
      some (runHistoryTile M time pos).nextCenter := by
  let c := M.runEmpty time
  have hstate : c.state ≠ M.halt := by
    exact M.runEmpty_state_ne_halt_of_not_halts h time
  have hnextRun : (M.runEmpty (time + 1)).state ≠ M.halt := by
    exact M.runEmpty_state_ne_halt_of_not_halts h (time + 1)
  have hnextState : (M.step c.state (c.tape c.head)).2.1 ≠ M.halt := by
    rw [← Machine.nextID_state_of_ne_halt hstate]
    simpa [c, Machine.runEmpty_succ] using hnextRun
  simpa [runHistoryTile, Machine.runCell, Machine.runCellLeft, c,
    Machine.runEmpty_succ] using
    Machine.localNextCell?_cellAt (M := M) (c := c) (pos := pos) hstate hnextState

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

theorem runHistoryTile_mem_machineHistoryTiles_of_not_halts {M : Machine}
    (h : ¬ M.HaltsEmpty) (time pos : Nat) :
    runHistoryTile M time pos ∈ machineHistoryTiles M := by
  rcases runHistoryTile_cells_mem_of_not_halts h time pos with
    ⟨hprevLeft, hprevCenter, hprevRight, hnextLeft, hnextCenter, hnextRight⟩
  exact mem_machineHistoryTiles_of_supported hprevLeft hprevCenter hprevRight
    hnextLeft hnextCenter hnextRight
    (runHistoryTile_local_of_not_halts h time pos)

/-- The Wang tiles produced from a concrete machine by the local-history construction. -/
def machineTiles (M : Machine) : TileSet :=
  (machineHistoryTiles M).map MachineHistoryTile.toWangTile

theorem mem_machineTiles_iff (M : Machine) (tile : WangTile) :
    tile ∈ machineTiles M ↔
      ∃ t : MachineHistoryTile, t ∈ machineHistoryTiles M ∧ t.toWangTile = tile := by
  simp [machineTiles]

theorem toWangTile_mem_machineTiles {M : Machine} {t : MachineHistoryTile}
    (ht : t ∈ machineHistoryTiles M) :
    t.toWangTile ∈ machineTiles M := by
  rw [mem_machineTiles_iff]
  exact ⟨t, ht, rfl⟩

theorem toWangTile_mem_machineTiles_iff (M : Machine) (t : MachineHistoryTile) :
    t.toWangTile ∈ machineTiles M ↔ t ∈ machineHistoryTiles M := by
  constructor
  · intro ht
    rcases (mem_machineTiles_iff M t.toWangTile).1 ht with ⟨u, hu, htile⟩
    exact MachineHistoryTile.toWangTile_injective htile
      ▸ hu
  · exact toWangTile_mem_machineTiles

theorem toWangTile_mem_machineTiles_of_supported {M : Machine} {t : MachineHistoryTile}
    (hprevLeft : t.prevLeft.Mem M) (hprevCenter : t.prevCenter.Mem M)
    (hprevRight : t.prevRight.Mem M) (hnextLeft : t.nextLeft.Mem M)
    (hnextCenter : t.nextCenter.Mem M) (hnextRight : t.nextRight.Mem M)
    (hlocal : localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter) :
    t.toWangTile ∈ machineTiles M :=
  toWangTile_mem_machineTiles
    (mem_machineHistoryTiles_of_supported hprevLeft hprevCenter hprevRight
      hnextLeft hnextCenter hnextRight hlocal)

def initialPrevLeft (_M : Machine) : MachineCell :=
  MachineCell.boundary

def initialPrevCenter (M : Machine) : MachineCell :=
  MachineCell.head M.start M.blank

def initialPrevRight (M : Machine) : MachineCell :=
  MachineCell.plain M.blank

def initialNextLeft (_M : Machine) : MachineCell :=
  MachineCell.boundary

def initialNextCenter (M : Machine) : MachineCell :=
  (localNextCell? M MachineCell.boundary (MachineCell.head M.start M.blank)
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

theorem initialHistoryTile_eq_runHistoryTile_zero_of_not_halts {M : Machine}
    (h : ¬ M.HaltsEmpty) :
    initialHistoryTile M = runHistoryTile M 0 0 := by
  have hstart : M.start ≠ M.halt := by
    intro hs
    exact h ⟨0, by simpa [Machine.runEmpty_zero, Machine.initialID] using hs⟩
  rcases hstep : M.step M.start M.blank with ⟨write, q', move⟩
  have hq' : q' ≠ M.halt := by
    intro hhalt
    exact h ⟨1, by
      simp [Machine.runEmpty_succ, Machine.runEmpty_zero, Machine.nextID,
        Machine.initialID, hstart, hstep, hhalt]⟩
  cases move <;>
    simp [initialHistoryTile, runHistoryTile, initialPrevLeft, initialPrevCenter,
      initialPrevRight, initialNextLeft, initialNextCenter, initialNextRight,
      Machine.runCell, Machine.runCellLeft, Machine.runEmpty_succ,
      Machine.runEmpty_zero, Machine.nextID, Machine.initialID, ID.cellAt,
      localNextCell?, Move.apply, hstart, hstep, hq']

/-- The distinguished lower-left tile forcing the empty-input initial configuration. -/
def machineSeed (M : Machine) : WangTile :=
  (initialHistoryTile M).toWangTile

@[simp]
theorem machineSeed_eq (M : Machine) :
    machineSeed M = (initialHistoryTile M).toWangTile :=
  rfl

theorem tilesQuarterWithSeed_machineTiles_of_not_halts {M : Machine}
    (h : ¬ M.HaltsEmpty) :
    TilesQuarterWithSeed (machineTiles M) (machineSeed M) := by
  let x : Nat × Nat → TileIn (machineTiles M) := fun p =>
    ⟨(runHistoryTile M p.2 p.1).toWangTile,
      toWangTile_mem_machineTiles
        (runHistoryTile_mem_machineHistoryTiles_of_not_halts h p.2 p.1)⟩
  refine ⟨x, ?_, ?_⟩
  · constructor
    · intro p
      exact runHistoryTile_hMatches M p.2 p.1
    · intro p
      exact runHistoryTile_vMatches M p.2 p.1
  · simp [x, machineSeed_eq, initialHistoryTile_eq_runHistoryTile_zero_of_not_halts h]

end LeanWang
