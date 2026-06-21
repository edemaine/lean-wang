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

def initialRowTag : Nat := 0

def normalRowTag : Nat := 1

theorem initialRowTag_ne_normalRowTag :
    initialRowTag ≠ normalRowTag := by
  decide

def taggedTripleCellColor (tag : Nat) (a b c : MachineCell) : Nat :=
  Nat.pair tag (tripleCellColor a b c)

theorem taggedTripleCellColor_eq_iff {tag tag' : Nat}
    {a b c d e f : MachineCell} :
    taggedTripleCellColor tag a b c = taggedTripleCellColor tag' d e f ↔
      tag = tag' ∧ a = d ∧ b = e ∧ c = f := by
  unfold taggedTripleCellColor
  rw [Nat.pair_eq_pair, tripleCellColor_eq_iff]

def taggedOverlapCellColor (tag : Nat)
    (prev₀ prev₁ next₀ next₁ : MachineCell) : Nat :=
  Nat.pair tag (overlapCellColor prev₀ prev₁ next₀ next₁)

theorem taggedOverlapCellColor_eq_iff {tag tag' : Nat}
    {a b c d e f g h : MachineCell} :
    taggedOverlapCellColor tag a b c d = taggedOverlapCellColor tag' e f g h ↔
      tag = tag' ∧ a = e ∧ b = f ∧ c = g ∧ d = h := by
  unfold taggedOverlapCellColor
  rw [Nat.pair_eq_pair, overlapCellColor_eq_iff]

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

/--
Convert a local-history block to a Wang tile carrying row-mode tags.

The south and horizontal edges carry the current row tag; the north edge carries
the next row tag. This lets a corner seed force a special initial row while all
later rows use the normal tag.
-/
def toTaggedWangTile (rowTag nextRowTag : Nat) (t : MachineHistoryTile) : WangTile where
  n := taggedTripleCellColor nextRowTag t.nextLeft t.nextCenter t.nextRight
  s := taggedTripleCellColor rowTag t.prevLeft t.prevCenter t.prevRight
  e := taggedOverlapCellColor rowTag t.prevCenter t.prevRight t.nextCenter t.nextRight
  w := taggedOverlapCellColor rowTag t.prevLeft t.prevCenter t.nextLeft t.nextCenter

theorem hMatches_toTaggedWangTile_iff_cells
    (rowTag nextRowTag rowTag' nextRowTag' : Nat)
    (left right : MachineHistoryTile) :
    WangTile.HMatches (left.toTaggedWangTile rowTag nextRowTag)
        (right.toTaggedWangTile rowTag' nextRowTag') ↔
      rowTag = rowTag' ∧
        left.prevCenter = right.prevLeft ∧
        left.prevRight = right.prevCenter ∧
        left.nextCenter = right.nextLeft ∧
        left.nextRight = right.nextCenter := by
  unfold WangTile.HMatches toTaggedWangTile
  rw [taggedOverlapCellColor_eq_iff]

theorem vMatches_toTaggedWangTile_iff_cells
    (rowTag nextRowTag rowTag' nextRowTag' : Nat)
    (lower upper : MachineHistoryTile) :
    WangTile.VMatches (lower.toTaggedWangTile rowTag nextRowTag)
        (upper.toTaggedWangTile rowTag' nextRowTag') ↔
      nextRowTag = rowTag' ∧
        lower.nextLeft = upper.prevLeft ∧
        lower.nextCenter = upper.prevCenter ∧
        lower.nextRight = upper.prevRight := by
  unfold WangTile.VMatches toTaggedWangTile
  rw [taggedTripleCellColor_eq_iff]

theorem toTaggedWangTile_injective
    {rowTag nextRowTag rowTag' nextRowTag' : Nat}
    {t u : MachineHistoryTile}
    (h : t.toTaggedWangTile rowTag nextRowTag =
      u.toTaggedWangTile rowTag' nextRowTag') :
    rowTag = rowTag' ∧ nextRowTag = nextRowTag' ∧ t = u := by
  have hs : taggedTripleCellColor rowTag t.prevLeft t.prevCenter t.prevRight =
      taggedTripleCellColor rowTag' u.prevLeft u.prevCenter u.prevRight := by
    simpa [toTaggedWangTile] using congrArg WangTile.s h
  have hn : taggedTripleCellColor nextRowTag t.nextLeft t.nextCenter t.nextRight =
      taggedTripleCellColor nextRowTag' u.nextLeft u.nextCenter u.nextRight := by
    simpa [toTaggedWangTile] using congrArg WangTile.n h
  rw [taggedTripleCellColor_eq_iff] at hs hn
  rcases hs with ⟨hrow, hprevLeft, hprevCenter, hprevRight⟩
  rcases hn with ⟨hnextRow, hnextLeft, hnextCenter, hnextRight⟩
  cases t
  cases u
  simp_all

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

theorem localNextCell?_of_mem_machineHistoryTiles {M : Machine} {t : MachineHistoryTile}
    (ht : t ∈ machineHistoryTiles M) :
    localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter := by
  exact (mem_machineHistoryTiles_iff M t).1 ht |>.2.2.2.2.2.2

theorem prevCenter_mem_of_mem_machineHistoryTiles {M : Machine} {t : MachineHistoryTile}
    (ht : t ∈ machineHistoryTiles M) :
    t.prevCenter.Mem M := by
  exact mem_of_mem_machineCells ((mem_machineHistoryTiles_iff M t).1 ht).2.1

theorem nextCenter_mem_of_mem_machineHistoryTiles {M : Machine} {t : MachineHistoryTile}
    (ht : t ∈ machineHistoryTiles M) :
    t.nextCenter.Mem M := by
  exact mem_of_mem_machineCells ((mem_machineHistoryTiles_iff M t).1 ht).2.2.2.2.1

theorem prevCenter_not_halt_of_mem_machineHistoryTiles {M : Machine}
    {t : MachineHistoryTile} {a : Nat}
    (ht : t ∈ machineHistoryTiles M) :
    t.prevCenter ≠ MachineCell.head M.halt a := by
  intro hcell
  have hmem := prevCenter_mem_of_mem_machineHistoryTiles ht
  rw [hcell] at hmem
  exact hmem.2.1 rfl

theorem nextCenter_not_halt_of_mem_machineHistoryTiles {M : Machine}
    {t : MachineHistoryTile} {a : Nat}
    (ht : t ∈ machineHistoryTiles M) :
    t.nextCenter ≠ MachineCell.head M.halt a := by
  intro hcell
  have hmem := nextCenter_mem_of_mem_machineHistoryTiles ht
  rw [hcell] at hmem
  exact hmem.2.1 rfl

theorem runHistoryTile_mem_machineHistoryTiles_of_not_halts {M : Machine}
    (h : ¬ M.HaltsEmpty) (time pos : Nat) :
    runHistoryTile M time pos ∈ machineHistoryTiles M := by
  rcases runHistoryTile_cells_mem_of_not_halts h time pos with
    ⟨hprevLeft, hprevCenter, hprevRight, hnextLeft, hnextCenter, hnextRight⟩
  exact mem_machineHistoryTiles_of_supported hprevLeft hprevCenter hprevRight
    hnextLeft hnextCenter hnextRight
    (runHistoryTile_local_of_not_halts h time pos)

/-- The untagged Wang tiles produced from the local-history construction. -/
def rawMachineTiles (M : Machine) : TileSet :=
  (machineHistoryTiles M).map MachineHistoryTile.toWangTile

theorem mem_rawMachineTiles_iff (M : Machine) (tile : WangTile) :
    tile ∈ rawMachineTiles M ↔
      ∃ t : MachineHistoryTile, t ∈ machineHistoryTiles M ∧ t.toWangTile = tile := by
  simp [rawMachineTiles]

theorem toWangTile_mem_rawMachineTiles {M : Machine} {t : MachineHistoryTile}
    (ht : t ∈ machineHistoryTiles M) :
    t.toWangTile ∈ rawMachineTiles M := by
  rw [mem_rawMachineTiles_iff]
  exact ⟨t, ht, rfl⟩

theorem toWangTile_mem_rawMachineTiles_iff (M : Machine) (t : MachineHistoryTile) :
    t.toWangTile ∈ rawMachineTiles M ↔ t ∈ machineHistoryTiles M := by
  constructor
  · intro ht
    rcases (mem_rawMachineTiles_iff M t.toWangTile).1 ht with ⟨u, hu, htile⟩
    exact MachineHistoryTile.toWangTile_injective htile
      ▸ hu
  · exact toWangTile_mem_rawMachineTiles

theorem toWangTile_mem_rawMachineTiles_of_supported {M : Machine} {t : MachineHistoryTile}
    (hprevLeft : t.prevLeft.Mem M) (hprevCenter : t.prevCenter.Mem M)
    (hprevRight : t.prevRight.Mem M) (hnextLeft : t.nextLeft.Mem M)
    (hnextCenter : t.nextCenter.Mem M) (hnextRight : t.nextRight.Mem M)
    (hlocal : localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter) :
    t.toWangTile ∈ rawMachineTiles M :=
  toWangTile_mem_rawMachineTiles
    (mem_machineHistoryTiles_of_supported hprevLeft hprevCenter hprevRight
      hnextLeft hnextCenter hnextRight hlocal)

def initialRowHistoryTiles (M : Machine) : List MachineHistoryTile :=
  [runHistoryTile M 0 0,
    runHistoryTile M 0 1,
    runHistoryTile M 0 2,
    runHistoryTile M 0 3]

def initialRowMachineTiles (M : Machine) : TileSet :=
  (initialRowHistoryTiles M).map
    (MachineHistoryTile.toTaggedWangTile initialRowTag normalRowTag)

def normalRowMachineTiles (M : Machine) : TileSet :=
  (machineHistoryTiles M).map
    (MachineHistoryTile.toTaggedWangTile normalRowTag normalRowTag)

def taggedMachineTiles (M : Machine) : TileSet :=
  initialRowMachineTiles M ++ normalRowMachineTiles M

/-- The public machine tileset, with row tags that force the bottom initial row. -/
def machineTiles (M : Machine) : TileSet :=
  taggedMachineTiles M

def IsInitialMachineTile (M : Machine) (tile : WangTile) : Prop :=
  ∃ t : MachineHistoryTile,
    t ∈ initialRowHistoryTiles M ∧
      t.toTaggedWangTile initialRowTag normalRowTag = tile

def IsNormalMachineTile (M : Machine) (tile : WangTile) : Prop :=
  ∃ t : MachineHistoryTile,
    t ∈ machineHistoryTiles M ∧
      t.toTaggedWangTile normalRowTag normalRowTag = tile

theorem mem_machineTiles_iff (M : Machine) (tile : WangTile) :
    tile ∈ machineTiles M ↔
      IsInitialMachineTile M tile ∨ IsNormalMachineTile M tile := by
  simp [IsInitialMachineTile, IsNormalMachineTile, machineTiles,
    taggedMachineTiles, initialRowMachineTiles, normalRowMachineTiles]

theorem initialTagged_ne_normalTagged {t u : MachineHistoryTile} :
    t.toTaggedWangTile initialRowTag normalRowTag ≠
      u.toTaggedWangTile normalRowTag normalRowTag := by
  intro h
  exact initialRowTag_ne_normalRowTag
    (MachineHistoryTile.toTaggedWangTile_injective h).1

theorem IsNormalMachineTile.of_hMatches_left {M : Machine}
    {left right : WangTile}
    (hleft : IsNormalMachineTile M left)
    (hmatch : WangTile.HMatches left right)
    (hright : right ∈ machineTiles M) :
    IsNormalMachineTile M right := by
  rcases hleft with ⟨leftHistory, _hleftMem, hleftTile⟩
  rcases (mem_machineTiles_iff M right).1 hright with hrightInitial | hrightNormal
  · rcases hrightInitial with ⟨rightHistory, _hrightMem, hrightTile⟩
    have hmatch' : WangTile.HMatches
        (leftHistory.toTaggedWangTile normalRowTag normalRowTag)
        (rightHistory.toTaggedWangTile initialRowTag normalRowTag) := by
      simpa [hleftTile, hrightTile] using hmatch
    have htag := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
      normalRowTag normalRowTag initialRowTag normalRowTag
      leftHistory rightHistory).1 hmatch'
    exact False.elim (initialRowTag_ne_normalRowTag htag.1.symm)
  · exact hrightNormal

theorem IsNormalMachineTile.of_vMatches_below {M : Machine}
    {lower upper : WangTile}
    (hlower : IsNormalMachineTile M lower)
    (hmatch : WangTile.VMatches lower upper)
    (hupper : upper ∈ machineTiles M) :
    IsNormalMachineTile M upper := by
  rcases hlower with ⟨lowerHistory, _hlowerMem, hlowerTile⟩
  rcases (mem_machineTiles_iff M upper).1 hupper with hupperInitial | hupperNormal
  · rcases hupperInitial with ⟨upperHistory, _hupperMem, hupperTile⟩
    have hmatch' : WangTile.VMatches
        (lowerHistory.toTaggedWangTile normalRowTag normalRowTag)
        (upperHistory.toTaggedWangTile initialRowTag normalRowTag) := by
      simpa [hlowerTile, hupperTile] using hmatch
    have htag := (MachineHistoryTile.vMatches_toTaggedWangTile_iff_cells
      normalRowTag normalRowTag initialRowTag normalRowTag
      lowerHistory upperHistory).1 hmatch'
    exact False.elim (initialRowTag_ne_normalRowTag htag.1.symm)
  · exact hupperNormal

theorem IsNormalMachineTile.of_vMatches_initial_below {M : Machine}
    {lower upper : WangTile}
    (hlower : IsInitialMachineTile M lower)
    (hmatch : WangTile.VMatches lower upper)
    (hupper : upper ∈ machineTiles M) :
    IsNormalMachineTile M upper := by
  rcases hlower with ⟨lowerHistory, _hlowerMem, hlowerTile⟩
  rcases (mem_machineTiles_iff M upper).1 hupper with hupperInitial | hupperNormal
  · rcases hupperInitial with ⟨upperHistory, _hupperMem, hupperTile⟩
    have hmatch' : WangTile.VMatches
        (lowerHistory.toTaggedWangTile initialRowTag normalRowTag)
        (upperHistory.toTaggedWangTile initialRowTag normalRowTag) := by
      simpa [hlowerTile, hupperTile] using hmatch
    have htag := (MachineHistoryTile.vMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag initialRowTag normalRowTag
      lowerHistory upperHistory).1 hmatch'
    exact False.elim (initialRowTag_ne_normalRowTag htag.1.symm)
  · exact hupperNormal

theorem initialRowHistoryTile_zero_mem (M : Machine) :
    runHistoryTile M 0 0 ∈ initialRowHistoryTiles M := by
  simp [initialRowHistoryTiles]

theorem initialRowHistoryTile_one_mem (M : Machine) :
    runHistoryTile M 0 1 ∈ initialRowHistoryTiles M := by
  simp [initialRowHistoryTiles]

theorem initialRowHistoryTile_two_mem (M : Machine) :
    runHistoryTile M 0 2 ∈ initialRowHistoryTiles M := by
  simp [initialRowHistoryTiles]

theorem initialRowHistoryTile_three_mem (M : Machine) :
    runHistoryTile M 0 3 ∈ initialRowHistoryTiles M := by
  simp [initialRowHistoryTiles]

theorem runHistoryTile_zero_eq_three_of_three_le (M : Machine) {pos : Nat}
    (hpos : 3 ≤ pos) :
    runHistoryTile M 0 pos = runHistoryTile M 0 3 := by
  cases pos with
  | zero => omega
  | succ pos =>
      cases pos with
      | zero => omega
      | succ pos =>
          cases pos with
          | zero => omega
          | succ pos =>
              by_cases hstart : M.start = M.halt
              · simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
                  Machine.runEmpty_zero, Machine.runEmpty_succ, Machine.nextID,
                  Machine.initialID, ID.cellAt, ID.cellAtLeft, hstart]
              · rcases hstep : M.step M.start M.blank with ⟨write, q', move⟩
                cases move <;>
                  simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
                    Machine.runEmpty_zero, Machine.runEmpty_succ, Machine.nextID,
                    Machine.initialID, ID.cellAt, ID.cellAtLeft, hstart, hstep,
                    Move.apply]

theorem runHistoryTile_zero_mem_initialRowHistoryTiles (M : Machine) (pos : Nat) :
    runHistoryTile M 0 pos ∈ initialRowHistoryTiles M := by
  cases pos with
  | zero =>
      exact initialRowHistoryTile_zero_mem M
  | succ pos =>
      cases pos with
      | zero =>
          exact initialRowHistoryTile_one_mem M
      | succ pos =>
          cases pos with
          | zero =>
              exact initialRowHistoryTile_two_mem M
          | succ pos =>
              rw [runHistoryTile_zero_eq_three_of_three_le M (by omega : 3 ≤ pos + 1 + 1 + 1)]
              exact initialRowHistoryTile_three_mem M

theorem toTaggedWangTile_mem_initialRowMachineTiles {M : Machine}
    {t : MachineHistoryTile} (ht : t ∈ initialRowHistoryTiles M) :
    t.toTaggedWangTile initialRowTag normalRowTag ∈ initialRowMachineTiles M := by
  rw [initialRowMachineTiles, List.mem_map]
  exact ⟨t, ht, rfl⟩

theorem toTaggedWangTile_mem_normalRowMachineTiles {M : Machine}
    {t : MachineHistoryTile} (ht : t ∈ machineHistoryTiles M) :
    t.toTaggedWangTile normalRowTag normalRowTag ∈ normalRowMachineTiles M := by
  rw [normalRowMachineTiles, List.mem_map]
  exact ⟨t, ht, rfl⟩

theorem toTaggedWangTile_mem_taggedMachineTiles_initial {M : Machine}
    {t : MachineHistoryTile} (ht : t ∈ initialRowHistoryTiles M) :
    t.toTaggedWangTile initialRowTag normalRowTag ∈ taggedMachineTiles M := by
  simp [taggedMachineTiles, toTaggedWangTile_mem_initialRowMachineTiles ht]

theorem toTaggedWangTile_mem_taggedMachineTiles_normal {M : Machine}
    {t : MachineHistoryTile} (ht : t ∈ machineHistoryTiles M) :
    t.toTaggedWangTile normalRowTag normalRowTag ∈ taggedMachineTiles M := by
  simp [taggedMachineTiles, toTaggedWangTile_mem_normalRowMachineTiles ht]

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
def rawMachineSeed (M : Machine) : WangTile :=
  (runHistoryTile M 0 0).toWangTile

def taggedMachineSeed (M : Machine) : WangTile :=
  (runHistoryTile M 0 0).toTaggedWangTile initialRowTag normalRowTag

/-- The public machine seed, using the initial-row tag. -/
def machineSeed (M : Machine) : WangTile :=
  taggedMachineSeed M

def machineRowTag : Nat → Nat
  | 0 => initialRowTag
  | _ + 1 => normalRowTag

@[simp]
theorem machineRowTag_zero :
    machineRowTag 0 = initialRowTag :=
  rfl

@[simp]
theorem machineRowTag_succ (time : Nat) :
    machineRowTag (time + 1) = normalRowTag :=
  rfl

def runTaggedHistoryTile (M : Machine) (time pos : Nat) : WangTile :=
  (runHistoryTile M time pos).toTaggedWangTile (machineRowTag time) normalRowTag

theorem runTaggedHistoryTile_mem_taggedMachineTiles_of_not_halts {M : Machine}
    (h : ¬ M.HaltsEmpty) (time pos : Nat) :
    runTaggedHistoryTile M time pos ∈ taggedMachineTiles M := by
  cases time with
  | zero =>
      exact toTaggedWangTile_mem_taggedMachineTiles_initial
        (runHistoryTile_zero_mem_initialRowHistoryTiles M pos)
  | succ time =>
      exact toTaggedWangTile_mem_taggedMachineTiles_normal
        (runHistoryTile_mem_machineHistoryTiles_of_not_halts h (time + 1) pos)

theorem runTaggedHistoryTile_hMatches (M : Machine) (time pos : Nat) :
    WangTile.HMatches (runTaggedHistoryTile M time pos)
      (runTaggedHistoryTile M time (pos + 1)) := by
  have hcells := (MachineHistoryTile.hMatches_toWangTile_iff_cells
    (runHistoryTile M time pos) (runHistoryTile M time (pos + 1))).1
    (runHistoryTile_hMatches M time pos)
  simp only [runTaggedHistoryTile]
  rw [MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells]
  exact ⟨rfl, hcells⟩

theorem runTaggedHistoryTile_vMatches (M : Machine) (time pos : Nat) :
    WangTile.VMatches (runTaggedHistoryTile M time pos)
      (runTaggedHistoryTile M (time + 1) pos) := by
  have hcells := (MachineHistoryTile.vMatches_toWangTile_iff_cells
    (runHistoryTile M time pos) (runHistoryTile M (time + 1) pos)).1
    (runHistoryTile_vMatches M time pos)
  simp only [runTaggedHistoryTile]
  rw [MachineHistoryTile.vMatches_toTaggedWangTile_iff_cells]
  exact ⟨rfl, hcells⟩

@[simp]
theorem rawMachineSeed_eq (M : Machine) :
    rawMachineSeed M = (runHistoryTile M 0 0).toWangTile :=
  rfl

@[simp]
theorem machineSeed_eq (M : Machine) :
    machineSeed M =
      (runHistoryTile M 0 0).toTaggedWangTile initialRowTag normalRowTag :=
  rfl

theorem initialTaggedWangTile_eq_machineSeed_iff {M : Machine}
    {t : MachineHistoryTile} :
    t.toTaggedWangTile initialRowTag normalRowTag = machineSeed M ↔
      t = runHistoryTile M 0 0 := by
  constructor
  · intro h
    exact (MachineHistoryTile.toTaggedWangTile_injective h).2.2
  · intro h
    rw [h, machineSeed_eq]

theorem normalTaggedWangTile_ne_machineSeed {M : Machine}
    {t : MachineHistoryTile} :
    t.toTaggedWangTile normalRowTag normalRowTag ≠ machineSeed M := by
  intro h
  exact initialTagged_ne_normalTagged (t := runHistoryTile M 0 0) (u := t) h.symm

theorem IsInitialMachineTile_machineSeed (M : Machine) :
    IsInitialMachineTile M (machineSeed M) := by
  exact ⟨runHistoryTile M 0 0, runHistoryTile_zero_mem_initialRowHistoryTiles M 0,
    by simp [machineSeed_eq]⟩

theorem IsNormalMachineTile.row_one_of_seeded_tiling {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) :
    ∀ pos : Nat, IsNormalMachineTile M (x (pos, 1)).1 := by
  intro pos
  induction pos with
  | zero =>
      exact IsNormalMachineTile.of_vMatches_initial_below
        (by simpa [hseed] using IsInitialMachineTile_machineSeed M)
        (hvalid.2 (0, 0))
        (x (0, 1)).2
  | succ pos ih =>
      exact IsNormalMachineTile.of_hMatches_left ih
        (hvalid.1 (pos, 1))
        (x (pos + 1, 1)).2

theorem IsNormalMachineTile.positive_row_of_seeded_tiling {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) :
    ∀ time pos : Nat, IsNormalMachineTile M (x (pos, time + 1)).1 := by
  intro time
  induction time with
  | zero =>
      exact IsNormalMachineTile.row_one_of_seeded_tiling hvalid hseed
  | succ time ih =>
      intro pos
      induction pos with
      | zero =>
          exact IsNormalMachineTile.of_vMatches_below
            (ih 0)
            (hvalid.2 (0, time + 1))
            (x (0, time + 1 + 1)).2
      | succ pos ihpos =>
          exact IsNormalMachineTile.of_hMatches_left ihpos
            (hvalid.1 (pos, time + 1 + 1))
            (x (pos + 1, time + 1 + 1)).2

theorem seeded_tiling_row_zero_one_eq {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) :
    (x (1, 0)).1 = runTaggedHistoryTile M 0 1 := by
  have hh : WangTile.HMatches (machineSeed M) (x (1, 0)).1 := by
    simpa [hseed] using hvalid.1 (0, 0)
  rcases (mem_machineTiles_iff M (x (1, 0)).1).1 (x (1, 0)).2 with hinit | hnormal
  · rcases hinit with ⟨t, ht, htile⟩
    have hh' : WangTile.HMatches
        ((runHistoryTile M 0 0).toTaggedWangTile initialRowTag normalRowTag)
        (t.toTaggedWangTile initialRowTag normalRowTag) := by
      simpa [machineSeed_eq, htile] using hh
    have hcells := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag initialRowTag normalRowTag
      (runHistoryTile M 0 0) t).1 hh'
    have htCases :
        t = runHistoryTile M 0 0 ∨
          t = runHistoryTile M 0 1 ∨
          t = runHistoryTile M 0 2 ∨
          t = runHistoryTile M 0 3 := by
      simpa [initialRowHistoryTiles] using ht
    rcases htCases with ht | ht | ht | ht
    · subst t
      have hbad := hcells.2.1
      simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
        Machine.runEmpty_zero, Machine.initialID, ID.cellAt, ID.cellAtLeft] at hbad
    · subst t
      rw [← htile]
      rfl
    · subst t
      have hbad := hcells.2.1
      simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
        Machine.runEmpty_zero, Machine.initialID, ID.cellAt, ID.cellAtLeft] at hbad
    · subst t
      have hbad := hcells.2.1
      simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
        Machine.runEmpty_zero, Machine.initialID, ID.cellAt, ID.cellAtLeft] at hbad
  · rcases hnormal with ⟨t, _ht, htile⟩
    have hh' : WangTile.HMatches
        ((runHistoryTile M 0 0).toTaggedWangTile initialRowTag normalRowTag)
        (t.toTaggedWangTile normalRowTag normalRowTag) := by
      simpa [machineSeed_eq, htile] using hh
    have htag := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag normalRowTag normalRowTag
      (runHistoryTile M 0 0) t).1 hh'
    exact False.elim (initialRowTag_ne_normalRowTag htag.1)

theorem seeded_tiling_row_zero_two_eq {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) :
    (x (2, 0)).1 = runTaggedHistoryTile M 0 2 := by
  have hleft := seeded_tiling_row_zero_one_eq (M := M) (x := x) hvalid hseed
  have hh : WangTile.HMatches (runTaggedHistoryTile M 0 1) (x (2, 0)).1 := by
    simpa [hleft] using hvalid.1 (1, 0)
  rcases (mem_machineTiles_iff M (x (2, 0)).1).1 (x (2, 0)).2 with hinit | hnormal
  · rcases hinit with ⟨t, ht, htile⟩
    have hh' : WangTile.HMatches
        ((runHistoryTile M 0 1).toTaggedWangTile initialRowTag normalRowTag)
        (t.toTaggedWangTile initialRowTag normalRowTag) := by
      simpa [runTaggedHistoryTile, htile] using hh
    have hcells := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag initialRowTag normalRowTag
      (runHistoryTile M 0 1) t).1 hh'
    have htCases :
        t = runHistoryTile M 0 0 ∨
          t = runHistoryTile M 0 1 ∨
          t = runHistoryTile M 0 2 ∨
          t = runHistoryTile M 0 3 := by
      simpa [initialRowHistoryTiles] using ht
    rcases htCases with ht | ht | ht | ht
    · subst t
      have hbad := hcells.2.1
      simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
        Machine.runEmpty_zero, Machine.initialID, ID.cellAt, ID.cellAtLeft] at hbad
    · subst t
      have hbad := hcells.2.1
      simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
        Machine.runEmpty_zero, Machine.initialID, ID.cellAt, ID.cellAtLeft] at hbad
    · subst t
      rw [← htile]
      rfl
    · subst t
      rw [← htile]
      simp [runTaggedHistoryTile]
      by_cases hstart : M.start = M.halt
      · simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
          Machine.runEmpty_zero, Machine.runEmpty_succ, Machine.nextID,
          Machine.initialID, ID.cellAt, ID.cellAtLeft, hstart]
      · rcases hstep : M.step M.start M.blank with ⟨write, q', move⟩
        cases move <;>
          simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
            Machine.runEmpty_zero, Machine.runEmpty_succ, Machine.nextID,
            Machine.initialID, ID.cellAt, ID.cellAtLeft, hstart, hstep,
            Move.apply] at hcells ⊢
  · rcases hnormal with ⟨t, _ht, htile⟩
    have hh' : WangTile.HMatches
        ((runHistoryTile M 0 1).toTaggedWangTile initialRowTag normalRowTag)
        (t.toTaggedWangTile normalRowTag normalRowTag) := by
      simpa [runTaggedHistoryTile, htile] using hh
    have htag := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag normalRowTag normalRowTag
      (runHistoryTile M 0 1) t).1 hh'
    exact False.elim (initialRowTag_ne_normalRowTag htag.1)

theorem seeded_tiling_row_zero_three_eq {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) :
    (x (3, 0)).1 = runTaggedHistoryTile M 0 3 := by
  have hleft := seeded_tiling_row_zero_two_eq (M := M) (x := x) hvalid hseed
  have hh : WangTile.HMatches (runTaggedHistoryTile M 0 2) (x (3, 0)).1 := by
    simpa [hleft] using hvalid.1 (2, 0)
  rcases (mem_machineTiles_iff M (x (3, 0)).1).1 (x (3, 0)).2 with hinit | hnormal
  · rcases hinit with ⟨t, ht, htile⟩
    have hh' : WangTile.HMatches
        ((runHistoryTile M 0 2).toTaggedWangTile initialRowTag normalRowTag)
        (t.toTaggedWangTile initialRowTag normalRowTag) := by
      simpa [runTaggedHistoryTile, htile] using hh
    have hcells := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag initialRowTag normalRowTag
      (runHistoryTile M 0 2) t).1 hh'
    have htCases :
        t = runHistoryTile M 0 0 ∨
          t = runHistoryTile M 0 1 ∨
          t = runHistoryTile M 0 2 ∨
          t = runHistoryTile M 0 3 := by
      simpa [initialRowHistoryTiles] using ht
    rcases htCases with ht | ht | ht | ht
    · subst t
      have hbad := hcells.2.1
      simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
        Machine.runEmpty_zero, Machine.initialID, ID.cellAt, ID.cellAtLeft] at hbad
    · subst t
      have hbad := hcells.2.1
      simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
        Machine.runEmpty_zero, Machine.initialID, ID.cellAt, ID.cellAtLeft] at hbad
    · subst t
      rw [← htile]
      simp [runTaggedHistoryTile]
      by_cases hstart : M.start = M.halt
      · simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
          Machine.runEmpty_zero, Machine.runEmpty_succ, Machine.nextID,
          Machine.initialID, ID.cellAt, ID.cellAtLeft, hstart]
      · rcases hstep : M.step M.start M.blank with ⟨write, q', move⟩
        cases move <;>
          simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
            Machine.runEmpty_zero, Machine.runEmpty_succ, Machine.nextID,
            Machine.initialID, ID.cellAt, ID.cellAtLeft, hstart, hstep,
            Move.apply] at hcells ⊢
    · subst t
      rw [← htile]
      rfl
  · rcases hnormal with ⟨t, _ht, htile⟩
    have hh' : WangTile.HMatches
        ((runHistoryTile M 0 2).toTaggedWangTile initialRowTag normalRowTag)
        (t.toTaggedWangTile normalRowTag normalRowTag) := by
      simpa [runTaggedHistoryTile, htile] using hh
    have htag := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag normalRowTag normalRowTag
      (runHistoryTile M 0 2) t).1 hh'
    exact False.elim (initialRowTag_ne_normalRowTag htag.1)

theorem seeded_tiling_row_zero_eq_of_le_three {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) :
    ∀ {pos : Nat}, pos ≤ 3 → (x (pos, 0)).1 = runTaggedHistoryTile M 0 pos := by
  intro pos hpos
  cases pos with
  | zero =>
      simpa [runTaggedHistoryTile, machineSeed_eq] using hseed
  | succ pos =>
      cases pos with
      | zero =>
          exact seeded_tiling_row_zero_one_eq hvalid hseed
      | succ pos =>
          cases pos with
          | zero =>
              exact seeded_tiling_row_zero_two_eq hvalid hseed
          | succ pos =>
              cases pos with
              | zero =>
                  exact seeded_tiling_row_zero_three_eq hvalid hseed
              | succ pos =>
                  omega

theorem not_tilesQuarterWithSeed_machineTiles_of_seed_nextCenter_halt {M : Machine}
    {a : Nat} (hnext : (runHistoryTile M 0 0).nextCenter = MachineCell.head M.halt a) :
    ¬ TilesQuarterWithSeed (machineTiles M) (machineSeed M) := by
  rintro ⟨x, hvalid, hseed⟩
  have hv : WangTile.VMatches (machineSeed M) (x (0, 1)).1 := by
    simpa [hseed] using hvalid.2 (0, 0)
  rcases (mem_machineTiles_iff M (x (0, 1)).1).1 (x (0, 1)).2 with hinit | hnormal
  · rcases hinit with ⟨t, _ht, htilet⟩
    have hv' : WangTile.VMatches (machineSeed M)
        (t.toTaggedWangTile initialRowTag normalRowTag) := by
      simpa [htilet] using hv
    have htag := (MachineHistoryTile.vMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag initialRowTag normalRowTag
      (runHistoryTile M 0 0) t).1 (by
        simpa [machineSeed_eq] using hv')
    exact initialRowTag_ne_normalRowTag htag.1.symm
  · rcases hnormal with ⟨t, ht, htilet⟩
    have hv' : WangTile.VMatches (machineSeed M)
        (t.toTaggedWangTile normalRowTag normalRowTag) := by
      simpa [htilet] using hv
    have hcells := (MachineHistoryTile.vMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag normalRowTag normalRowTag
      (runHistoryTile M 0 0) t).1 (by
        simpa [machineSeed_eq] using hv')
    exact prevCenter_not_halt_of_mem_machineHistoryTiles (M := M)
      (t := t) (a := a) ht (by
        rw [← hcells.2.2.1, hnext])

theorem not_tilesQuarterWithSeed_machineTiles_of_seed_nextRight_halt {M : Machine}
    {a : Nat} (hnext : (runHistoryTile M 0 0).nextRight = MachineCell.head M.halt a) :
    ¬ TilesQuarterWithSeed (machineTiles M) (machineSeed M) := by
  rintro ⟨x, hvalid, hseed⟩
  have hv : WangTile.VMatches (machineSeed M) (x (0, 1)).1 := by
    simpa [hseed] using hvalid.2 (0, 0)
  rcases (mem_machineTiles_iff M (x (0, 1)).1).1 (x (0, 1)).2 with hinit | hnormal
  · rcases hinit with ⟨t, _ht, htilet⟩
    have hv' : WangTile.VMatches (machineSeed M)
        (t.toTaggedWangTile initialRowTag normalRowTag) := by
      simpa [htilet] using hv
    have htag := (MachineHistoryTile.vMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag initialRowTag normalRowTag
      (runHistoryTile M 0 0) t).1 (by
        simpa [machineSeed_eq] using hv')
    exact initialRowTag_ne_normalRowTag htag.1.symm
  · rcases hnormal with ⟨t0, ht0, ht0tile⟩
    have hv0' : WangTile.VMatches (machineSeed M)
        (t0.toTaggedWangTile normalRowTag normalRowTag) := by
      simpa [ht0tile] using hv
    have hv0cells := (MachineHistoryTile.vMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag normalRowTag normalRowTag
      (runHistoryTile M 0 0) t0).1 (by
        simpa [machineSeed_eq] using hv0')
    have hh : WangTile.HMatches (x (0, 1)).1 (x (1, 1)).1 := by
      simpa using hvalid.1 (0, 1)
    rcases (mem_machineTiles_iff M (x (1, 1)).1).1 (x (1, 1)).2 with hinit1 | hnormal1
    · rcases hinit1 with ⟨t1, _ht1, ht1tile⟩
      have hh' : WangTile.HMatches
          (t0.toTaggedWangTile normalRowTag normalRowTag)
          (t1.toTaggedWangTile initialRowTag normalRowTag) := by
        simpa [ht0tile, ht1tile] using hh
      have htag := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
        normalRowTag normalRowTag initialRowTag normalRowTag t0 t1).1 hh'
      exact initialRowTag_ne_normalRowTag htag.1.symm
    · rcases hnormal1 with ⟨t1, ht1, ht1tile⟩
      have hh' : WangTile.HMatches
          (t0.toTaggedWangTile normalRowTag normalRowTag)
          (t1.toTaggedWangTile normalRowTag normalRowTag) := by
        simpa [ht0tile, ht1tile] using hh
      have hhcells := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
        normalRowTag normalRowTag normalRowTag normalRowTag t0 t1).1 hh'
      exact prevCenter_not_halt_of_mem_machineHistoryTiles (M := M)
        (t := t1) (a := a) ht1 (by
          rw [← hhcells.2.2.1, ← hv0cells.2.2.2, hnext])

theorem not_tilesQuarterWithSeed_machineTiles_of_initial_halt {M : Machine}
    (hstart : M.start = M.halt) :
    ¬ TilesQuarterWithSeed (machineTiles M) (machineSeed M) := by
  exact not_tilesQuarterWithSeed_machineTiles_of_seed_nextCenter_halt
    (M := M) (a := M.blank) (by
      simp [runHistoryTile, Machine.runCell, Machine.runEmpty_succ,
        Machine.runEmpty_zero, Machine.nextID, Machine.initialID, ID.cellAt,
        hstart])

theorem not_tilesQuarterWithSeed_machineTiles_of_first_step_left_halt {M : Machine}
    {write : Nat} (hstart : M.start ≠ M.halt)
    (hstep : M.step M.start M.blank = (write, M.halt, Move.left)) :
    ¬ TilesQuarterWithSeed (machineTiles M) (machineSeed M) := by
  exact not_tilesQuarterWithSeed_machineTiles_of_seed_nextCenter_halt
    (M := M) (a := write) (by
      simp [runHistoryTile, Machine.runCell, Machine.runEmpty_succ,
        Machine.runEmpty_zero, Machine.nextID, Machine.initialID, ID.cellAt,
        hstart, hstep, Move.apply])

theorem not_tilesQuarterWithSeed_machineTiles_of_first_step_right_halt {M : Machine}
    {write : Nat} (hstart : M.start ≠ M.halt)
    (hstep : M.step M.start M.blank = (write, M.halt, Move.right)) :
    ¬ TilesQuarterWithSeed (machineTiles M) (machineSeed M) := by
  exact not_tilesQuarterWithSeed_machineTiles_of_seed_nextRight_halt
    (M := M) (a := M.blank) (by
      simp [runHistoryTile, Machine.runCell, Machine.runEmpty_succ,
        Machine.runEmpty_zero, Machine.nextID, Machine.initialID, ID.cellAt,
        hstart, hstep, Move.apply])

theorem not_tilesQuarterWithSeed_machineTiles_of_halts_at_one {M : Machine}
    (hhalt : (M.runEmpty 1).state = M.halt) :
    ¬ TilesQuarterWithSeed (machineTiles M) (machineSeed M) := by
  by_cases hstart : M.start = M.halt
  · exact not_tilesQuarterWithSeed_machineTiles_of_initial_halt hstart
  · rcases hstep : M.step M.start M.blank with ⟨write, q', move⟩
    have hq' : q' = M.halt := by
      simpa [Machine.runEmpty_succ, Machine.runEmpty_zero, Machine.nextID,
        Machine.initialID, hstart, hstep] using hhalt
    cases move with
    | left =>
        exact not_tilesQuarterWithSeed_machineTiles_of_first_step_left_halt
          hstart (by simpa [hq'] using hstep)
    | right =>
        exact not_tilesQuarterWithSeed_machineTiles_of_first_step_right_halt
          hstart (by simpa [hq'] using hstep)

theorem tilesQuarterWithSeed_rawMachineTiles_of_not_halts {M : Machine}
    (h : ¬ M.HaltsEmpty) :
    TilesQuarterWithSeed (rawMachineTiles M) (rawMachineSeed M) := by
  let x : Nat × Nat → TileIn (rawMachineTiles M) := fun p =>
    ⟨(runHistoryTile M p.2 p.1).toWangTile,
      toWangTile_mem_rawMachineTiles
        (runHistoryTile_mem_machineHistoryTiles_of_not_halts h p.2 p.1)⟩
  refine ⟨x, ?_, ?_⟩
  · constructor
    · intro p
      exact runHistoryTile_hMatches M p.2 p.1
    · intro p
      exact runHistoryTile_vMatches M p.2 p.1
  · simp [x, rawMachineSeed_eq]

theorem tilesQuarterWithSeed_taggedMachineTiles_of_not_halts {M : Machine}
    (h : ¬ M.HaltsEmpty) :
    TilesQuarterWithSeed (taggedMachineTiles M) (taggedMachineSeed M) := by
  let x : Nat × Nat → TileIn (taggedMachineTiles M) := fun p =>
    ⟨runTaggedHistoryTile M p.2 p.1,
      runTaggedHistoryTile_mem_taggedMachineTiles_of_not_halts h p.2 p.1⟩
  refine ⟨x, ?_, ?_⟩
  · constructor
    · intro p
      exact runTaggedHistoryTile_hMatches M p.2 p.1
    · intro p
      exact runTaggedHistoryTile_vMatches M p.2 p.1
  · simp [x, runTaggedHistoryTile, taggedMachineSeed]

theorem tilesQuarterWithSeed_machineTiles_of_not_halts {M : Machine}
    (h : ¬ M.HaltsEmpty) :
    TilesQuarterWithSeed (machineTiles M) (machineSeed M) := by
  simpa [machineTiles, machineSeed] using
    tilesQuarterWithSeed_taggedMachineTiles_of_not_halts h

end LeanWang
