/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Machine
import Mathlib.Data.Nat.Pairing

/-!
Finite local-history data for the machine space-time construction.

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

abbrev CodeType : Type :=
  Unit ⊕ Nat ⊕ Nat × Nat

def toSum : MachineCell → CodeType
  | boundary => Sum.inl ⟨⟩
  | plain a => Sum.inr (Sum.inl a)
  | head q a => Sum.inr (Sum.inr (q, a))

def ofSum : CodeType → MachineCell
  | Sum.inl _ => boundary
  | Sum.inr (Sum.inl a) => plain a
  | Sum.inr (Sum.inr (q, a)) => head q a

def equivSum : MachineCell ≃ CodeType where
  toFun := toSum
  invFun := ofSum
  left_inv := by
    intro c
    cases c <;> rfl
  right_inv := by
    intro p
    rcases p with _ | a | ⟨q, a⟩ <;> rfl

def symbol : MachineCell → Nat
  | boundary => 0
  | plain a => a
  | head _ a => a

/-- A machine cell is supported by a machine's finite symbol and state sets. -/
def Mem (M : Machine) : MachineCell → Prop
  | boundary => True
  | plain a => a ∈ M.symbols
  | head q a => q ∈ M.states ∧ q ≠ M.halt ∧ a ∈ M.symbols

end MachineCell

instance instPrimcodableMachineCell : Primcodable MachineCell :=
  Primcodable.ofEquiv MachineCell.CodeType MachineCell.equivSum

namespace MachineCell

/-- Use the canonical primitive-recursive encoding for machine-cell colors. -/
def code : MachineCell → Nat := Encodable.encode

theorem code_injective : Function.Injective code :=
  Encodable.encode_injective

theorem toSum_primrec : Primrec MachineCell.toSum := by
  simpa [MachineCell.equivSum] using
    (Primrec.of_equiv (e := MachineCell.equivSum) : Primrec MachineCell.equivSum)

theorem ofSum_primrec : Primrec MachineCell.ofSum := by
  simpa [MachineCell.equivSum] using
    (Primrec.of_equiv_symm (e := MachineCell.equivSum) : Primrec MachineCell.equivSum.symm)

theorem plain_primrec : Primrec MachineCell.plain := by
  have h :
      Primrec (fun a : Nat =>
        MachineCell.ofSum (Sum.inr (Sum.inl a) : MachineCell.CodeType)) :=
    ofSum_primrec.comp (Primrec.sumInr.comp (Primrec.sumInl.comp Primrec.id))
  exact h.of_eq fun _ => rfl

theorem head_primrec : Primrec (fun p : Nat × Nat => MachineCell.head p.1 p.2) := by
  have h :
      Primrec (fun p : Nat × Nat =>
        MachineCell.ofSum (Sum.inr (Sum.inr p) : MachineCell.CodeType)) :=
    ofSum_primrec.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.id))
  exact h.of_eq fun _ => rfl

theorem code_primrec : Primrec MachineCell.code :=
  Primrec.encode

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

theorem cellAt_ne_boundary (c : ID) (i : Nat) :
    c.cellAt i ≠ MachineCell.boundary := by
  by_cases hi : i = c.head
  · simp [cellAt, hi]
  · simp [cellAt, hi]

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

theorem pairCellColor_primrec :
    Primrec (fun p : MachineCell × MachineCell => pairCellColor p.1 p.2) :=
  Primrec₂.natPair.comp (MachineCell.code_primrec.comp Primrec.fst)
    (MachineCell.code_primrec.comp Primrec.snd)

theorem tripleCellColor_primrec :
    Primrec (fun p : MachineCell × MachineCell × MachineCell =>
      tripleCellColor p.1 p.2.1 p.2.2) := by
  unfold tripleCellColor
  exact Primrec₂.natPair.comp (MachineCell.code_primrec.comp Primrec.fst)
    (Primrec₂.natPair.comp
      (MachineCell.code_primrec.comp (Primrec.fst.comp Primrec.snd))
      (MachineCell.code_primrec.comp (Primrec.snd.comp Primrec.snd)))

theorem overlapCellColor_primrec :
    Primrec (fun p : MachineCell × MachineCell × MachineCell × MachineCell =>
      overlapCellColor p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold overlapCellColor
  exact Primrec₂.natPair.comp
    (pairCellColor_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
    (pairCellColor_primrec.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

theorem taggedTripleCellColor_primrec :
    Primrec (fun p : Nat × MachineCell × MachineCell × MachineCell =>
      taggedTripleCellColor p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold taggedTripleCellColor
  exact Primrec₂.natPair.comp Primrec.fst
    (tripleCellColor_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem taggedOverlapCellColor_primrec :
    Primrec (fun p : Nat × MachineCell × MachineCell × MachineCell × MachineCell =>
      taggedOverlapCellColor p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold taggedOverlapCellColor
  exact Primrec₂.natPair.comp Primrec.fst
    (overlapCellColor_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))))

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
        | _, Move.stay =>
            if q' = M.halt then none else some (MachineCell.head q' write)
        | _, _ => some (MachineCell.plain write)
  | MachineCell.head q a, MachineCell.plain b, _ =>
      if _h : q = M.halt then
        none
      else
        let (_write, q', move) := M.step q a
        match move with
        | Move.right => if q' = M.halt then none else some (MachineCell.head q' b)
        | Move.left | Move.stay => some (MachineCell.plain b)
  | _, MachineCell.plain b, MachineCell.head q a =>
      if _h : q = M.halt then
        none
      else
        let (_write, q', move) := M.step q a
        match move with
        | Move.left => if q' = M.halt then none else some (MachineCell.head q' b)
        | Move.right | Move.stay => some (MachineCell.plain b)
  | MachineCell.boundary, MachineCell.plain b, _ =>
      some (MachineCell.plain b)
  | _, MachineCell.plain b, _ =>
      some (MachineCell.plain b)

namespace Machine

theorem localNextCell?_cellAt_or_halt {M : Machine} {c : ID} {pos : Nat}
    (hstate : c.state ≠ M.halt) :
    localNextCell? M (c.cellAtLeft pos) (c.cellAt pos) (c.cellAt (pos + 1)) =
      if (M.nextID c).state = M.halt ∧ pos = (M.nextID c).head then
        none
      else
        some ((M.nextID c).cellAt pos) := by
  rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
  by_cases hcenter : pos = c.head
  · subst pos
    cases hhead : c.head with
    | zero =>
        cases move <;>
          simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID, localNextCell?,
            Move.apply]
    | succ pred =>
        cases move <;>
          simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID, localNextCell?,
            Move.apply]
  · by_cases hleft : c.head = pos + 1
    · cases hpos : pos with
      | zero =>
          cases move <;>
            simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID, localNextCell?,
              Move.apply]
      | succ pred =>
          have hpred : pred ≠ pred + 1 + 1 := by omega
          cases move <;>
            simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID, localNextCell?,
              Move.apply]
    · by_cases hright : pos = c.head + 1
      · subst pos
        cases hhead : c.head with
        | zero =>
            cases move <;>
              simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID, localNextCell?,
                Move.apply]
        | succ pred =>
            have hpred : pred + 1 + 1 ≠ pred := by omega
            cases move <;>
              simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID, localNextCell?,
                Move.apply]
      · cases hpos : pos with
        | zero =>
            cases hhead : c.head with
            | zero => omega
            | succ pred =>
                cases move <;>
                  (simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID,
                    localNextCell?, Move.apply]
                   try omega)
        | succ posPred =>
            cases hhead : c.head with
            | zero =>
                cases move <;>
                  simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID,
                    localNextCell?, Move.apply]
            | succ headPred =>
                have hleftCell : posPred ≠ headPred + 1 := by omega
                have hcenterCell : posPred ≠ headPred := by omega
                have hrightCell : posPred + 1 + 1 ≠ headPred + 1 := by omega
                have hnewLeft : posPred + 1 ≠ headPred := by omega
                have hnewRight : posPred + 1 ≠ headPred + 1 + 1 := by omega
                cases move <;>
                  simp_all [ID.cellAt, ID.cellAtLeft, Machine.nextID,
                    localNextCell?, Move.apply]

theorem localNextCell?_cellAt {M : Machine} {c : ID} {pos : Nat}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).2.1 ≠ M.halt) :
    localNextCell? M (c.cellAtLeft pos) (c.cellAt pos) (c.cellAt (pos + 1)) =
      some ((M.nextID c).cellAt pos) := by
  rw [localNextCell?_cellAt_or_halt hstate]
  simp [Machine.nextID, hstate, hnextState]

theorem localNextCell?_at_next_halt_head {M : Machine} {c : ID}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).2.1 = M.halt) :
    localNextCell? M
        (c.cellAtLeft ((M.step c.state (c.tape c.head)).2.2.apply c.head))
        (c.cellAt ((M.step c.state (c.tape c.head)).2.2.apply c.head))
        (c.cellAt ((M.step c.state (c.tape c.head)).2.2.apply c.head + 1)) =
      none := by
  rw [localNextCell?_cellAt_or_halt hstate]
  simp [Machine.nextID, hstate, hnextState]

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

def toTuple (t : MachineHistoryTile) :
    MachineCell × MachineCell × MachineCell × MachineCell × MachineCell × MachineCell :=
  (t.prevLeft, t.prevCenter, t.prevRight, t.nextLeft, t.nextCenter, t.nextRight)

def ofTuple
    (p : MachineCell × MachineCell × MachineCell × MachineCell × MachineCell × MachineCell) :
    MachineHistoryTile where
  prevLeft := p.1
  prevCenter := p.2.1
  prevRight := p.2.2.1
  nextLeft := p.2.2.2.1
  nextCenter := p.2.2.2.2.1
  nextRight := p.2.2.2.2.2

def equivTuple :
    MachineHistoryTile ≃
      MachineCell × MachineCell × MachineCell × MachineCell × MachineCell × MachineCell where
  toFun := toTuple
  invFun := ofTuple
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro p
    rcases p with ⟨prevLeft, prevCenter, prevRight, nextLeft, nextCenter, nextRight⟩
    rfl

instance instPrimcodableMachineHistoryTile : Primcodable MachineHistoryTile :=
  Primcodable.ofEquiv
    (MachineCell × MachineCell × MachineCell × MachineCell × MachineCell × MachineCell)
    MachineHistoryTile.equivTuple

theorem toTuple_primrec : Primrec MachineHistoryTile.toTuple := by
  simpa [MachineHistoryTile.equivTuple] using
    (Primrec.of_equiv (e := MachineHistoryTile.equivTuple) :
      Primrec MachineHistoryTile.equivTuple)

theorem ofTuple_primrec : Primrec MachineHistoryTile.ofTuple := by
  simpa [MachineHistoryTile.equivTuple] using
    (Primrec.of_equiv_symm (e := MachineHistoryTile.equivTuple) :
      Primrec MachineHistoryTile.equivTuple.symm)

theorem prevLeft_primrec : Primrec MachineHistoryTile.prevLeft :=
  Primrec.fst.comp toTuple_primrec

theorem prevCenter_primrec : Primrec MachineHistoryTile.prevCenter :=
  Primrec.fst.comp (Primrec.snd.comp toTuple_primrec)

theorem prevRight_primrec : Primrec MachineHistoryTile.prevRight :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))

theorem nextLeft_primrec : Primrec MachineHistoryTile.nextLeft :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec)))

theorem nextCenter_primrec : Primrec MachineHistoryTile.nextCenter :=
  Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))))

theorem nextRight_primrec : Primrec MachineHistoryTile.nextRight :=
  Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))))

theorem mk_primrec :
    Primrec
      (fun p :
        MachineCell × MachineCell × MachineCell × MachineCell × MachineCell × MachineCell =>
        ({ prevLeft := p.1
           prevCenter := p.2.1
           prevRight := p.2.2.1
           nextLeft := p.2.2.2.1
           nextCenter := p.2.2.2.2.1
           nextRight := p.2.2.2.2.2 } : MachineHistoryTile)) :=
  ofTuple_primrec

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

theorem toTaggedWangTile_primrec :
    Primrec (fun p : Nat × Nat × MachineHistoryTile =>
      p.2.2.toTaggedWangTile p.1 p.2.1) := by
  let f : Nat × Nat × MachineHistoryTile → Nat × Nat × Nat × Nat := fun p =>
    (taggedTripleCellColor p.2.1 p.2.2.nextLeft p.2.2.nextCenter p.2.2.nextRight,
      taggedTripleCellColor p.1 p.2.2.prevLeft p.2.2.prevCenter p.2.2.prevRight,
      taggedOverlapCellColor p.1 p.2.2.prevCenter p.2.2.prevRight
        p.2.2.nextCenter p.2.2.nextRight,
      taggedOverlapCellColor p.1 p.2.2.prevLeft p.2.2.prevCenter
        p.2.2.nextLeft p.2.2.nextCenter)
  have hf : Primrec f := by
    dsimp [f]
    exact Primrec.pair
      (taggedTripleCellColor_primrec.comp
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair (nextLeft_primrec.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.pair (nextCenter_primrec.comp (Primrec.snd.comp Primrec.snd))
              (nextRight_primrec.comp (Primrec.snd.comp Primrec.snd))))))
      (Primrec.pair
        (taggedTripleCellColor_primrec.comp
          (Primrec.pair Primrec.fst
            (Primrec.pair (prevLeft_primrec.comp (Primrec.snd.comp Primrec.snd))
              (Primrec.pair (prevCenter_primrec.comp (Primrec.snd.comp Primrec.snd))
                (prevRight_primrec.comp (Primrec.snd.comp Primrec.snd))))))
        (Primrec.pair
          (taggedOverlapCellColor_primrec.comp
            (Primrec.pair Primrec.fst
              (Primrec.pair (prevCenter_primrec.comp (Primrec.snd.comp Primrec.snd))
                (Primrec.pair (prevRight_primrec.comp (Primrec.snd.comp Primrec.snd))
                  (Primrec.pair (nextCenter_primrec.comp (Primrec.snd.comp Primrec.snd))
                    (nextRight_primrec.comp (Primrec.snd.comp Primrec.snd)))))))
          (taggedOverlapCellColor_primrec.comp
            (Primrec.pair Primrec.fst
              (Primrec.pair (prevLeft_primrec.comp (Primrec.snd.comp Primrec.snd))
                (Primrec.pair (prevCenter_primrec.comp (Primrec.snd.comp Primrec.snd))
                  (Primrec.pair (nextLeft_primrec.comp (Primrec.snd.comp Primrec.snd))
                    (nextCenter_primrec.comp (Primrec.snd.comp Primrec.snd)))))))))
  exact (WangTile.ofTuple_primrec.comp hf).of_eq fun p => by
    rcases p with ⟨rowTag, nextRowTag, t⟩
    cases t
    rfl

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
  if localNextCell? M prevLeft prevCenter prevRight = some nextCenter ∧
      (prevLeft = MachineCell.boundary → nextLeft = MachineCell.boundary) then
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
      localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter ∧
      (t.prevLeft = MachineCell.boundary → t.nextLeft = MachineCell.boundary) := by
  cases t
  simp [machineHistoryTiles]


theorem mem_machineHistoryTiles_of_supported {M : Machine} {t : MachineHistoryTile}
    (hprevLeft : t.prevLeft.Mem M) (hprevCenter : t.prevCenter.Mem M)
    (hprevRight : t.prevRight.Mem M) (hnextLeft : t.nextLeft.Mem M)
    (hnextCenter : t.nextCenter.Mem M) (hnextRight : t.nextRight.Mem M)
    (hlocal : localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter)
    (hboundary : t.prevLeft = MachineCell.boundary → t.nextLeft = MachineCell.boundary) :
    t ∈ machineHistoryTiles M := by
  rw [mem_machineHistoryTiles_iff]
  exact ⟨mem_machineCells_of_mem hprevLeft,
    mem_machineCells_of_mem hprevCenter,
    mem_machineCells_of_mem hprevRight,
    mem_machineCells_of_mem hnextLeft,
    mem_machineCells_of_mem hnextCenter,
    mem_machineCells_of_mem hnextRight,
    hlocal, hboundary⟩

theorem localNextCell?_of_mem_machineHistoryTiles {M : Machine} {t : MachineHistoryTile}
    (ht : t ∈ machineHistoryTiles M) :
    localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter := by
  exact (mem_machineHistoryTiles_iff M t).1 ht |>.2.2.2.2.2.2.1

theorem nextLeft_boundary_of_mem_machineHistoryTiles {M : Machine} {t : MachineHistoryTile}
    (ht : t ∈ machineHistoryTiles M)
    (hprev : t.prevLeft = MachineCell.boundary) :
    t.nextLeft = MachineCell.boundary := by
  exact (mem_machineHistoryTiles_iff M t).1 ht |>.2.2.2.2.2.2.2 hprev

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


end LeanWang
