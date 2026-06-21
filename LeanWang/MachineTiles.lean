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

def isHead : MachineCell → Bool
  | boundary => false
  | plain _ => false
  | head _ _ => true

def isBoundary : MachineCell → Bool
  | boundary => true
  | plain _ => false
  | head _ _ => false

def plain? : MachineCell → Option Nat
  | plain a => some a
  | _ => none

def head? : MachineCell → Option (Nat × Nat)
  | head q a => some (q, a)
  | _ => none

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

instance instPrimcodableMachineCell : Primcodable MachineCell :=
  Primcodable.ofEquiv MachineCell.CodeType MachineCell.equivSum

namespace MachineCell

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

theorem code_primrec : Primrec MachineCell.code := by
  have hrest :
      Primrec₂ (fun (_ : MachineCell) (r : Nat ⊕ Nat × Nat) =>
        match r with
        | Sum.inl a => Nat.pair 0 a
        | Sum.inr p => Nat.pair 1 (Nat.pair p.1 p.2)) := by
    apply Primrec₂.mk
    refine (Primrec.sumCasesOn
      (α := MachineCell × (Nat ⊕ Nat × Nat)) (β := Nat) (γ := Nat × Nat) (σ := Nat)
      (f := fun p : MachineCell × (Nat ⊕ Nat × Nat) => p.2)
      (g := fun _ a => Nat.pair 0 a)
      (h := fun _ p => Nat.pair 1 (Nat.pair p.1 p.2))
      Primrec.snd ?_ ?_).of_eq ?_
    · exact Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd
    · exact Primrec₂.natPair.comp (Primrec.const 1)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))
    · intro p
      cases p.2 <;> rfl
  refine (Primrec.sumCasesOn
    (α := MachineCell) (β := Unit) (γ := Nat ⊕ Nat × Nat) (σ := Nat)
    (f := MachineCell.toSum)
    (g := fun _ _ => Nat.pair 2 0)
    (h := fun _ r =>
      match r with
      | Sum.inl a => Nat.pair 0 a
      | Sum.inr p => Nat.pair 1 (Nat.pair p.1 p.2))
    toSum_primrec ?_ hrest).of_eq ?_
  · exact (Primrec.const (Nat.pair 2 0)).to₂
  · intro c
    cases c <;> rfl

theorem isBoundary_primrec : Primrec MachineCell.isBoundary := by
  exact (Primrec.eq.decide.comp Primrec.id (Primrec.const MachineCell.boundary)).of_eq
    fun c => by cases c <;> rfl

theorem plain?_primrec : Primrec MachineCell.plain? := by
  have hrest :
      Primrec₂ (fun (_ : MachineCell) (r : Nat ⊕ Nat × Nat) =>
        match r with
        | Sum.inl a => some a
        | Sum.inr _ => none) := by
    apply Primrec₂.mk
    refine (Primrec.sumCasesOn
      (α := MachineCell × (Nat ⊕ Nat × Nat)) (β := Nat) (γ := Nat × Nat)
      (σ := Option Nat)
      (f := fun p : MachineCell × (Nat ⊕ Nat × Nat) => p.2)
      (g := fun _ a => some a)
      (h := fun _ _ => none)
      Primrec.snd ?_ ?_).of_eq ?_
    · exact (Primrec.option_some.comp Primrec.snd).to₂
    · exact (Primrec.const none).to₂
    · intro p
      cases p.2 <;> rfl
  refine (Primrec.sumCasesOn
    (α := MachineCell) (β := Unit) (γ := Nat ⊕ Nat × Nat) (σ := Option Nat)
    (f := MachineCell.toSum)
    (g := fun _ _ => none)
    (h := fun _ r =>
      match r with
      | Sum.inl a => some a
      | Sum.inr _ => none)
    toSum_primrec ?_ hrest).of_eq ?_
  · exact (Primrec.const none).to₂
  · intro c
    cases c <;> rfl

theorem head?_primrec : Primrec MachineCell.head? := by
  have hrest :
      Primrec₂ (fun (_ : MachineCell) (r : Nat ⊕ Nat × Nat) =>
        match r with
        | Sum.inl _ => none
        | Sum.inr p => some p) := by
    apply Primrec₂.mk
    refine (Primrec.sumCasesOn
      (α := MachineCell × (Nat ⊕ Nat × Nat)) (β := Nat) (γ := Nat × Nat)
      (σ := Option (Nat × Nat))
      (f := fun p : MachineCell × (Nat ⊕ Nat × Nat) => p.2)
      (g := fun _ _ => none)
      (h := fun _ p => some p)
      Primrec.snd ?_ ?_).of_eq ?_
    · exact (Primrec.const none).to₂
    · exact (Primrec.option_some.comp Primrec.snd).to₂
    · intro p
      cases p.2 <;> rfl
  refine (Primrec.sumCasesOn
    (α := MachineCell) (β := Unit) (γ := Nat ⊕ Nat × Nat) (σ := Option (Nat × Nat))
    (f := MachineCell.toSum)
    (g := fun _ _ => none)
    (h := fun _ r =>
      match r with
      | Sum.inl _ => none
      | Sum.inr p => some p)
    toSum_primrec ?_ hrest).of_eq ?_
  · exact (Primrec.const none).to₂
  · intro c
    cases c <;> rfl

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

/-- The machine-cell support generated directly from finite table-program data. -/
def tableProgramMachineCells (P : TableProgram) : List MachineCell :=
  MachineCell.boundary :: (P.supportedSymbols.map MachineCell.plain) ++
    (P.supportedStates.filter fun q => q ≠ P.halt).flatMap fun q =>
      P.supportedSymbols.map fun a => MachineCell.head q a

theorem tableProgramMachineCells_eq_machineCells (P : TableProgram) :
    tableProgramMachineCells P = machineCells P.toMachine := by
  rfl

theorem tableProgramMachineCells_primrec : Primrec tableProgramMachineCells := by
  have hplain : Primrec (fun P : TableProgram =>
      P.supportedSymbols.map MachineCell.plain) :=
    Primrec.list_map TableProgram.supportedSymbols_primrec
      (MachineCell.plain_primrec.comp Primrec.snd).to₂
  have hnonhaltRel : PrimrecRel (fun (q : Nat) (P : TableProgram) => q ≠ P.halt) := by
    have hrelEq : PrimrecRel (fun (q : Nat) (P : TableProgram) => q = P.halt) :=
      Primrec.eq.comp₂ Primrec₂.left (TableProgram.halt_primrec.comp₂ Primrec₂.right)
    exact hrelEq.not
  have hnonhalt : Primrec (fun P : TableProgram =>
      P.supportedStates.filter fun q => q ≠ P.halt) :=
    (hnonhaltRel.listFilter.comp TableProgram.supportedStates_primrec Primrec.id).of_eq
      fun _ => rfl
  have hheads : Primrec (fun P : TableProgram =>
      (P.supportedStates.filter fun q => q ≠ P.halt).flatMap fun q =>
        P.supportedSymbols.map fun a => MachineCell.head q a) := by
    refine Primrec.list_flatMap hnonhalt ?_
    apply Primrec₂.mk
    refine Primrec.list_map (TableProgram.supportedSymbols_primrec.comp Primrec.fst) ?_
    rw [← Primrec₂.uncurry]
    exact MachineCell.head_primrec.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  unfold tableProgramMachineCells
  exact Primrec.list_cons.comp (Primrec.const MachineCell.boundary)
    (Primrec.list_append.comp hplain hheads)

theorem tableProgramMachineCells_computable : Computable tableProgramMachineCells :=
  tableProgramMachineCells_primrec.to_comp

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

def tableProgramLocalNextCell?
    (P : TableProgram) (left center right : MachineCell) : Option MachineCell :=
  match left, center, right with
  | _, MachineCell.boundary, _ => none
  | _, MachineCell.head q a, _ =>
      if _h : q = P.toTableMachine.halt then
        none
      else
        let (write, q', move) := P.toTableMachine.step q a
        match left, move with
        | MachineCell.boundary, Move.left =>
            if q' = P.toTableMachine.halt then none else some (MachineCell.head q' write)
        | _, _ => some (MachineCell.plain write)
  | MachineCell.head q a, MachineCell.plain b, _ =>
      if _h : q = P.toTableMachine.halt then
        none
      else
        let (_write, q', move) := P.toTableMachine.step q a
        match move with
        | Move.right => if q' = P.toTableMachine.halt then none else some (MachineCell.head q' b)
        | Move.left => some (MachineCell.plain b)
  | _, MachineCell.plain b, MachineCell.head q a =>
      if _h : q = P.toTableMachine.halt then
        none
      else
        let (_write, q', move) := P.toTableMachine.step q a
        match move with
        | Move.left => if q' = P.toTableMachine.halt then none else some (MachineCell.head q' b)
        | Move.right => some (MachineCell.plain b)
  | MachineCell.boundary, MachineCell.plain b, _ =>
      some (MachineCell.plain b)
  | _, MachineCell.plain b, _ =>
      some (MachineCell.plain b)

def tableProgramCenterHeadNext?
    (P : TableProgram) (left : MachineCell) (q a : Nat) : Option MachineCell :=
  if q = P.toTableMachine.halt then
    none
  else
    let action := P.toTableMachine.step q a
    let write := action.1
    let q' := action.2.1
    let move := action.2.2
    if left.isBoundary && decide (move = Move.left) then
      if q' = P.toTableMachine.halt then none else some (MachineCell.head q' write)
    else
      some (MachineCell.plain write)

theorem tableProgramCenterHeadNext?_primrec :
    Primrec (fun p : TableProgram × MachineCell × Nat × Nat =>
      tableProgramCenterHeadNext? p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let action : TableProgram × MachineCell × Nat × Nat → Nat × Nat × Move := fun p =>
    p.1.toTableMachine.step p.2.2.1 p.2.2.2
  have haction : Primrec action := by
    exact (TableProgram.step_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))).of_eq fun _ => rfl
  let leftFn : TableProgram × MachineCell × Nat × Nat → MachineCell := fun p => p.2.1
  let qFn : TableProgram × MachineCell × Nat × Nat → Nat := fun p => p.2.2.1
  let write : TableProgram × MachineCell × Nat × Nat → Nat := fun p => (action p).1
  let q' : TableProgram × MachineCell × Nat × Nat → Nat := fun p => (action p).2.1
  let move : TableProgram × MachineCell × Nat × Nat → Move := fun p => (action p).2.2
  have hleft : Primrec leftFn := Primrec.fst.comp Primrec.snd
  have hq : Primrec qFn := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hwrite : Primrec write := Primrec.fst.comp haction
  have hq' : Primrec q' := Primrec.fst.comp (Primrec.snd.comp haction)
  have hmove : Primrec move := Primrec.snd.comp (Primrec.snd.comp haction)
  have hqHalt :
      PrimrecPred (fun p : TableProgram × MachineCell × Nat × Nat => qFn p = p.1.halt) :=
    Primrec.eq.comp hq (TableProgram.halt_primrec.comp Primrec.fst)
  have hq'Halt :
      PrimrecPred (fun p : TableProgram × MachineCell × Nat × Nat => q' p = p.1.halt) :=
    Primrec.eq.comp hq' (TableProgram.halt_primrec.comp Primrec.fst)
  have hleftBoundary : Primrec (fun p : TableProgram × MachineCell × Nat × Nat =>
      (leftFn p).isBoundary) :=
    MachineCell.isBoundary_primrec.comp hleft
  have hmoveLeftBool : Primrec (fun p : TableProgram × MachineCell × Nat × Nat =>
      decide (move p = Move.left)) :=
    Primrec.eq.decide.comp hmove (Primrec.const Move.left)
  have hboundaryMove :
      PrimrecPred (fun p : TableProgram × MachineCell × Nat × Nat =>
        ((leftFn p).isBoundary && decide (move p = Move.left)) = true) :=
    Primrec.primrecPred
      (Primrec.eq.decide.comp
        (Primrec.and.comp hleftBoundary hmoveLeftBool)
        (Primrec.const true))
  have hsomeHead : Primrec (fun p : TableProgram × MachineCell × Nat × Nat =>
      some (MachineCell.head (q' p) (write p))) :=
    Primrec.option_some.comp
      (MachineCell.head_primrec.comp (Primrec.pair hq' hwrite))
  have hsomePlain : Primrec (fun p : TableProgram × MachineCell × Nat × Nat =>
      some (MachineCell.plain (write p))) :=
    Primrec.option_some.comp (MachineCell.plain_primrec.comp hwrite)
  refine (Primrec.ite hqHalt (Primrec.const none)
    (Primrec.ite hboundaryMove
      (Primrec.ite hq'Halt (Primrec.const none) hsomeHead)
      hsomePlain)).of_eq ?_
  intro p
  rcases p with ⟨P, left, q, a⟩
  rfl

def tableProgramLeftHeadNext?
    (P : TableProgram) (b q a : Nat) : Option MachineCell :=
  if q = P.toTableMachine.halt then
    none
  else
    let action := P.toTableMachine.step q a
    let q' := action.2.1
    let move := action.2.2
    if move = Move.right then
      if q' = P.toTableMachine.halt then none else some (MachineCell.head q' b)
    else
      some (MachineCell.plain b)

theorem tableProgramLeftHeadNext?_primrec :
    Primrec (fun p : TableProgram × Nat × Nat × Nat =>
      tableProgramLeftHeadNext? p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let action : TableProgram × Nat × Nat × Nat → Nat × Nat × Move := fun p =>
    p.1.toTableMachine.step p.2.2.1 p.2.2.2
  have haction : Primrec action := by
    exact (TableProgram.step_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))).of_eq fun _ => rfl
  let bFn : TableProgram × Nat × Nat × Nat → Nat := fun p => p.2.1
  let qFn : TableProgram × Nat × Nat × Nat → Nat := fun p => p.2.2.1
  let q' : TableProgram × Nat × Nat × Nat → Nat := fun p => (action p).2.1
  let move : TableProgram × Nat × Nat × Nat → Move := fun p => (action p).2.2
  have hb : Primrec bFn := Primrec.fst.comp Primrec.snd
  have hq : Primrec qFn := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hq' : Primrec q' := Primrec.fst.comp (Primrec.snd.comp haction)
  have hmove : Primrec move := Primrec.snd.comp (Primrec.snd.comp haction)
  have hqHalt : PrimrecPred (fun p : TableProgram × Nat × Nat × Nat => qFn p = p.1.halt) :=
    Primrec.eq.comp hq (TableProgram.halt_primrec.comp Primrec.fst)
  have hq'Halt : PrimrecPred (fun p : TableProgram × Nat × Nat × Nat => q' p = p.1.halt) :=
    Primrec.eq.comp hq' (TableProgram.halt_primrec.comp Primrec.fst)
  have hmoveRight :
      PrimrecPred (fun p : TableProgram × Nat × Nat × Nat => move p = Move.right) :=
    Primrec.eq.comp hmove (Primrec.const Move.right)
  have hsomeHead : Primrec (fun p : TableProgram × Nat × Nat × Nat =>
      some (MachineCell.head (q' p) (bFn p))) :=
    Primrec.option_some.comp
      (MachineCell.head_primrec.comp (Primrec.pair hq' hb))
  have hsomePlain : Primrec (fun p : TableProgram × Nat × Nat × Nat =>
      some (MachineCell.plain (bFn p))) :=
    Primrec.option_some.comp (MachineCell.plain_primrec.comp hb)
  refine (Primrec.ite hqHalt (Primrec.const none)
    (Primrec.ite hmoveRight
      (Primrec.ite hq'Halt (Primrec.const none) hsomeHead)
      hsomePlain)).of_eq ?_
  intro p
  rcases p with ⟨P, b, q, a⟩
  rfl

def tableProgramRightHeadNext?
    (P : TableProgram) (b q a : Nat) : Option MachineCell :=
  if q = P.toTableMachine.halt then
    none
  else
    let action := P.toTableMachine.step q a
    let q' := action.2.1
    let move := action.2.2
    if move = Move.left then
      if q' = P.toTableMachine.halt then none else some (MachineCell.head q' b)
    else
      some (MachineCell.plain b)

theorem tableProgramRightHeadNext?_primrec :
    Primrec (fun p : TableProgram × Nat × Nat × Nat =>
      tableProgramRightHeadNext? p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let action : TableProgram × Nat × Nat × Nat → Nat × Nat × Move := fun p =>
    p.1.toTableMachine.step p.2.2.1 p.2.2.2
  have haction : Primrec action := by
    exact (TableProgram.step_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))).of_eq fun _ => rfl
  let bFn : TableProgram × Nat × Nat × Nat → Nat := fun p => p.2.1
  let qFn : TableProgram × Nat × Nat × Nat → Nat := fun p => p.2.2.1
  let q' : TableProgram × Nat × Nat × Nat → Nat := fun p => (action p).2.1
  let move : TableProgram × Nat × Nat × Nat → Move := fun p => (action p).2.2
  have hb : Primrec bFn := Primrec.fst.comp Primrec.snd
  have hq : Primrec qFn := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hq' : Primrec q' := Primrec.fst.comp (Primrec.snd.comp haction)
  have hmove : Primrec move := Primrec.snd.comp (Primrec.snd.comp haction)
  have hqHalt : PrimrecPred (fun p : TableProgram × Nat × Nat × Nat => qFn p = p.1.halt) :=
    Primrec.eq.comp hq (TableProgram.halt_primrec.comp Primrec.fst)
  have hq'Halt : PrimrecPred (fun p : TableProgram × Nat × Nat × Nat => q' p = p.1.halt) :=
    Primrec.eq.comp hq' (TableProgram.halt_primrec.comp Primrec.fst)
  have hmoveLeft :
      PrimrecPred (fun p : TableProgram × Nat × Nat × Nat => move p = Move.left) :=
    Primrec.eq.comp hmove (Primrec.const Move.left)
  have hsomeHead : Primrec (fun p : TableProgram × Nat × Nat × Nat =>
      some (MachineCell.head (q' p) (bFn p))) :=
    Primrec.option_some.comp
      (MachineCell.head_primrec.comp (Primrec.pair hq' hb))
  have hsomePlain : Primrec (fun p : TableProgram × Nat × Nat × Nat =>
      some (MachineCell.plain (bFn p))) :=
    Primrec.option_some.comp (MachineCell.plain_primrec.comp hb)
  refine (Primrec.ite hqHalt (Primrec.const none)
    (Primrec.ite hmoveLeft
      (Primrec.ite hq'Halt (Primrec.const none) hsomeHead)
      hsomePlain)).of_eq ?_
  intro p
  rcases p with ⟨P, b, q, a⟩
  rfl

def tableProgramRightHeadOrPlainNext?
    (P : TableProgram) (right : MachineCell) (b : Nat) : Option MachineCell :=
  match right.head? with
  | some (q, a) =>
      tableProgramRightHeadNext? P b q a
  | none => some (MachineCell.plain b)

theorem tableProgramRightHeadOrPlainNext?_primrec :
    Primrec (fun p : TableProgram × MachineCell × Nat =>
      tableProgramRightHeadOrPlainNext? p.1 p.2.1 p.2.2) := by
  let rightFn : TableProgram × MachineCell × Nat → MachineCell := fun p => p.2.1
  let bFn : TableProgram × MachineCell × Nat → Nat := fun p => p.2.2
  have hright : Primrec rightFn := Primrec.fst.comp Primrec.snd
  have hb : Primrec bFn := Primrec.snd.comp Primrec.snd
  have hrightHead : Primrec (fun p : TableProgram × MachineCell × Nat => (rightFn p).head?) :=
    MachineCell.head?_primrec.comp hright
  have hnone : Primrec (fun p : TableProgram × MachineCell × Nat =>
      some (MachineCell.plain (bFn p))) :=
    Primrec.option_some.comp (MachineCell.plain_primrec.comp hb)
  have hsome : Primrec₂ (fun p : TableProgram × MachineCell × Nat => fun qa : Nat × Nat =>
      tableProgramRightHeadNext? p.1 p.2.2 qa.1 qa.2) := by
    apply Primrec₂.mk
    exact tableProgramRightHeadNext?_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  exact (Primrec.option_casesOn hrightHead hnone hsome).of_eq fun p => by
    rcases p with ⟨P, right, b⟩
    cases h : right.head? with
    | none => simp [tableProgramRightHeadOrPlainNext?, bFn, h]
    | some qa =>
        rcases qa with ⟨q, a⟩
        simp [tableProgramRightHeadOrPlainNext?, h]

def tableProgramPlainCenterNext?
    (P : TableProgram) (left right : MachineCell) (b : Nat) : Option MachineCell :=
  match left.head? with
  | some (q, a) =>
      tableProgramLeftHeadNext? P b q a
  | none =>
      tableProgramRightHeadOrPlainNext? P right b

theorem tableProgramPlainCenterNext?_primrec :
    Primrec (fun p : TableProgram × MachineCell × MachineCell × Nat =>
      tableProgramPlainCenterNext? p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let leftFn : TableProgram × MachineCell × MachineCell × Nat → MachineCell := fun p => p.2.1
  have hleft : Primrec leftFn := Primrec.fst.comp Primrec.snd
  have hleftHead :
      Primrec (fun p : TableProgram × MachineCell × MachineCell × Nat => (leftFn p).head?) :=
    MachineCell.head?_primrec.comp hleft
  have hnone : Primrec (fun p : TableProgram × MachineCell × MachineCell × Nat =>
      tableProgramRightHeadOrPlainNext? p.1 p.2.2.1 p.2.2.2) :=
    tableProgramRightHeadOrPlainNext?_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hsome :
      Primrec₂ (fun p : TableProgram × MachineCell × MachineCell × Nat =>
        fun qa : Nat × Nat => tableProgramLeftHeadNext? p.1 p.2.2.2 qa.1 qa.2) := by
    apply Primrec₂.mk
    exact tableProgramLeftHeadNext?_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          Primrec.snd))
  exact (Primrec.option_casesOn hleftHead hnone hsome).of_eq fun p => by
    rcases p with ⟨P, left, right, b⟩
    cases h : left.head? with
    | none => simp [tableProgramPlainCenterNext?, h]
    | some qa =>
        rcases qa with ⟨q, a⟩
        simp [tableProgramPlainCenterNext?, h]

def tableProgramLocalNextCellData?
    (P : TableProgram) (left center right : MachineCell) : Option MachineCell :=
  match center.head? with
  | some (q, a) =>
      tableProgramCenterHeadNext? P left q a
  | none =>
      match center.plain? with
      | none => none
      | some b =>
          tableProgramPlainCenterNext? P left right b

theorem tableProgramLocalNextCellData?_primrec :
    Primrec (fun p : TableProgram × MachineCell × MachineCell × MachineCell =>
      tableProgramLocalNextCellData? p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let centerFn : TableProgram × MachineCell × MachineCell × MachineCell → MachineCell :=
    fun p => p.2.2.1
  have hcenter : Primrec centerFn := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hcenterHead :
      Primrec (fun p : TableProgram × MachineCell × MachineCell × MachineCell =>
        (centerFn p).head?) :=
    MachineCell.head?_primrec.comp hcenter
  have hcenterPlain :
      Primrec (fun p : TableProgram × MachineCell × MachineCell × MachineCell =>
        (centerFn p).plain?) :=
    MachineCell.plain?_primrec.comp hcenter
  have hcenterSome :
      Primrec₂ (fun p : TableProgram × MachineCell × MachineCell × MachineCell =>
        fun qa : Nat × Nat => tableProgramCenterHeadNext? p.1 p.2.1 qa.1 qa.2) := by
    apply Primrec₂.mk
    exact tableProgramCenterHeadNext?_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  have hplainSome :
      Primrec₂ (fun p : TableProgram × MachineCell × MachineCell × MachineCell =>
        fun b : Nat => tableProgramPlainCenterNext? p.1 p.2.1 p.2.2.2 b) := by
    apply Primrec₂.mk
    exact tableProgramPlainCenterNext?_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
            Primrec.snd)))
  have hcenterNone :=
    Primrec.option_casesOn hcenterPlain (Primrec.const (none : Option MachineCell)) hplainSome
  exact (Primrec.option_casesOn hcenterHead hcenterNone hcenterSome).of_eq fun p => by
    rcases p with ⟨P, left, center, right⟩
    cases hhead : center.head? with
    | none =>
        cases hplain : center.plain? with
        | none => simp [tableProgramLocalNextCellData?, hhead, hplain]
        | some b => simp [tableProgramLocalNextCellData?, hhead, hplain]
    | some qa =>
        rcases qa with ⟨q, a⟩
        simp [tableProgramLocalNextCellData?, hhead]

theorem tableProgramLocalNextCellData?_eq_tableProgramLocalNextCell?
    (P : TableProgram) (left center right : MachineCell) :
    tableProgramLocalNextCellData? P left center right =
      tableProgramLocalNextCell? P left center right := by
  cases left <;> cases center <;> cases right <;>
    simp only [tableProgramLocalNextCellData?, tableProgramPlainCenterNext?,
      tableProgramRightHeadOrPlainNext?, tableProgramCenterHeadNext?,
      tableProgramLeftHeadNext?, tableProgramRightHeadNext?, tableProgramLocalNextCell?,
      MachineCell.head?, MachineCell.plain?, MachineCell.isBoundary]
    <;> try
      (cases hmove : (P.toTableMachine.step _ _).2.2 <;>
        simp only [Bool.true_and, Bool.false_and, decide_eq_true_eq, reduceCtorEq, if_true,
          if_false])
    <;> repeat' split
    <;> rfl

theorem tableProgramLocalNextCell?_eq_localNextCell?
    (P : TableProgram) (left center right : MachineCell) :
    tableProgramLocalNextCell? P left center right =
      localNextCell? P.toMachine left center right := by
  cases left <;> cases center <;> cases right <;> rfl

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

theorem localNextCell?_at_next_halt_head {M : Machine} {c : ID}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).2.1 = M.halt) :
    localNextCell? M
        (c.cellAtLeft ((M.step c.state (c.tape c.head)).2.2.apply c.head))
        (c.cellAt ((M.step c.state (c.tape c.head)).2.2.apply c.head))
        (c.cellAt ((M.step c.state (c.tape c.head)).2.2.apply c.head + 1)) =
      none := by
  rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
  have hstate' : state' = M.halt := by
    simpa [hstep] using hnextState
  cases move with
  | left =>
      cases hhead : c.head with
      | zero =>
          have hstep0 :
              M.step c.state (c.tape 0) = (write, state', Move.left) := by
            simpa [hhead] using hstep
          simp [ID.cellAt, hstate, hstep0, hstate',
            localNextCell?, Move.apply, hhead]
      | succ pred =>
          have hstepPred :
              M.step c.state (c.tape (pred + 1)) =
                (write, state', Move.left) := by
            simpa [hhead] using hstep
          cases pred with
          | zero =>
              have hcenter :
                  c.cellAt 0 = MachineCell.plain (c.tape 0) :=
                ID.cellAt_of_ne (c := c) (i := 0) (by omega)
              have hright :
                  c.cellAt 1 = MachineCell.head c.state (c.tape 1) := by
                simpa [hhead] using ID.cellAt_head c
              change localNextCell? M MachineCell.boundary (c.cellAt 0)
                  (c.cellAt 1) = none
              rw [hcenter, hright]
              simp [localNextCell?, hstate, hstepPred, hstate']
          | succ leftPred =>
              have hleft :
                  c.cellAtLeft (leftPred + 1) =
                    MachineCell.plain (c.tape leftPred) := by
                have hne : leftPred ≠ c.head := by omega
                simp [ID.cellAtLeft, ID.cellAt, hne]
              have hcenter :
                  c.cellAt (leftPred + 1) =
                    MachineCell.plain (c.tape (leftPred + 1)) :=
                ID.cellAt_of_ne (c := c) (i := leftPred + 1) (by omega)
              have hright :
                  c.cellAt (leftPred + 1 + 1) =
                    MachineCell.head c.state (c.tape (leftPred + 1 + 1)) := by
                simpa [hhead] using ID.cellAt_head c
              change localNextCell? M (c.cellAtLeft (leftPred + 1))
                  (c.cellAt (leftPred + 1))
                  (c.cellAt (leftPred + 1 + 1)) = none
              rw [hleft, hcenter, hright]
              simp [localNextCell?, hstate, hstepPred, hstate']
  | right =>
      simp [ID.cellAt, ID.cellAtLeft, hstate, hstep,
        hstate', localNextCell?, Move.apply]

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

theorem runHistoryTile_local_of_state_ne_halt {M : Machine} {time : Nat}
    (hstate : (M.runEmpty time).state ≠ M.halt)
    (hnextRun : (M.runEmpty (time + 1)).state ≠ M.halt)
    (pos : Nat) :
    localNextCell? M (runHistoryTile M time pos).prevLeft
        (runHistoryTile M time pos).prevCenter
        (runHistoryTile M time pos).prevRight =
      some (runHistoryTile M time pos).nextCenter := by
  let c := M.runEmpty time
  have hstate' : c.state ≠ M.halt := by
    simpa [c] using hstate
  have hnextState : (M.step c.state (c.tape c.head)).2.1 ≠ M.halt := by
    rw [← Machine.nextID_state_of_ne_halt hstate']
    simpa [c, Machine.runEmpty_succ] using hnextRun
  simpa [runHistoryTile, Machine.runCell, Machine.runCellLeft, c,
    Machine.runEmpty_succ] using
    Machine.localNextCell?_cellAt (M := M) (c := c) (pos := pos) hstate' hnextState

theorem runHistoryTile_local_of_not_halts {M : Machine} (h : ¬ M.HaltsEmpty)
    (time pos : Nat) :
    localNextCell? M (runHistoryTile M time pos).prevLeft
        (runHistoryTile M time pos).prevCenter
        (runHistoryTile M time pos).prevRight =
      some (runHistoryTile M time pos).nextCenter := by
  exact runHistoryTile_local_of_state_ne_halt
    (M := M)
    (M.runEmpty_state_ne_halt_of_not_halts h time)
    (M.runEmpty_state_ne_halt_of_not_halts h (time + 1))
    pos

theorem runHistoryTile_boundaryOK (M : Machine) (time pos : Nat) :
    (runHistoryTile M time pos).prevLeft = MachineCell.boundary →
      (runHistoryTile M time pos).nextLeft = MachineCell.boundary := by
  cases pos with
  | zero =>
      simp [runHistoryTile, Machine.runCellLeft]
  | succ pos =>
      intro hprev
      have hnot : (M.runEmpty time).cellAt pos ≠ MachineCell.boundary :=
        ID.cellAt_ne_boundary (M.runEmpty time) pos
      exact False.elim (hnot (by
        simpa [runHistoryTile, Machine.runCellLeft] using hprev))

def machineHistoryTilePrefixes2 (cells : List MachineCell) :
    List (MachineCell × MachineCell) := do
  let prevLeft ← cells
  let prevCenter ← cells
  pure (prevLeft, prevCenter)

theorem machineHistoryTilePrefixes2_primrec : Primrec machineHistoryTilePrefixes2 := by
  unfold machineHistoryTilePrefixes2
  refine Primrec.list_flatMap Primrec.id ?_
  apply Primrec₂.mk
  have hmap :
      Primrec₂ (fun p : List MachineCell × MachineCell =>
        fun c : MachineCell => (p.2, c)) := by
    rw [← Primrec₂.uncurry]
    exact Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_map
    (show Primrec (fun p : List MachineCell × MachineCell => p.1) from Primrec.fst) hmap
    ).of_eq fun p => by
      induction p.1 with
      | nil => rfl
      | cons _ _ ih => simp [ih]

def machineHistoryTilePrefixes3 (cells : List MachineCell) :
    List ((MachineCell × MachineCell) × MachineCell) := do
  let pref ← machineHistoryTilePrefixes2 cells
  let prevRight ← cells
  pure (pref, prevRight)

theorem machineHistoryTilePrefixes3_primrec : Primrec machineHistoryTilePrefixes3 := by
  unfold machineHistoryTilePrefixes3
  refine Primrec.list_flatMap machineHistoryTilePrefixes2_primrec ?_
  apply Primrec₂.mk
  have hmap :
      Primrec₂ (fun p : List MachineCell × (MachineCell × MachineCell) =>
        fun c : MachineCell => (p.2, c)) := by
    rw [← Primrec₂.uncurry]
    exact Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_map
    (show Primrec (fun p : List MachineCell × (MachineCell × MachineCell) => p.1) from
      Primrec.fst) hmap).of_eq fun p => by
      induction p.1 with
      | nil => rfl
      | cons _ _ ih => simp [ih]

def machineHistoryTilePrefixes4 (cells : List MachineCell) :
    List (((MachineCell × MachineCell) × MachineCell) × MachineCell) := do
  let pref ← machineHistoryTilePrefixes3 cells
  let nextLeft ← cells
  pure (pref, nextLeft)

theorem machineHistoryTilePrefixes4_primrec : Primrec machineHistoryTilePrefixes4 := by
  unfold machineHistoryTilePrefixes4
  refine Primrec.list_flatMap machineHistoryTilePrefixes3_primrec ?_
  apply Primrec₂.mk
  have hmap :
      Primrec₂ (fun p : List MachineCell × ((MachineCell × MachineCell) × MachineCell) =>
        fun c : MachineCell => (p.2, c)) := by
    rw [← Primrec₂.uncurry]
    exact Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_map
    (show Primrec
      (fun p : List MachineCell × ((MachineCell × MachineCell) × MachineCell) => p.1) from
      Primrec.fst) hmap).of_eq fun p => by
      induction p.1 with
      | nil => rfl
      | cons _ _ ih => simp [ih]

def machineHistoryTilePrefixes5 (cells : List MachineCell) :
    List ((((MachineCell × MachineCell) × MachineCell) × MachineCell) × MachineCell) := do
  let pref ← machineHistoryTilePrefixes4 cells
  let nextCenter ← cells
  pure (pref, nextCenter)

theorem machineHistoryTilePrefixes5_primrec : Primrec machineHistoryTilePrefixes5 := by
  unfold machineHistoryTilePrefixes5
  refine Primrec.list_flatMap machineHistoryTilePrefixes4_primrec ?_
  apply Primrec₂.mk
  have hmap :
      Primrec₂ (fun p : List MachineCell ×
        (((MachineCell × MachineCell) × MachineCell) × MachineCell) =>
        fun c : MachineCell => (p.2, c)) := by
    rw [← Primrec₂.uncurry]
    exact Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_map
    (show Primrec
      (fun p : List MachineCell ×
        (((MachineCell × MachineCell) × MachineCell) × MachineCell) => p.1) from
      Primrec.fst) hmap).of_eq fun p => by
      induction p.1 with
      | nil => rfl
      | cons _ _ ih => simp [ih]

/-- All six-cell history blocks over a given finite cell support,
before local validity filtering. -/
def machineHistoryTileCandidates (cells : List MachineCell) : List MachineHistoryTile := do
  let pref ← machineHistoryTilePrefixes5 cells
  let nextRight ← cells
  pure
    { prevLeft := pref.1.1.1.1
      prevCenter := pref.1.1.1.2
      prevRight := pref.1.1.2
      nextLeft := pref.1.2
      nextCenter := pref.2
      nextRight }

theorem machineHistoryTileCandidates_primrec : Primrec machineHistoryTileCandidates := by
  unfold machineHistoryTileCandidates
  refine Primrec.list_flatMap machineHistoryTilePrefixes5_primrec ?_
  apply Primrec₂.mk
  let pref :
      (List MachineCell ×
        ((((MachineCell × MachineCell) × MachineCell) × MachineCell) × MachineCell)) ×
        MachineCell →
        ((((MachineCell × MachineCell) × MachineCell) × MachineCell) × MachineCell) :=
    fun p => p.1.2
  have hprefix : Primrec pref := Primrec.snd.comp Primrec.fst
  let a4 : (List MachineCell ×
        ((((MachineCell × MachineCell) × MachineCell) × MachineCell) × MachineCell)) ×
        MachineCell →
        (((MachineCell × MachineCell) × MachineCell) × MachineCell) :=
    fun p => (pref p).1
  let a3 : (List MachineCell ×
        ((((MachineCell × MachineCell) × MachineCell) × MachineCell) × MachineCell)) ×
        MachineCell →
        ((MachineCell × MachineCell) × MachineCell) :=
    fun p => (pref p).1.1
  let a2 : (List MachineCell ×
        ((((MachineCell × MachineCell) × MachineCell) × MachineCell) × MachineCell)) ×
        MachineCell →
        (MachineCell × MachineCell) :=
    fun p => (pref p).1.1.1
  have ha4 : Primrec a4 := Primrec.fst.comp hprefix
  have ha3 : Primrec a3 := Primrec.fst.comp ha4
  have ha2 : Primrec a2 := Primrec.fst.comp ha3
  have hmap :
      Primrec₂ (fun p : List MachineCell ×
        ((((MachineCell × MachineCell) × MachineCell) × MachineCell) × MachineCell) =>
        fun nextRight : MachineCell =>
          ({ prevLeft := p.2.1.1.1.1
             prevCenter := p.2.1.1.1.2
             prevRight := p.2.1.1.2
             nextLeft := p.2.1.2
             nextCenter := p.2.2
             nextRight } : MachineHistoryTile)) := by
    rw [← Primrec₂.uncurry]
    exact MachineHistoryTile.mk_primrec.comp
      (Primrec.pair (Primrec.fst.comp ha2)
        (Primrec.pair (Primrec.snd.comp ha2)
          (Primrec.pair (Primrec.snd.comp ha3)
            (Primrec.pair (Primrec.snd.comp ha4)
              (Primrec.pair (Primrec.snd.comp hprefix) Primrec.snd)))))
  exact (Primrec.list_map
    (show Primrec
      (fun p : List MachineCell ×
        ((((MachineCell × MachineCell) × MachineCell) × MachineCell) × MachineCell) => p.1)
      from Primrec.fst) hmap).of_eq fun p => by
      induction p.1 with
      | nil => rfl
      | cons _ _ ih => simp [ih]

theorem mem_machineHistoryTileCandidates_iff (cells : List MachineCell) (t : MachineHistoryTile) :
    t ∈ machineHistoryTileCandidates cells ↔
      t.prevLeft ∈ cells ∧
      t.prevCenter ∈ cells ∧
      t.prevRight ∈ cells ∧
      t.nextLeft ∈ cells ∧
      t.nextCenter ∈ cells ∧
      t.nextRight ∈ cells := by
  cases t
  simp [machineHistoryTileCandidates, machineHistoryTilePrefixes2,
    machineHistoryTilePrefixes3, machineHistoryTilePrefixes4, machineHistoryTilePrefixes5,
    and_assoc]

def tableProgramHistoryTileValid (P : TableProgram) (t : MachineHistoryTile) : Prop :=
  tableProgramLocalNextCellData? P t.prevLeft t.prevCenter t.prevRight = some t.nextCenter ∧
    (t.prevLeft = MachineCell.boundary → t.nextLeft = MachineCell.boundary)

instance tableProgramHistoryTileValid_decidable (P : TableProgram) (t : MachineHistoryTile) :
    Decidable (tableProgramHistoryTileValid P t) := by
  unfold tableProgramHistoryTileValid
  infer_instance

theorem tableProgramHistoryTileValid_primrecPred :
    PrimrecPred (fun p : TableProgram × MachineHistoryTile =>
      tableProgramHistoryTileValid p.1 p.2) := by
  have hprevLeft : Primrec (fun p : TableProgram × MachineHistoryTile => p.2.prevLeft) :=
    MachineHistoryTile.prevLeft_primrec.comp Primrec.snd
  have hprevCenter : Primrec (fun p : TableProgram × MachineHistoryTile => p.2.prevCenter) :=
    MachineHistoryTile.prevCenter_primrec.comp Primrec.snd
  have hprevRight : Primrec (fun p : TableProgram × MachineHistoryTile => p.2.prevRight) :=
    MachineHistoryTile.prevRight_primrec.comp Primrec.snd
  have hnextLeft : Primrec (fun p : TableProgram × MachineHistoryTile => p.2.nextLeft) :=
    MachineHistoryTile.nextLeft_primrec.comp Primrec.snd
  have hnextCenter : Primrec (fun p : TableProgram × MachineHistoryTile => p.2.nextCenter) :=
    MachineHistoryTile.nextCenter_primrec.comp Primrec.snd
  have hlocal : Primrec (fun p : TableProgram × MachineHistoryTile =>
      tableProgramLocalNextCellData? p.1 p.2.prevLeft p.2.prevCenter p.2.prevRight) :=
    tableProgramLocalNextCellData?_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair hprevLeft (Primrec.pair hprevCenter hprevRight)))
  have hlocalOK : PrimrecPred (fun p : TableProgram × MachineHistoryTile =>
      tableProgramLocalNextCellData? p.1 p.2.prevLeft p.2.prevCenter p.2.prevRight =
        some p.2.nextCenter) :=
    Primrec.eq.comp hlocal (Primrec.option_some.comp hnextCenter)
  have hprevBoundary : PrimrecPred (fun p : TableProgram × MachineHistoryTile =>
      p.2.prevLeft = MachineCell.boundary) :=
    Primrec.eq.comp hprevLeft (Primrec.const MachineCell.boundary)
  have hnextBoundary : PrimrecPred (fun p : TableProgram × MachineHistoryTile =>
      p.2.nextLeft = MachineCell.boundary) :=
    Primrec.eq.comp hnextLeft (Primrec.const MachineCell.boundary)
  have hboundaryOK : PrimrecPred (fun p : TableProgram × MachineHistoryTile =>
      p.2.prevLeft = MachineCell.boundary → p.2.nextLeft = MachineCell.boundary) :=
    (PrimrecPred.or hprevBoundary.not hnextBoundary).of_eq fun p => by
      by_cases h : p.2.prevLeft = MachineCell.boundary <;> simp [h]
  exact (PrimrecPred.and hlocalOK hboundaryOK).of_eq fun p => by
    rfl

def tableProgramMachineHistoryTilesData (P : TableProgram) : List MachineHistoryTile :=
  (machineHistoryTileCandidates (tableProgramMachineCells P)).filterMap fun t =>
    if tableProgramHistoryTileValid P t then some t else none

theorem tableProgramMachineHistoryTilesData_primrec :
    Primrec tableProgramMachineHistoryTilesData := by
  unfold tableProgramMachineHistoryTilesData
  have hcandidates : Primrec (fun P : TableProgram =>
      machineHistoryTileCandidates (tableProgramMachineCells P)) :=
    machineHistoryTileCandidates_primrec.comp tableProgramMachineCells_primrec
  have hfilter :
      Primrec₂ (fun P : TableProgram => fun t : MachineHistoryTile =>
        if tableProgramHistoryTileValid P t then some t else none) :=
    Primrec.ite tableProgramHistoryTileValid_primrecPred
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact Primrec.listFilterMap hcandidates hfilter

theorem tableProgramMachineHistoryTilesData_computable :
    Computable tableProgramMachineHistoryTilesData :=
  tableProgramMachineHistoryTilesData_primrec.to_comp

theorem mem_tableProgramMachineHistoryTilesData_iff (P : TableProgram)
    (t : MachineHistoryTile) :
    t ∈ tableProgramMachineHistoryTilesData P ↔
      t.prevLeft ∈ tableProgramMachineCells P ∧
      t.prevCenter ∈ tableProgramMachineCells P ∧
      t.prevRight ∈ tableProgramMachineCells P ∧
      t.nextLeft ∈ tableProgramMachineCells P ∧
      t.nextCenter ∈ tableProgramMachineCells P ∧
      t.nextRight ∈ tableProgramMachineCells P ∧
      tableProgramLocalNextCell? P t.prevLeft t.prevCenter t.prevRight = some t.nextCenter ∧
      (t.prevLeft = MachineCell.boundary → t.nextLeft = MachineCell.boundary) := by
  simp [tableProgramMachineHistoryTilesData, tableProgramHistoryTileValid,
    mem_machineHistoryTileCandidates_iff,
    tableProgramLocalNextCellData?_eq_tableProgramLocalNextCell?, and_assoc]

def tableProgramNormalRowMachineTilesData (P : TableProgram) : TileSet :=
  (tableProgramMachineHistoryTilesData P).map
    (MachineHistoryTile.toTaggedWangTile normalRowTag normalRowTag)

theorem tableProgramNormalRowMachineTilesData_primrec :
    Primrec tableProgramNormalRowMachineTilesData := by
  unfold tableProgramNormalRowMachineTilesData
  refine Primrec.list_map tableProgramMachineHistoryTilesData_primrec ?_
  apply Primrec₂.mk
  exact MachineHistoryTile.toTaggedWangTile_primrec.comp
    (Primrec.pair (Primrec.const normalRowTag)
      (Primrec.pair (Primrec.const normalRowTag) Primrec.snd))

theorem tableProgramNormalRowMachineTilesData_computable :
    Computable tableProgramNormalRowMachineTilesData :=
  tableProgramNormalRowMachineTilesData_primrec.to_comp

def tableProgramLocalNextCellDataD
    (P : TableProgram) (left center right fallback : MachineCell) : MachineCell :=
  (tableProgramLocalNextCellData? P left center right).getD fallback

theorem tableProgramLocalNextCellDataD_primrec :
    Primrec (fun p : TableProgram × MachineCell × MachineCell × MachineCell × MachineCell =>
      tableProgramLocalNextCellDataD p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold tableProgramLocalNextCellDataD
  have hoption :
      Primrec (fun p : TableProgram × MachineCell × MachineCell × MachineCell × MachineCell =>
      tableProgramLocalNextCellData? p.1 p.2.1 p.2.2.1 p.2.2.2.1) :=
    tableProgramLocalNextCellData?_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
  have hfallback : Primrec (fun p : TableProgram × MachineCell × MachineCell × MachineCell ×
      MachineCell => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.option_getD.comp hoption hfallback

def tableProgramInitialBlankCell (P : TableProgram) : MachineCell :=
  MachineCell.plain P.blank

theorem tableProgramInitialBlankCell_primrec :
    Primrec tableProgramInitialBlankCell :=
  MachineCell.plain_primrec.comp TableProgram.blank_primrec

def tableProgramInitialHeadCell (P : TableProgram) : MachineCell :=
  MachineCell.head P.start P.blank

theorem tableProgramInitialHeadCell_primrec :
    Primrec tableProgramInitialHeadCell :=
  MachineCell.head_primrec.comp
    (Primrec.pair TableProgram.start_primrec TableProgram.blank_primrec)

def tableProgramInitialNextAt
    (P : TableProgram) (left center right : MachineCell) : MachineCell :=
  tableProgramLocalNextCellDataD P left center right (tableProgramInitialBlankCell P)

theorem tableProgramInitialNextAt_primrec :
    Primrec (fun p : TableProgram × MachineCell × MachineCell × MachineCell =>
      tableProgramInitialNextAt p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold tableProgramInitialNextAt
  exact tableProgramLocalNextCellDataD_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
            (tableProgramInitialBlankCell_primrec.comp Primrec.fst)))))

def tableProgramInitialNext0 (P : TableProgram) : MachineCell :=
  tableProgramLocalNextCellDataD P MachineCell.boundary (tableProgramInitialHeadCell P)
    (tableProgramInitialBlankCell P) (tableProgramInitialHeadCell P)

theorem tableProgramInitialNext0_primrec : Primrec tableProgramInitialNext0 := by
  unfold tableProgramInitialNext0
  exact tableProgramLocalNextCellDataD_primrec.comp
    (Primrec.pair Primrec.id
      (Primrec.pair (Primrec.const MachineCell.boundary)
        (Primrec.pair tableProgramInitialHeadCell_primrec
          (Primrec.pair tableProgramInitialBlankCell_primrec
            tableProgramInitialHeadCell_primrec))))

def tableProgramInitialNext1 (P : TableProgram) : MachineCell :=
  tableProgramInitialNextAt P (tableProgramInitialHeadCell P) (tableProgramInitialBlankCell P)
    (tableProgramInitialBlankCell P)

theorem tableProgramInitialNext1_primrec : Primrec tableProgramInitialNext1 := by
  unfold tableProgramInitialNext1
  exact tableProgramInitialNextAt_primrec.comp
    (Primrec.pair Primrec.id
      (Primrec.pair tableProgramInitialHeadCell_primrec
        (Primrec.pair tableProgramInitialBlankCell_primrec
          tableProgramInitialBlankCell_primrec)))

def tableProgramInitialNext2 (P : TableProgram) : MachineCell :=
  tableProgramInitialNextAt P (tableProgramInitialBlankCell P) (tableProgramInitialBlankCell P)
    (tableProgramInitialBlankCell P)

theorem tableProgramInitialNext2_primrec : Primrec tableProgramInitialNext2 := by
  unfold tableProgramInitialNext2
  exact tableProgramInitialNextAt_primrec.comp
    (Primrec.pair Primrec.id
      (Primrec.pair tableProgramInitialBlankCell_primrec
        (Primrec.pair tableProgramInitialBlankCell_primrec
          tableProgramInitialBlankCell_primrec)))

def tableProgramInitialHistoryTile1 (P : TableProgram) : MachineHistoryTile where
  prevLeft := tableProgramInitialHeadCell P
  prevCenter := tableProgramInitialBlankCell P
  prevRight := tableProgramInitialBlankCell P
  nextLeft := tableProgramInitialNext0 P
  nextCenter := tableProgramInitialNext1 P
  nextRight := tableProgramInitialNext2 P

theorem tableProgramInitialHistoryTile1_primrec :
    Primrec tableProgramInitialHistoryTile1 := by
  exact MachineHistoryTile.mk_primrec.comp
    (Primrec.pair tableProgramInitialHeadCell_primrec
      (Primrec.pair tableProgramInitialBlankCell_primrec
        (Primrec.pair tableProgramInitialBlankCell_primrec
          (Primrec.pair tableProgramInitialNext0_primrec
            (Primrec.pair tableProgramInitialNext1_primrec
              tableProgramInitialNext2_primrec)))))

def tableProgramInitialHistoryTile2 (P : TableProgram) : MachineHistoryTile where
  prevLeft := tableProgramInitialBlankCell P
  prevCenter := tableProgramInitialBlankCell P
  prevRight := tableProgramInitialBlankCell P
  nextLeft := tableProgramInitialNext1 P
  nextCenter := tableProgramInitialNext2 P
  nextRight := tableProgramInitialNext2 P

theorem tableProgramInitialHistoryTile2_primrec :
    Primrec tableProgramInitialHistoryTile2 := by
  exact MachineHistoryTile.mk_primrec.comp
    (Primrec.pair tableProgramInitialBlankCell_primrec
      (Primrec.pair tableProgramInitialBlankCell_primrec
        (Primrec.pair tableProgramInitialBlankCell_primrec
          (Primrec.pair tableProgramInitialNext1_primrec
            (Primrec.pair tableProgramInitialNext2_primrec
              tableProgramInitialNext2_primrec)))))

def tableProgramInitialHistoryTile3 (P : TableProgram) : MachineHistoryTile where
  prevLeft := tableProgramInitialBlankCell P
  prevCenter := tableProgramInitialBlankCell P
  prevRight := tableProgramInitialBlankCell P
  nextLeft := tableProgramInitialNext2 P
  nextCenter := tableProgramInitialNext2 P
  nextRight := tableProgramInitialNext2 P

theorem tableProgramInitialHistoryTile3_primrec :
    Primrec tableProgramInitialHistoryTile3 := by
  exact MachineHistoryTile.mk_primrec.comp
    (Primrec.pair tableProgramInitialBlankCell_primrec
      (Primrec.pair tableProgramInitialBlankCell_primrec
        (Primrec.pair tableProgramInitialBlankCell_primrec
          (Primrec.pair tableProgramInitialNext2_primrec
            (Primrec.pair tableProgramInitialNext2_primrec
              tableProgramInitialNext2_primrec)))))

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

def tableProgramMachineHistoryTiles (P : TableProgram) : List MachineHistoryTile := do
  let cells := tableProgramMachineCells P
  let prevLeft ← cells
  let prevCenter ← cells
  let prevRight ← cells
  let nextLeft ← cells
  let nextCenter ← cells
  let nextRight ← cells
  if tableProgramLocalNextCell? P prevLeft prevCenter prevRight = some nextCenter ∧
      (prevLeft = MachineCell.boundary → nextLeft = MachineCell.boundary) then
    pure { prevLeft, prevCenter, prevRight, nextLeft, nextCenter, nextRight }
  else
    []

theorem tableProgramMachineHistoryTiles_eq_machineHistoryTiles (P : TableProgram) :
    tableProgramMachineHistoryTiles P = machineHistoryTiles P.toMachine := by
  simp [tableProgramMachineHistoryTiles, machineHistoryTiles,
    tableProgramMachineCells_eq_machineCells,
    tableProgramLocalNextCell?_eq_localNextCell?]

theorem mem_tableProgramMachineHistoryTiles_iff (P : TableProgram) (t : MachineHistoryTile) :
    t ∈ tableProgramMachineHistoryTiles P ↔
      t.prevLeft ∈ tableProgramMachineCells P ∧
      t.prevCenter ∈ tableProgramMachineCells P ∧
      t.prevRight ∈ tableProgramMachineCells P ∧
      t.nextLeft ∈ tableProgramMachineCells P ∧
      t.nextCenter ∈ tableProgramMachineCells P ∧
      t.nextRight ∈ tableProgramMachineCells P ∧
      tableProgramLocalNextCell? P t.prevLeft t.prevCenter t.prevRight = some t.nextCenter ∧
      (t.prevLeft = MachineCell.boundary → t.nextLeft = MachineCell.boundary) := by
  cases t
  simp [tableProgramMachineHistoryTiles]

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

theorem runHistoryTile_mem_machineHistoryTiles_of_not_halts {M : Machine}
    (h : ¬ M.HaltsEmpty) (time pos : Nat) :
    runHistoryTile M time pos ∈ machineHistoryTiles M := by
  rcases runHistoryTile_cells_mem_of_not_halts h time pos with
    ⟨hprevLeft, hprevCenter, hprevRight, hnextLeft, hnextCenter, hnextRight⟩
  exact mem_machineHistoryTiles_of_supported hprevLeft hprevCenter hprevRight
    hnextLeft hnextCenter hnextRight
    (runHistoryTile_local_of_not_halts h time pos)
    (runHistoryTile_boundaryOK M time pos)

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
    (hlocal : localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter)
    (hboundary : t.prevLeft = MachineCell.boundary → t.nextLeft = MachineCell.boundary) :
    t.toWangTile ∈ rawMachineTiles M :=
  toWangTile_mem_rawMachineTiles
    (mem_machineHistoryTiles_of_supported hprevLeft hprevCenter hprevRight
      hnextLeft hnextCenter hnextRight hlocal hboundary)

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

/--
The machine tiles generated by finite table-program data.

This is definitionally the semantic machine construction, but gives the compiler
side a data-level surface to target before unpacking into `Machine`.
-/
def tableProgramTiles (P : TableProgram) : TileSet :=
  machineTiles P.toMachine

/--
The distinguished seed generated by finite table-program data.

This is definitionally the semantic machine seed, but keeps reductions phrased
in terms of the finite table data produced by the compiler.
-/
def tableProgramSeed (P : TableProgram) : WangTile :=
  machineSeed P.toMachine

def tableProgramSeedHistoryTile (P : TableProgram) : MachineHistoryTile :=
  let action := P.toTableMachine.step P.start P.blank
  let write := action.1
  let state' := action.2.1
  let move := action.2.2
  { prevLeft := MachineCell.boundary
    prevCenter := MachineCell.head P.start P.blank
    prevRight := MachineCell.plain P.blank
    nextLeft := MachineCell.boundary
    nextCenter :=
      if P.start = P.halt then
        MachineCell.head P.start P.blank
      else
        match move with
        | Move.left => MachineCell.head state' write
        | Move.right => MachineCell.plain write
    nextRight :=
      if P.start = P.halt then
        MachineCell.plain P.blank
      else
        match move with
        | Move.left => MachineCell.plain P.blank
        | Move.right => MachineCell.head state' P.blank }

def tableProgramSeedData (P : TableProgram) : WangTile :=
  (tableProgramSeedHistoryTile P).toTaggedWangTile initialRowTag normalRowTag

theorem tableProgramSeedHistoryTile_eq_runHistoryTile (P : TableProgram) :
    tableProgramSeedHistoryTile P = runHistoryTile P.toMachine 0 0 := by
  unfold tableProgramSeedHistoryTile
  have htmBlank : P.toTableMachine.blank = P.blank := rfl
  have htmStart : P.toTableMachine.start = P.start := rfl
  have htmHalt : P.toTableMachine.halt = P.halt := rfl
  by_cases hstart : P.start = P.halt
  · simp [runHistoryTile, Machine.runCell, Machine.runCellLeft, Machine.runEmpty_zero,
      Machine.runEmpty_succ, Machine.nextID, Machine.initialID, ID.cellAt, ID.cellAtLeft,
      TableProgram.toMachine, TableMachine.toMachine, -TableProgram.toTableMachine_step,
      -TableMachine.toMachine_step, htmBlank, htmStart, htmHalt, hstart]
  · rcases hstep : P.toTableMachine.step P.start P.blank with ⟨write, state', move⟩
    cases move <;>
      simp [runHistoryTile, Machine.runCell, Machine.runCellLeft, Machine.runEmpty_zero,
        Machine.runEmpty_succ, Machine.nextID, Machine.initialID, ID.cellAt, ID.cellAtLeft,
        TableProgram.toMachine, TableMachine.toMachine, -TableProgram.toTableMachine_step,
        -TableMachine.toMachine_step, htmBlank, htmStart, htmHalt, hstart, hstep, Move.apply]

theorem tableProgramSeedData_eq_tableProgramSeed (P : TableProgram) :
    tableProgramSeedData P = tableProgramSeed P := by
  unfold tableProgramSeedData tableProgramSeed machineSeed taggedMachineSeed
  rw [tableProgramSeedHistoryTile_eq_runHistoryTile]

theorem tableProgramSeedHistoryTile_primrec :
    Primrec tableProgramSeedHistoryTile := by
  let action : TableProgram → Nat × Nat × Move := fun P =>
    P.toTableMachine.step P.start P.blank
  have haction : Primrec action := by
    exact (TableProgram.step_primrec.comp
      (Primrec.pair Primrec.id
        (Primrec.pair TableProgram.start_primrec TableProgram.blank_primrec))).of_eq fun _ => rfl
  let write : TableProgram → Nat := fun P => (action P).1
  let state' : TableProgram → Nat := fun P => (action P).2.1
  let move : TableProgram → Move := fun P => (action P).2.2
  have hwrite : Primrec write := Primrec.fst.comp haction
  have hstate' : Primrec state' := Primrec.fst.comp (Primrec.snd.comp haction)
  have hmove : Primrec move := Primrec.snd.comp (Primrec.snd.comp haction)
  have hstartHalt : PrimrecPred (fun P : TableProgram => P.start = P.halt) :=
    Primrec.eq.comp TableProgram.start_primrec TableProgram.halt_primrec
  have hmoveLeft : PrimrecPred (fun P : TableProgram => move P = Move.left) :=
    Primrec.eq.comp hmove (Primrec.const Move.left)
  have hprevCenter : Primrec (fun P : TableProgram => MachineCell.head P.start P.blank) :=
    MachineCell.head_primrec.comp
      (Primrec.pair TableProgram.start_primrec TableProgram.blank_primrec)
  have hprevRight : Primrec (fun P : TableProgram => MachineCell.plain P.blank) :=
    MachineCell.plain_primrec.comp TableProgram.blank_primrec
  have hnextCenter : Primrec (fun P : TableProgram =>
      if P.start = P.halt then
        MachineCell.head P.start P.blank
      else
        match move P with
        | Move.left => MachineCell.head (state' P) (write P)
        | Move.right => MachineCell.plain (write P)) := by
    refine Primrec.ite hstartHalt hprevCenter ?_
    refine (Primrec.ite hmoveLeft
      (MachineCell.head_primrec.comp (Primrec.pair hstate' hwrite))
      (MachineCell.plain_primrec.comp hwrite)).of_eq ?_
    intro P
    cases move P <;> rfl
  have hnextRight : Primrec (fun P : TableProgram =>
      if P.start = P.halt then
        MachineCell.plain P.blank
      else
        match move P with
        | Move.left => MachineCell.plain P.blank
        | Move.right => MachineCell.head (state' P) P.blank) := by
    refine Primrec.ite hstartHalt hprevRight ?_
    refine (Primrec.ite hmoveLeft hprevRight
      (MachineCell.head_primrec.comp (Primrec.pair hstate' TableProgram.blank_primrec))).of_eq ?_
    intro P
    cases move P <;> rfl
  let tileTuple :
      TableProgram →
        MachineCell × MachineCell × MachineCell × MachineCell × MachineCell × MachineCell :=
    fun P =>
      (MachineCell.boundary,
        MachineCell.head P.start P.blank,
        MachineCell.plain P.blank,
        MachineCell.boundary,
        if P.start = P.halt then
          MachineCell.head P.start P.blank
        else
          match move P with
          | Move.left => MachineCell.head (state' P) (write P)
          | Move.right => MachineCell.plain (write P),
        if P.start = P.halt then
          MachineCell.plain P.blank
        else
          match move P with
          | Move.left => MachineCell.plain P.blank
          | Move.right => MachineCell.head (state' P) P.blank)
  have htuple : Primrec tileTuple := by
    dsimp [tileTuple]
    exact
      Primrec.pair (Primrec.const MachineCell.boundary)
        (Primrec.pair hprevCenter
          (Primrec.pair hprevRight
            (Primrec.pair (Primrec.const MachineCell.boundary)
              (Primrec.pair hnextCenter hnextRight))))
  exact (MachineHistoryTile.mk_primrec.comp htuple).of_eq fun _ => rfl

theorem tableProgramSeedData_primrec : Primrec tableProgramSeedData := by
  unfold tableProgramSeedData
  exact MachineHistoryTile.toTaggedWangTile_primrec.comp
    (Primrec.pair (Primrec.const initialRowTag)
      (Primrec.pair (Primrec.const normalRowTag) tableProgramSeedHistoryTile_primrec))

theorem tableProgramSeed_computable : Computable tableProgramSeed :=
  tableProgramSeedData_primrec.to_comp.of_eq tableProgramSeedData_eq_tableProgramSeed

def tableProgramInitialRowHistoryTilesData (P : TableProgram) : List MachineHistoryTile :=
  [tableProgramSeedHistoryTile P,
    tableProgramInitialHistoryTile1 P,
    tableProgramInitialHistoryTile2 P,
    tableProgramInitialHistoryTile3 P]

theorem tableProgramInitialRowHistoryTilesData_primrec :
    Primrec tableProgramInitialRowHistoryTilesData := by
  unfold tableProgramInitialRowHistoryTilesData
  exact Primrec.list_cons.comp tableProgramSeedHistoryTile_primrec
    (Primrec.list_cons.comp tableProgramInitialHistoryTile1_primrec
      (Primrec.list_cons.comp tableProgramInitialHistoryTile2_primrec
        (Primrec.list_cons.comp tableProgramInitialHistoryTile3_primrec
          (Primrec.const []))))

def tableProgramInitialRowMachineTilesData (P : TableProgram) : TileSet :=
  (tableProgramInitialRowHistoryTilesData P).map
    (MachineHistoryTile.toTaggedWangTile initialRowTag normalRowTag)

theorem tableProgramInitialRowMachineTilesData_primrec :
    Primrec tableProgramInitialRowMachineTilesData := by
  unfold tableProgramInitialRowMachineTilesData
  refine Primrec.list_map tableProgramInitialRowHistoryTilesData_primrec ?_
  apply Primrec₂.mk
  exact MachineHistoryTile.toTaggedWangTile_primrec.comp
    (Primrec.pair (Primrec.const initialRowTag)
      (Primrec.pair (Primrec.const normalRowTag) Primrec.snd))

theorem tableProgramInitialRowMachineTilesData_computable :
    Computable tableProgramInitialRowMachineTilesData :=
  tableProgramInitialRowMachineTilesData_primrec.to_comp

def tableProgramTilesData (P : TableProgram) : TileSet :=
  tableProgramInitialRowMachineTilesData P ++ tableProgramNormalRowMachineTilesData P

theorem tableProgramTilesData_primrec : Primrec tableProgramTilesData := by
  unfold tableProgramTilesData
  exact Primrec.list_append.comp tableProgramInitialRowMachineTilesData_primrec
    tableProgramNormalRowMachineTilesData_primrec

theorem tableProgramTilesData_computable : Computable tableProgramTilesData :=
  tableProgramTilesData_primrec.to_comp

def tableProgramFixedDominoData (P : TableProgram) : TileSet × WangTile :=
  (tableProgramTilesData P, tableProgramSeedData P)

theorem tableProgramFixedDominoData_primrec :
    Primrec tableProgramFixedDominoData := by
  unfold tableProgramFixedDominoData
  exact Primrec.pair tableProgramTilesData_primrec tableProgramSeedData_primrec

theorem tableProgramFixedDominoData_computable :
    Computable tableProgramFixedDominoData :=
  tableProgramFixedDominoData_primrec.to_comp

/-- The fixed-domino instance generated by finite table-program data. -/
def tableProgramFixedDomino (P : TableProgram) : TileSet × WangTile :=
  (tableProgramTiles P, tableProgramSeed P)

@[simp]
theorem tableProgramFixedDomino_fst (P : TableProgram) :
    (tableProgramFixedDomino P).1 = tableProgramTiles P :=
  rfl

@[simp]
theorem tableProgramFixedDomino_snd (P : TableProgram) :
    (tableProgramFixedDomino P).2 = tableProgramSeed P :=
  rfl

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

theorem seeded_tiling_positive_row_decode {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) (time pos : Nat) :
    ∃ t : MachineHistoryTile,
      t ∈ machineHistoryTiles M ∧
        t.toTaggedWangTile normalRowTag normalRowTag = (x (pos, time + 1)).1 := by
  exact IsNormalMachineTile.positive_row_of_seeded_tiling hvalid hseed time pos

theorem seeded_tiling_positive_row_prev_cells_of_lower {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M)
    {time pos : Nat} {lower : MachineHistoryTile}
    (hlower :
      (x (pos, time)).1 =
        lower.toTaggedWangTile (machineRowTag time) normalRowTag) :
    ∃ upper : MachineHistoryTile,
      upper ∈ machineHistoryTiles M ∧
        upper.toTaggedWangTile normalRowTag normalRowTag = (x (pos, time + 1)).1 ∧
        upper.prevLeft = lower.nextLeft ∧
        upper.prevCenter = lower.nextCenter ∧
        upper.prevRight = lower.nextRight := by
  rcases seeded_tiling_positive_row_decode hvalid hseed time pos with
    ⟨upper, hupperMem, hupperTile⟩
  have hv : WangTile.VMatches
      (lower.toTaggedWangTile (machineRowTag time) normalRowTag)
      (upper.toTaggedWangTile normalRowTag normalRowTag) := by
    simpa [hlower, hupperTile] using hvalid.2 (pos, time)
  have hcells := (MachineHistoryTile.vMatches_toTaggedWangTile_iff_cells
    (machineRowTag time) normalRowTag normalRowTag normalRowTag
    lower upper).1 hv
  exact ⟨upper, hupperMem, hupperTile, hcells.2.1.symm,
    hcells.2.2.1.symm, hcells.2.2.2.symm⟩

theorem seeded_tiling_positive_row_hMatches_cells {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    {time pos : Nat} {left right : MachineHistoryTile}
    (hleft :
      left.toTaggedWangTile normalRowTag normalRowTag = (x (pos, time + 1)).1)
    (hright :
      right.toTaggedWangTile normalRowTag normalRowTag = (x (pos + 1, time + 1)).1) :
    left.prevCenter = right.prevLeft ∧
      left.prevRight = right.prevCenter ∧
      left.nextCenter = right.nextLeft ∧
      left.nextRight = right.nextCenter := by
  have hh : WangTile.HMatches
      (left.toTaggedWangTile normalRowTag normalRowTag)
      (right.toTaggedWangTile normalRowTag normalRowTag) := by
    simpa [hleft, hright] using hvalid.1 (pos, time + 1)
  exact (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
    normalRowTag normalRowTag normalRowTag normalRowTag left right).1 hh |>.2

theorem nextCenter_eq_runHistoryTile_nextCenter_of_prev_cells {M : Machine}
    {time pos : Nat} {t : MachineHistoryTile}
    (ht : t ∈ machineHistoryTiles M)
    (hstate : (M.runEmpty time).state ≠ M.halt)
    (hnextRun : (M.runEmpty (time + 1)).state ≠ M.halt)
    (hprevLeft : t.prevLeft = (runHistoryTile M time pos).prevLeft)
    (hprevCenter : t.prevCenter = (runHistoryTile M time pos).prevCenter)
    (hprevRight : t.prevRight = (runHistoryTile M time pos).prevRight) :
    t.nextCenter = (runHistoryTile M time pos).nextCenter := by
  have htlocal := localNextCell?_of_mem_machineHistoryTiles ht
  rw [hprevLeft, hprevCenter, hprevRight] at htlocal
  have hrun := runHistoryTile_local_of_state_ne_halt
    (M := M) hstate hnextRun pos
  rw [hrun] at htlocal
  exact Option.some.inj htlocal.symm

theorem seeded_tiling_next_row_prev_run_cells {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M)
    {time : Nat}
    (hrow : ∀ pos : Nat,
      ∃ t : MachineHistoryTile,
        t ∈ machineHistoryTiles M ∧
          t.toTaggedWangTile normalRowTag normalRowTag = (x (pos, time + 1)).1 ∧
          t.prevLeft = (runHistoryTile M (time + 1) pos).prevLeft ∧
          t.prevCenter = (runHistoryTile M (time + 1) pos).prevCenter ∧
          t.prevRight = (runHistoryTile M (time + 1) pos).prevRight)
    (hstate : (M.runEmpty (time + 1)).state ≠ M.halt)
    (hnextRun : (M.runEmpty (time + 1 + 1)).state ≠ M.halt)
    (pos : Nat) :
    ∃ t : MachineHistoryTile,
      t ∈ machineHistoryTiles M ∧
        t.toTaggedWangTile normalRowTag normalRowTag = (x (pos, time + 1 + 1)).1 ∧
        t.prevLeft = (runHistoryTile M (time + 1 + 1) pos).prevLeft ∧
        t.prevCenter = (runHistoryTile M (time + 1 + 1) pos).prevCenter ∧
        t.prevRight = (runHistoryTile M (time + 1 + 1) pos).prevRight := by
  rcases hrow pos with
    ⟨lower, hlowerMem, hlowerTile, hlowerPrevLeft,
      hlowerPrevCenter, hlowerPrevRight⟩
  rcases seeded_tiling_positive_row_prev_cells_of_lower hvalid hseed
      (time := time + 1) (pos := pos) (lower := lower)
      (by simpa using hlowerTile.symm) with
    ⟨upper, hupperMem, hupperTile, hupperPrevLeft,
      hupperPrevCenter, hupperPrevRight⟩
  have hlowerNextCenter :
      lower.nextCenter = (runHistoryTile M (time + 1) pos).nextCenter :=
    nextCenter_eq_runHistoryTile_nextCenter_of_prev_cells
      hlowerMem hstate hnextRun
      hlowerPrevLeft hlowerPrevCenter hlowerPrevRight
  have hlowerNextLeft :
      lower.nextLeft = (runHistoryTile M (time + 1) pos).nextLeft := by
    cases pos with
    | zero =>
        have hprevBoundary : lower.prevLeft = MachineCell.boundary := by
          simpa [runHistoryTile, Machine.runCellLeft] using hlowerPrevLeft
        calc
          lower.nextLeft = MachineCell.boundary :=
            nextLeft_boundary_of_mem_machineHistoryTiles hlowerMem hprevBoundary
          _ = (runHistoryTile M (time + 1) 0).nextLeft := by
            exact (runHistoryTile_boundaryOK M (time + 1) 0 (by
              simp [runHistoryTile, Machine.runCellLeft])).symm
    | succ pred =>
        rcases hrow pred with
          ⟨left, hleftMem, hleftTile, hleftPrevLeft,
            hleftPrevCenter, hleftPrevRight⟩
        have hmatches := seeded_tiling_positive_row_hMatches_cells
          (M := M) (x := x) hvalid (time := time) (pos := pred)
          (left := left) (right := lower) hleftTile hlowerTile
        have hleftNextCenter :
            left.nextCenter = (runHistoryTile M (time + 1) pred).nextCenter :=
          nextCenter_eq_runHistoryTile_nextCenter_of_prev_cells
            hleftMem hstate hnextRun
            hleftPrevLeft hleftPrevCenter hleftPrevRight
        calc
          lower.nextLeft = left.nextCenter := hmatches.2.2.1.symm
          _ = (runHistoryTile M (time + 1) pred).nextCenter := hleftNextCenter
          _ = (runHistoryTile M (time + 1) (pred + 1)).nextLeft := by
            simp [runHistoryTile, Machine.runCellLeft, Machine.runCell]
  have hlowerNextRight :
      lower.nextRight = (runHistoryTile M (time + 1) pos).nextRight := by
    rcases hrow (pos + 1) with
      ⟨right, hrightMem, hrightTile, hrightPrevLeft,
        hrightPrevCenter, hrightPrevRight⟩
    have hmatches := seeded_tiling_positive_row_hMatches_cells
      (M := M) (x := x) hvalid (time := time) (pos := pos)
      (left := lower) (right := right) hlowerTile hrightTile
    have hrightNextCenter :
        right.nextCenter = (runHistoryTile M (time + 1) (pos + 1)).nextCenter :=
      nextCenter_eq_runHistoryTile_nextCenter_of_prev_cells
        hrightMem hstate hnextRun
        hrightPrevLeft hrightPrevCenter hrightPrevRight
    calc
      lower.nextRight = right.nextCenter := hmatches.2.2.2
      _ = (runHistoryTile M (time + 1) (pos + 1)).nextCenter := hrightNextCenter
      _ = (runHistoryTile M (time + 1) pos).nextRight := by
        simp [runHistoryTile]
  exact ⟨upper, hupperMem, hupperTile, by
      rw [hupperPrevLeft, hlowerNextLeft]
      simp [runHistoryTile],
    by
      rw [hupperPrevCenter, hlowerNextCenter]
      simp [runHistoryTile],
    by
      rw [hupperPrevRight, hlowerNextRight]
      simp [runHistoryTile]⟩

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

theorem seeded_tiling_row_zero_tail_succ_eq {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    {pos : Nat} (hpos : 3 ≤ pos)
    (hleft : (x (pos, 0)).1 = runTaggedHistoryTile M 0 pos) :
    (x (pos + 1, 0)).1 = runTaggedHistoryTile M 0 (pos + 1) := by
  have hposSucc : 3 ≤ pos + 1 := by omega
  have hleftTail : runHistoryTile M 0 pos = runHistoryTile M 0 3 :=
    runHistoryTile_zero_eq_three_of_three_le M hpos
  have hrightTail : runHistoryTile M 0 (pos + 1) = runHistoryTile M 0 3 :=
    runHistoryTile_zero_eq_three_of_three_le M hposSucc
  have hh : WangTile.HMatches
      ((runHistoryTile M 0 3).toTaggedWangTile initialRowTag normalRowTag)
      (x (pos + 1, 0)).1 := by
    simpa [runTaggedHistoryTile, hleft, hleftTail] using hvalid.1 (pos, 0)
  rcases (mem_machineTiles_iff M (x (pos + 1, 0)).1).1 (x (pos + 1, 0)).2 with hinit | hnormal
  · rcases hinit with ⟨t, ht, htile⟩
    have hh' : WangTile.HMatches
        ((runHistoryTile M 0 3).toTaggedWangTile initialRowTag normalRowTag)
        (t.toTaggedWangTile initialRowTag normalRowTag) := by
      simpa [htile] using hh
    have hcells := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag initialRowTag normalRowTag
      (runHistoryTile M 0 3) t).1 hh'
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
      simp [runTaggedHistoryTile, hrightTail]
      by_cases hstart : M.start = M.halt
      · simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
          Machine.runEmpty_zero, Machine.runEmpty_succ, Machine.nextID,
          Machine.initialID, ID.cellAt, ID.cellAtLeft, hstart] at hcells ⊢
      · rcases hstep : M.step M.start M.blank with ⟨write, q', move⟩
        cases move <;>
          simp [runHistoryTile, Machine.runCell, Machine.runCellLeft,
            Machine.runEmpty_zero, Machine.runEmpty_succ, Machine.nextID,
            Machine.initialID, ID.cellAt, ID.cellAtLeft, hstart, hstep,
            Move.apply] at hcells ⊢
    · subst t
      rw [← htile]
      simp [runTaggedHistoryTile, hrightTail]
  · rcases hnormal with ⟨t, _ht, htile⟩
    have hh' : WangTile.HMatches
        ((runHistoryTile M 0 3).toTaggedWangTile initialRowTag normalRowTag)
        (t.toTaggedWangTile normalRowTag normalRowTag) := by
      simpa [htile] using hh
    have htag := (MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
      initialRowTag normalRowTag normalRowTag normalRowTag
      (runHistoryTile M 0 3) t).1 hh'
    exact False.elim (initialRowTag_ne_normalRowTag htag.1)

theorem seeded_tiling_row_zero_eq {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) :
    ∀ pos : Nat, (x (pos, 0)).1 = runTaggedHistoryTile M 0 pos := by
  intro pos
  cases pos with
  | zero =>
      exact seeded_tiling_row_zero_eq_of_le_three hvalid hseed (by decide : 0 ≤ 3)
  | succ pos =>
      cases pos with
      | zero =>
          exact seeded_tiling_row_zero_eq_of_le_three hvalid hseed (by decide : 1 ≤ 3)
      | succ pos =>
          cases pos with
          | zero =>
              exact seeded_tiling_row_zero_eq_of_le_three hvalid hseed (by decide : 2 ≤ 3)
          | succ pos =>
              cases pos with
              | zero =>
                  exact seeded_tiling_row_zero_eq_of_le_three hvalid hseed (by decide : 3 ≤ 3)
              | succ pos =>
                  induction pos with
                  | zero =>
                      exact seeded_tiling_row_zero_tail_succ_eq hvalid
                        (by decide : 3 ≤ 3)
                        (seeded_tiling_row_zero_eq_of_le_three hvalid hseed
                          (by decide : 3 ≤ 3))
                  | succ pos ih =>
                      exact seeded_tiling_row_zero_tail_succ_eq hvalid
                        (by omega : 3 ≤ pos + 1 + 1 + 1 + 1)
                        ih

theorem seeded_tiling_row_one_prev_cells {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) (pos : Nat) :
    ∃ t : MachineHistoryTile,
      t ∈ machineHistoryTiles M ∧
        t.toTaggedWangTile normalRowTag normalRowTag = (x (pos, 1)).1 ∧
        t.prevLeft = (runHistoryTile M 0 pos).nextLeft ∧
        t.prevCenter = (runHistoryTile M 0 pos).nextCenter ∧
        t.prevRight = (runHistoryTile M 0 pos).nextRight := by
  rcases IsNormalMachineTile.row_one_of_seeded_tiling hvalid hseed pos with
    ⟨t, ht, htilet⟩
  have hbottom := seeded_tiling_row_zero_eq (M := M) (x := x) hvalid hseed pos
  have hv : WangTile.VMatches
      ((runHistoryTile M 0 pos).toTaggedWangTile initialRowTag normalRowTag)
      (t.toTaggedWangTile normalRowTag normalRowTag) := by
    simpa [runTaggedHistoryTile, hbottom, htilet] using hvalid.2 (pos, 0)
  have hcells := (MachineHistoryTile.vMatches_toTaggedWangTile_iff_cells
    initialRowTag normalRowTag normalRowTag normalRowTag
    (runHistoryTile M 0 pos) t).1 hv
  exact ⟨t, ht, htilet, hcells.2.1.symm, hcells.2.2.1.symm,
    hcells.2.2.2.symm⟩

theorem seeded_tiling_row_one_prev_run_cells {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) (pos : Nat) :
    ∃ t : MachineHistoryTile,
      t ∈ machineHistoryTiles M ∧
        t.toTaggedWangTile normalRowTag normalRowTag = (x (pos, 1)).1 ∧
        t.prevLeft = (runHistoryTile M 1 pos).prevLeft ∧
        t.prevCenter = (runHistoryTile M 1 pos).prevCenter ∧
        t.prevRight = (runHistoryTile M 1 pos).prevRight := by
  rcases seeded_tiling_row_one_prev_cells hvalid hseed pos with
    ⟨t, ht, htile, hprevLeft, hprevCenter, hprevRight⟩
  exact ⟨t, ht, htile, by
    simpa [runHistoryTile] using hprevLeft, by
    simpa [runHistoryTile] using hprevCenter, by
    simpa [runHistoryTile] using hprevRight⟩

theorem seeded_tiling_positive_row_prev_run_cells_of_nonhalting_prefix {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (hvalid : ValidQuarterTiling (machineTiles M) x)
    (hseed : (x (0, 0)).1 = machineSeed M) (time : Nat)
    (hprefix : ∀ k : Nat, 1 ≤ k → k ≤ time + 1 →
      (M.runEmpty k).state ≠ M.halt) :
    ∀ pos : Nat,
      ∃ t : MachineHistoryTile,
        t ∈ machineHistoryTiles M ∧
          t.toTaggedWangTile normalRowTag normalRowTag = (x (pos, time + 1)).1 ∧
          t.prevLeft = (runHistoryTile M (time + 1) pos).prevLeft ∧
          t.prevCenter = (runHistoryTile M (time + 1) pos).prevCenter ∧
          t.prevRight = (runHistoryTile M (time + 1) pos).prevRight := by
  induction time with
  | zero =>
      intro pos
      exact seeded_tiling_row_one_prev_run_cells hvalid hseed pos
  | succ time ih =>
      exact seeded_tiling_next_row_prev_run_cells hvalid hseed
        (time := time)
        (ih fun k hk1 hkbound => hprefix k hk1 (by omega))
        (hprefix (time + 1) (by omega) (by omega))
        (hprefix (time + 1 + 1) (by omega) (by omega))

theorem seeded_tiling_false_of_next_halt_from_decoded_row {M : Machine}
    {x : Nat × Nat → TileIn (machineTiles M)}
    (_hvalid : ValidQuarterTiling (machineTiles M) x)
    (_hseed : (x (0, 0)).1 = machineSeed M)
    {time : Nat}
    (hrow : ∀ pos : Nat,
      ∃ t : MachineHistoryTile,
        t ∈ machineHistoryTiles M ∧
          t.toTaggedWangTile normalRowTag normalRowTag = (x (pos, time + 1)).1 ∧
          t.prevLeft = (runHistoryTile M (time + 1) pos).prevLeft ∧
          t.prevCenter = (runHistoryTile M (time + 1) pos).prevCenter ∧
          t.prevRight = (runHistoryTile M (time + 1) pos).prevRight)
    (hstate : (M.runEmpty (time + 1)).state ≠ M.halt)
    (hnextRun : (M.runEmpty (time + 1 + 1)).state = M.halt) :
    False := by
  let c := M.runEmpty (time + 1)
  let pos := (M.step c.state (c.tape c.head)).2.2.apply c.head
  rcases hrow pos with
    ⟨t, ht, _htile, hprevLeft, hprevCenter, hprevRight⟩
  have hstate' : c.state ≠ M.halt := by
    simpa [c] using hstate
  have hnextState : (M.step c.state (c.tape c.head)).2.1 = M.halt := by
    rw [← Machine.nextID_state_of_ne_halt hstate']
    simpa [c, Machine.runEmpty_succ] using hnextRun
  have htlocal := localNextCell?_of_mem_machineHistoryTiles ht
  rw [hprevLeft, hprevCenter, hprevRight] at htlocal
  have hnone := Machine.localNextCell?_at_next_halt_head
    (M := M) (c := c) hstate' hnextState
  have hnoneRun :
      localNextCell? M (runHistoryTile M (time + 1) pos).prevLeft
          (runHistoryTile M (time + 1) pos).prevCenter
          (runHistoryTile M (time + 1) pos).prevRight = none := by
    simpa [runHistoryTile, Machine.runCell, Machine.runCellLeft, c, pos] using hnone
  rw [hnoneRun] at htlocal
  cases htlocal

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

theorem not_tilesQuarterWithSeed_machineTiles_of_halts_at {M : Machine}
    (n : Nat) (hhalt : (M.runEmpty n).state = M.halt) :
    ¬ TilesQuarterWithSeed (machineTiles M) (machineSeed M) := by
  induction n with
  | zero =>
      exact not_tilesQuarterWithSeed_machineTiles_of_initial_halt
        (by simpa [Machine.runEmpty_zero, Machine.initialID] using hhalt)
  | succ n ih =>
      by_cases hprev : (M.runEmpty n).state = M.halt
      · exact ih hprev
      · cases n with
        | zero =>
            exact not_tilesQuarterWithSeed_machineTiles_of_halts_at_one hhalt
        | succ time =>
            rintro ⟨x, hvalid, hseed⟩
            have hprefix : ∀ k : Nat, 1 ≤ k → k ≤ time + 1 →
                (M.runEmpty k).state ≠ M.halt := by
              intro k _hk1 hkbound
              exact Machine.runEmpty_state_ne_halt_of_le
                (M := M) hkbound hprev
            have hrow :=
              seeded_tiling_positive_row_prev_run_cells_of_nonhalting_prefix
                (M := M) (x := x) hvalid hseed time hprefix
            exact seeded_tiling_false_of_next_halt_from_decoded_row
              (M := M) (x := x) hvalid hseed hrow hprev
              (by simpa using hhalt)

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
