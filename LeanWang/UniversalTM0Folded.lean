/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PostMachineInput
import LeanWang.UniversalTM0Semantic

/-!
# Folding the fixed universal TM0 machine onto a one-sided tape

The source machine and both finite supports are constants.  Consequently the
Post table below is constant too; only the finite initial word varies with the
source code.
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Folded

open UniversalTM0Semantic

abbrev SourceSymbol := Turing.TM2to1.Γ' Stack StackSymbol
abbrev SourceLabel := Turing.TM1to0.Λ' tm1

private instance : DecidableEq SourceSymbol := Classical.decEq SourceSymbol
private instance : DecidableEq SourceLabel := Classical.decEq SourceLabel

private def stackVectorEquiv :
    (∀ _ : Stack, Option Turing.PartrecToTM2.Γ') ≃
      Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' ×
        Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' where
  toFun f := (f .main, f .rev, f .aux, f .stack)
  invFun p
    | .main => p.1
    | .rev => p.2.1
    | .aux => p.2.2.1
    | .stack => p.2.2.2
  left_inv f := by funext k; cases k <;> rfl
  right_inv p := by rcases p with ⟨a, b, c, d⟩; rfl

private instance : Primcodable (∀ _ : Stack, Option Turing.PartrecToTM2.Γ') :=
  Primcodable.ofEquiv _ stackVectorEquiv

private instance : Primcodable SourceSymbol :=
  inferInstanceAs
    (Primcodable (Bool × (∀ _ : Stack, Option Turing.PartrecToTM2.Γ')))

def symbols : List SourceSymbol := Finset.univ.toList

theorem mem_symbols (a : SourceSymbol) : a ∈ symbols := by
  simp [symbols]

def labels : List SourceLabel := tm0Support.toList

theorem labels_nodup : labels.Nodup := Finset.nodup_toList _

theorem mem_labels_iff (q : SourceLabel) : q ∈ labels ↔ q ∈ tm0Support := by
  simp [labels]

theorem default_mem_labels : (default : SourceLabel) ∈ labels := by
  rw [mem_labels_iff]
  exact tm0_supports.1

theorem next_mem_labels {q q' : SourceLabel} {a : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol} (hq : q ∈ labels)
    (hstep : tm0 q a = some (q', stmt)) : q' ∈ labels := by
  rw [mem_labels_iff] at hq ⊢
  have hm : (q', stmt) ∈ tm0 q a := by rw [hstep]; simp
  exact tm0_supports.2 hm hq

def symbolCode (a : SourceSymbol) : Nat := Encodable.encode a

theorem symbolCode_injective : Function.Injective symbolCode :=
  Encodable.encode_injective

theorem symbolCode_primrec : Primrec symbolCode := Primrec.encode

def stateCode (q : SourceLabel) : Nat := labels.idxOf q

theorem stateCode_injective_on_labels {q r : SourceLabel}
    (hq : q ∈ labels) (_hr : r ∈ labels) (h : stateCode q = stateCode r) : q = r := by
  exact (List.idxOf_inj hq).1 h

inductive Side where
  | left
  | right
deriving DecidableEq, Repr

def sides : List Side := [.left, .right]

theorem mem_sides (side : Side) : side ∈ sides := by cases side <;> simp [sides]

def sideCode : Side → Nat
  | .left => 0
  | .right => 1

def foldedSymbol (marked : Bool) (left right : SourceSymbol) : Nat :=
  Nat.pair (if marked then 1 else 0)
    (Nat.pair (symbolCode left) (symbolCode right))

theorem foldedSymbol_injective {marked marked' : Bool}
    {left right left' right' : SourceSymbol}
    (h : foldedSymbol marked' left' right' = foldedSymbol marked left right) :
    marked' = marked ∧ left' = left ∧ right' = right := by
  have houter := Nat.pair_eq_pair.mp h
  have hinner := Nat.pair_eq_pair.mp houter.2
  have hmarked : marked' = marked := by
    cases marked' <;> cases marked <;> simp_all
  exact ⟨hmarked, symbolCode_injective hinner.1, symbolCode_injective hinner.2⟩

def foldedSymbols : List Nat :=
  [false, true].flatMap fun marked =>
    symbols.flatMap fun left => symbols.map fun right => foldedSymbol marked left right

theorem foldedSymbol_mem (marked : Bool) (left right : SourceSymbol) :
    foldedSymbol marked left right ∈ foldedSymbols := by
  simp only [foldedSymbols, List.mem_flatMap, List.mem_map]
  exact ⟨marked, by cases marked <;> simp, left, mem_symbols left,
    right, mem_symbols right, rfl⟩

def foldedBlank : Nat := foldedSymbol false default default

def foldedState (side : Side) (q : SourceLabel) : Nat :=
  Nat.pair (sideCode side) (stateCode q)

theorem foldedState_injective_on_labels {side side' : Side} {q r : SourceLabel}
    (hq : q ∈ labels) (hr : r ∈ labels)
    (h : foldedState side q = foldedState side' r) : side = side' ∧ q = r := by
  have hp := Nat.pair_eq_pair.mp h
  have hs : side = side' := by cases side <;> cases side' <;> simp_all [sideCode]
  exact ⟨hs, stateCode_injective_on_labels hq hr hp.2⟩

def foldedStates : List Nat :=
  sides.flatMap fun side => labels.map fun q => foldedState side q

theorem foldedState_mem (side : Side) {q : SourceLabel} (hq : q ∈ labels) :
    foldedState side q ∈ foldedStates := by
  simp only [foldedStates, List.mem_flatMap, List.mem_map]
  exact ⟨side, mem_sides side, q, hq, rfl⟩

def read : Side → SourceSymbol → SourceSymbol → SourceSymbol
  | .left, left, _ => left
  | .right, _, right => right

def writeCell (side : Side) (marked : Bool) (new left right : SourceSymbol) : Nat :=
  match side with
  | .left => foldedSymbol marked new right
  | .right => foldedSymbol marked left new

def nextSide (side : Side) (marked : Bool) (dir : Turing.Dir) : Side :=
  match side, marked, dir with
  | .right, true, .left => .left
  | .left, true, .right => .right
  | side, _, _ => side

def moveStmt (side : Side) (marked : Bool) (cell : Nat)
    (dir : Turing.Dir) : PostStmt :=
  match side, marked, dir with
  | .right, true, .left => .write cell
  | .left, true, .right => .write cell
  | .right, _, .right => .move .right
  | .right, _, .left => .move .left
  | .left, _, .left => .move .right
  | .left, _, .right => .move .left

def rowOfStep (q q' : SourceLabel) (side : Side) (marked : Bool)
    (left right : SourceSymbol) (stmt : Turing.TM0.Stmt SourceSymbol) :
    PostTransition :=
  let cell := foldedSymbol marked left right
  match stmt with
  | .write new =>
      { state := foldedState side q
        read := cell
        next := foldedState side q'
        stmt := .write (writeCell side marked new left right) }
  | .move dir =>
      { state := foldedState side q
        read := cell
        next := foldedState (nextSide side marked dir) q'
        stmt := moveStmt side marked cell dir }

def row? (q : SourceLabel) (side : Side) (marked : Bool)
    (left right : SourceSymbol) : Option PostTransition :=
  (tm0 q (read side left right)).map fun (q', stmt) =>
    rowOfStep q q' side marked left right stmt

def rowsFor (q : SourceLabel) : List PostTransition :=
  sides.flatMap fun side =>
    [false, true].flatMap fun marked =>
      symbols.flatMap fun left => symbols.filterMap fun right =>
        row? q side marked left right

def rows : List PostTransition := labels.flatMap rowsFor

def program : PostProgram where
  symbols := foldedSymbols
  states := foldedStates
  blank := foldedBlank
  start := foldedState .right default
  table := rows

theorem rowOfStep_matches (q q' : SourceLabel) (side : Side) (marked : Bool)
    (left right : SourceSymbol) (stmt : Turing.TM0.Stmt SourceSymbol) :
    (rowOfStep q q' side marked left right stmt).matchesInput
      (foldedState side q) (foldedSymbol marked left right) = true := by
  cases stmt <;> simp [rowOfStep, PostTransition.matchesInput]

theorem rowsFor_state {q : SourceLabel} {row : PostTransition}
    (hrow : row ∈ rowsFor q) : ∃ side, row.state = foldedState side q := by
  simp only [rowsFor, List.mem_flatMap, List.mem_filterMap] at hrow
  rcases hrow with ⟨side, _, marked, _, left, _, right, _, hrow⟩
  simp only [row?, Option.map_eq_some_iff] at hrow
  rcases hrow with ⟨⟨q', stmt⟩, _, rfl⟩
  exact ⟨side, by cases stmt <;> rfl⟩

theorem rowsFor_find?_eq_none_of_label_ne {q r : SourceLabel}
    (hq : q ∈ labels) (hr : r ∈ labels) (hne : r ≠ q)
    (side : Side) (marked : Bool) (left right : SourceSymbol) :
    (rowsFor r).find? (fun row => row.matchesInput
      (foldedState side q) (foldedSymbol marked left right)) = none := by
  rw [List.find?_eq_none]
  intro row hrow
  rcases rowsFor_state hrow with ⟨side', hstate⟩
  intro hmatch
  unfold PostTransition.matchesInput at hmatch
  simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
  rw [hstate] at hmatch
  exact hne (foldedState_injective_on_labels hr hq hmatch.1).2

end UniversalTM0Folded
end LeanWang
