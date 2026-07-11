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

abbrev Input := (Side × Bool) × (SourceSymbol × SourceSymbol)

def inputs : List Input :=
  (sides ×ˢ [false, true]) ×ˢ (symbols ×ˢ symbols)

theorem inputs_nodup : inputs.Nodup := by
  exact (List.Nodup.product (by simp [sides]) (by simp)).product
    (List.Nodup.product (Finset.nodup_toList _) (Finset.nodup_toList _))

theorem mem_inputs (side : Side) (marked : Bool) (left right : SourceSymbol) :
    ((side, marked), (left, right)) ∈ inputs := by
  simp [inputs, mem_sides, mem_symbols]

def rowForInput (q : SourceLabel) (input : Input) : Option PostTransition :=
  row? q input.1.1 input.1.2 input.2.1 input.2.2

def rowsFor (q : SourceLabel) : List PostTransition :=
  inputs.filterMap (rowForInput q)

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
  simp only [rowsFor, List.mem_filterMap] at hrow
  rcases hrow with ⟨⟨⟨side, marked⟩, ⟨left, right⟩⟩, _, hrow⟩
  simp only [rowForInput, row?, Option.map_eq_some_iff] at hrow
  rcases hrow with ⟨⟨q', stmt⟩, _, rfl⟩
  exact ⟨side, by cases stmt <;> rfl⟩

theorem rowOfStep_mem_rowsFor {q q' : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep : tm0 q (read side left right) = some (q', stmt)) :
    rowOfStep q q' side marked left right stmt ∈ rowsFor q := by
  rw [rowsFor, List.mem_filterMap]
  refine ⟨((side, marked), (left, right)), mem_inputs side marked left right, ?_⟩
  simp [rowForInput, row?, hstep]

def inputState (q : SourceLabel) (input : Input) : Nat :=
  foldedState input.1.1 q

def inputSymbol (input : Input) : Nat :=
  foldedSymbol input.1.2 input.2.1 input.2.2

theorem inputKey_injective (q : SourceLabel) :
    Function.Injective fun input : Input => (inputState q input, inputSymbol input) := by
  rintro ⟨⟨side, marked⟩, ⟨left, right⟩⟩
    ⟨⟨side', marked'⟩, ⟨left', right'⟩⟩ h
  have hstate := congrArg Prod.fst h
  have hsymbol := congrArg Prod.snd h
  have hsides : side = side' := by
    have hp := Nat.pair_eq_pair.mp hstate
    cases side <;> cases side' <;> simp_all [inputState, foldedState, sideCode]
  have hsymbols := foldedSymbol_injective hsymbol.symm
  rcases hsymbols with ⟨rfl, rfl, rfl⟩
  subst side'
  rfl

theorem rowForInput_key {q : SourceLabel} {input : Input} {row : PostTransition}
    (hrow : rowForInput q input = some row) :
    (row.state, row.read) = (inputState q input, inputSymbol input) := by
  rcases input with ⟨⟨side, marked⟩, ⟨left, right⟩⟩
  simp only [rowForInput, row?, Option.map_eq_some_iff] at hrow
  rcases hrow with ⟨⟨q', stmt⟩, _, rfl⟩
  cases stmt <;> rfl

private theorem find?_filterMap_rowForInput
    (q : SourceLabel) (target : Input) (targetRow : PostTransition)
    (hrow : rowForInput q target = some targetRow) :
    ∀ xs : List Input, xs.Nodup → target ∈ xs →
      (xs.filterMap (rowForInput q)).find? (fun row =>
        row.matchesInput (inputState q target) (inputSymbol target)) = some targetRow
  | [], _, hmem => by simp at hmem
  | input :: xs, hnodup, hmem => by
      simp only [List.nodup_cons] at hnodup
      by_cases htarget : input = target
      · subst input
        rw [List.filterMap_cons_some hrow, List.find?_cons]
        have hmatch : targetRow.matchesInput
            (inputState q target) (inputSymbol target) = true := by
          unfold PostTransition.matchesInput
          have hkey := rowForInput_key hrow
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
          exact ⟨congrArg Prod.fst hkey, congrArg Prod.snd hkey⟩
        rw [hmatch]
      · have htargetMem : target ∈ xs := by
          simp only [List.mem_cons] at hmem
          exact hmem.resolve_left (Ne.symm htarget)
        cases hinput : rowForInput q input with
        | none =>
            simp only [List.filterMap_cons_none hinput]
            exact find?_filterMap_rowForInput q target targetRow hrow xs
              hnodup.2 htargetMem
        | some row =>
            have hkeyNe : (row.state, row.read) ≠
                (inputState q target, inputSymbol target) := by
              intro hkey
              apply htarget
              apply inputKey_injective q
              change (inputState q input, inputSymbol input) =
                (inputState q target, inputSymbol target)
              exact (rowForInput_key hinput).symm.trans hkey
            have hmatch : row.matchesInput
                (inputState q target) (inputSymbol target) = false := by
              unfold PostTransition.matchesInput
              by_cases hs : row.state = inputState q target
              · have hr : row.read ≠ inputSymbol target := fun hr => hkeyNe (by simp [hs, hr])
                simp [hs, hr]
              · simp [hs]
            simp only [List.filterMap_cons_some hinput, List.find?_cons, hmatch]
            exact find?_filterMap_rowForInput q target targetRow hrow xs
              hnodup.2 htargetMem

theorem rowsFor_find?_of_step {q q' : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep : tm0 q (read side left right) = some (q', stmt)) :
    (rowsFor q).find? (fun row => row.matchesInput
      (foldedState side q) (foldedSymbol marked left right)) =
      some (rowOfStep q q' side marked left right stmt) := by
  let target : Input := ((side, marked), (left, right))
  have hrow : rowForInput q target =
      some (rowOfStep q q' side marked left right stmt) := by
    simp [target, rowForInput, row?, hstep]
  exact find?_filterMap_rowForInput q target
    (rowOfStep q q' side marked left right stmt) hrow inputs inputs_nodup
      (mem_inputs side marked left right)

theorem rowsFor_find?_of_no_step {q : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol}
    (hstep : tm0 q (read side left right) = none) :
    (rowsFor q).find? (fun row => row.matchesInput
      (foldedState side q) (foldedSymbol marked left right)) = none := by
  rw [List.find?_eq_none]
  intro row hrow hmatch
  unfold PostTransition.matchesInput at hmatch
  simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
  simp only [rowsFor, List.mem_filterMap] at hrow
  rcases hrow with ⟨⟨⟨side', marked'⟩, ⟨left', right'⟩⟩, _, hrow⟩
  simp only [rowForInput, row?, Option.map_eq_some_iff] at hrow
  rcases hrow with ⟨⟨r, sourceStmt⟩, hsource, rfl⟩
  have hside : side' = side := by
    have hp : sideCode side' = sideCode side := by
      cases sourceStmt <;> exact (Nat.pair_eq_pair.mp hmatch.1).1
    cases side' <;> cases side <;> simp_all [sideCode]
  have hcell : foldedSymbol marked' left' right' =
      foldedSymbol marked left right := by
    cases sourceStmt <;> exact hmatch.2
  rcases foldedSymbol_injective hcell with ⟨rfl, rfl, rfl⟩
  subst side'
  rw [hstep] at hsource
  contradiction

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

private theorem find?_append_of_some {α : Type} (xs ys : List α)
    (p : α → Bool) {a : α} (h : xs.find? p = some a) :
    (xs ++ ys).find? p = some a := by simp [h]

private theorem find?_append_of_none {α : Type} (xs ys : List α)
    (p : α → Bool) (h : xs.find? p = none) :
    (xs ++ ys).find? p = ys.find? p := by simp [h]

private theorem rows_find?_of_step_aux {q q' : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (qs : List SourceLabel) (hqs : ∀ r ∈ qs, r ∈ labels) (hq : q ∈ qs)
    (hstep : tm0 q (read side left right) = some (q', stmt)) :
    (qs.flatMap rowsFor).find? (fun row => row.matchesInput
      (foldedState side q) (foldedSymbol marked left right)) =
      some (rowOfStep q q' side marked left right stmt) := by
  induction qs with
  | nil => contradiction
  | cons r qs ih =>
      simp only [List.mem_cons] at hq
      by_cases hrq : r = q
      · subst r
        exact find?_append_of_some _ _ _ (rowsFor_find?_of_step hstep)
      · have hqtail : q ∈ qs := hq.resolve_left (Ne.symm hrq)
        have hnone := rowsFor_find?_eq_none_of_label_ne
          (hqs q (by simp [hqtail])) (hqs r (by simp)) hrq
          side marked left right
        rw [List.flatMap_cons, find?_append_of_none _ _ _ hnone]
        exact ih (fun s hs => hqs s (by simp [hs])) hqtail

theorem rows_find?_of_step {q q' : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hq : q ∈ labels)
    (hstep : tm0 q (read side left right) = some (q', stmt)) :
    rows.find? (fun row => row.matchesInput
      (foldedState side q) (foldedSymbol marked left right)) =
      some (rowOfStep q q' side marked left right stmt) := by
  exact rows_find?_of_step_aux labels (fun _ h => h) hq hstep

private theorem rows_find?_of_no_step_aux {q : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol}
    (qs : List SourceLabel) (hqs : ∀ r ∈ qs, r ∈ labels) (hq : q ∈ labels)
    (hstep : tm0 q (read side left right) = none) :
    (qs.flatMap rowsFor).find? (fun row => row.matchesInput
      (foldedState side q) (foldedSymbol marked left right)) = none := by
  induction qs with
  | nil => simp
  | cons r qs ih =>
      by_cases hrq : r = q
      · subst r
        rw [List.flatMap_cons, find?_append_of_none _ _ _
          (rowsFor_find?_of_no_step hstep)]
        exact ih (fun s hs => hqs s (by simp [hs]))
      · have hnone := rowsFor_find?_eq_none_of_label_ne
          hq (hqs r (by simp)) hrq side marked left right
        rw [List.flatMap_cons, find?_append_of_none _ _ _ hnone]
        exact ih (fun s hs => hqs s (by simp [hs]))

theorem rows_find?_of_no_step {q : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol} (hq : q ∈ labels)
    (hstep : tm0 q (read side left right) = none) :
    rows.find? (fun row => row.matchesInput
      (foldedState side q) (foldedSymbol marked left right)) = none := by
  exact rows_find?_of_no_step_aux labels (fun _ h => h) hq hstep

theorem transition?_of_step {q q' : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hq : q ∈ labels)
    (hstep : tm0 q (read side left right) = some (q', stmt)) :
    program.transition? (foldedState side q) (foldedSymbol marked left right) =
      some (rowOfStep q q' side marked left right stmt) := by
  exact rows_find?_of_step hq hstep

theorem transition?_of_no_step {q : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol} (hq : q ∈ labels)
    (hstep : tm0 q (read side left right) = none) :
    program.transition? (foldedState side q) (foldedSymbol marked left right) = none := by
  exact rows_find?_of_no_step hq hstep

theorem rowOfStep_next_mem {q q' : SourceLabel} {side : Side} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hq' : q' ∈ labels) :
    (rowOfStep q q' side marked left right stmt).next ∈ foldedStates := by
  cases stmt with
  | write => exact foldedState_mem side hq'
  | move dir => exact foldedState_mem (nextSide side marked dir) hq'

theorem rowOfStep_write_mem {q q' : SourceLabel} {side : Side} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol} :
    match (rowOfStep q q' side marked left right stmt).stmt with
    | .move _ => True
    | .write symbol => symbol ∈ foldedSymbols := by
  cases stmt with
  | write new => cases side <;> exact foldedSymbol_mem marked _ _
  | move dir =>
      cases side <;> cases marked <;> cases dir <;>
        simp [rowOfStep, moveStmt, foldedSymbol_mem]

theorem step_of_source_step {q q' : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hq : q ∈ labels)
    (hstep : tm0 q (read side left right) = some (q', stmt)) :
    program.step (foldedState side q) (foldedSymbol marked left right) =
      some ((rowOfStep q q' side marked left right stmt).next,
        (rowOfStep q q' side marked left right stmt).stmt) := by
  apply PostProgram.step_of_transition?_eq_some (transition?_of_step hq hstep)
  · exact rowOfStep_next_mem (next_mem_labels hq hstep)
  · exact rowOfStep_write_mem

theorem step_of_no_source_step {q : SourceLabel} {side : Side}
    {marked : Bool} {left right : SourceSymbol} (hq : q ∈ labels)
    (hstep : tm0 q (read side left right) = none) :
    program.step (foldedState side q) (foldedSymbol marked left right) = none := by
  exact PostProgram.step_eq_none_of_transition?_eq_none
    (transition?_of_no_step hq hstep)

end UniversalTM0Folded
end LeanWang
