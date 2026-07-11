/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.MachineInput
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

theorem foldedSymbol_primrec :
    Primrec (fun p : Bool × SourceSymbol × SourceSymbol =>
      foldedSymbol p.1 p.2.1 p.2.2) := by
  exact Primrec.dom_finite _

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

def rightAbs (i : Nat) : Int := i

def leftAbs (i : Nat) : Int := -((i : Int) + 1)

def activeAbs : Side → Nat → Int
  | .right, head => rightAbs head
  | .left, head => leftAbs head

def sourceOffset (side : Side) (head : Nat) (absolute : Int) : Int :=
  absolute - activeAbs side head

def foldedCellOfTapeAt (tape : Turing.Tape SourceSymbol)
    (side : Side) (head position : Nat) : Nat :=
  foldedSymbol (decide (position = 0))
    (tape.nth (sourceOffset side head (leftAbs position)))
    (tape.nth (sourceOffset side head (rightAbs position)))

def FoldedTapeRel (tape : Turing.Tape SourceSymbol)
    (side : Side) (head : Nat) (foldedTape : Nat → Nat) : Prop :=
  ∀ position, foldedTape position = foldedCellOfTapeAt tape side head position

def FoldedConfigRel (cfg : Turing.TM0.Cfg SourceSymbol SourceLabel)
    (id : PostID) : Prop :=
  ∃ side : Side, cfg.q ∈ labels ∧
    id.state = some (foldedState side cfg.q) ∧
    FoldedTapeRel cfg.Tape side id.head id.tape

@[simp] theorem sourceOffset_right_head (head : Nat) :
    sourceOffset .right head (rightAbs head) = 0 := by
  simp [sourceOffset, activeAbs, rightAbs]

@[simp] theorem sourceOffset_left_head (head : Nat) :
    sourceOffset .left head (leftAbs head) = 0 := by
  simp [sourceOffset, activeAbs, leftAbs]

theorem read_active_cell (tape : Turing.Tape SourceSymbol)
    (side : Side) (head : Nat) :
    read side
      (tape.nth (sourceOffset side head (leftAbs head)))
      (tape.nth (sourceOffset side head (rightAbs head))) = tape.head := by
  cases side <;> simp [read, Turing.Tape.nth_zero]

theorem sourceOffset_right_left_head_ne_zero (head : Nat) :
    sourceOffset .right head (leftAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

theorem sourceOffset_left_right_head_ne_zero (head : Nat) :
    sourceOffset .left head (rightAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

theorem foldedCellOfTapeAt_write_active (tape : Turing.Tape SourceSymbol)
    (side : Side) (head : Nat) (new : SourceSymbol) :
    foldedCellOfTapeAt (tape.write new) side head head =
      writeCell side (decide (head = 0)) new
        (tape.nth (sourceOffset side head (leftAbs head)))
        (tape.nth (sourceOffset side head (rightAbs head))) := by
  cases side <;> by_cases h : head = 0
  all_goals
    simp [foldedCellOfTapeAt, writeCell, sourceOffset_right_left_head_ne_zero,
      sourceOffset_left_right_head_ne_zero, h]
  all_goals rfl

theorem sourceOffset_left_ne_zero_of_ne_head
    (side : Side) {head position : Nat} (h : position ≠ head) :
    sourceOffset side head (leftAbs position) ≠ 0 := by
  cases side <;> simp [sourceOffset, activeAbs, leftAbs, rightAbs] <;> omega

theorem sourceOffset_right_ne_zero_of_ne_head
    (side : Side) {head position : Nat} (h : position ≠ head) :
    sourceOffset side head (rightAbs position) ≠ 0 := by
  cases side <;> simp [sourceOffset, activeAbs, leftAbs, rightAbs] <;> omega

theorem foldedCellOfTapeAt_write_inactive (tape : Turing.Tape SourceSymbol)
    (side : Side) {head position : Nat} (new : SourceSymbol) (h : position ≠ head) :
    foldedCellOfTapeAt (tape.write new) side head position =
      foldedCellOfTapeAt tape side head position := by
  simp [foldedCellOfTapeAt, sourceOffset_left_ne_zero_of_ne_head side h,
    sourceOffset_right_ne_zero_of_ne_head side h]

theorem FoldedTapeRel_write {tape : Turing.Tape SourceSymbol} {side : Side}
    {head : Nat} {foldedTape : Nat → Nat} (new : SourceSymbol)
    (hrel : FoldedTapeRel tape side head foldedTape) :
    FoldedTapeRel (tape.write new) side head
      (Function.update foldedTape head
        (writeCell side (decide (head = 0)) new
          (tape.nth (sourceOffset side head (leftAbs head)))
          (tape.nth (sourceOffset side head (rightAbs head))))) := by
  intro position
  by_cases h : position = head
  · subst position
    simp [foldedCellOfTapeAt_write_active]
  · rw [Function.update_of_ne h, hrel position]
    exact (foldedCellOfTapeAt_write_inactive tape side new h).symm

def moveHead (side : Side) (marked : Bool) (head : Nat) (dir : Turing.Dir) : Nat :=
  match side, marked, dir with
  | .right, true, .left => head
  | .left, true, .right => head
  | .right, _, .right => head + 1
  | .right, _, .left => head.pred
  | .left, _, .left => head + 1
  | .left, _, .right => head.pred

theorem activeAbs_moveHead (side : Side) (head : Nat) (dir : Turing.Dir) :
    activeAbs (nextSide side (decide (head = 0)) dir)
        (moveHead side (decide (head = 0)) head dir) =
      activeAbs side head + match dir with
      | .left => -1
      | .right => 1 := by
  cases side <;> cases dir <;> by_cases h : head = 0
  all_goals subst_vars
  all_goals simp_all [nextSide, moveHead, activeAbs, leftAbs, rightAbs]
  all_goals try omega

theorem sourceOffset_moveHead (side : Side) (head : Nat) (dir : Turing.Dir)
    (absolute : Int) :
    sourceOffset (nextSide side (decide (head = 0)) dir)
        (moveHead side (decide (head = 0)) head dir) absolute =
      sourceOffset side head absolute - match dir with
      | .left => -1
      | .right => 1 := by
  unfold sourceOffset
  rw [activeAbs_moveHead]
  cases dir <;> omega

theorem foldedCellOfTapeAt_move (tape : Turing.Tape SourceSymbol)
    (side : Side) (head position : Nat) (dir : Turing.Dir) :
    foldedCellOfTapeAt (tape.move dir)
        (nextSide side (decide (head = 0)) dir)
        (moveHead side (decide (head = 0)) head dir) position =
      foldedCellOfTapeAt tape side head position := by
  cases dir <;> simp [foldedCellOfTapeAt, sourceOffset_moveHead]

theorem FoldedTapeRel_move {tape : Turing.Tape SourceSymbol} {side : Side}
    {head : Nat} {foldedTape : Nat → Nat} (dir : Turing.Dir)
    (hrel : FoldedTapeRel tape side head foldedTape) :
    FoldedTapeRel (tape.move dir)
      (nextSide side (decide (head = 0)) dir)
      (moveHead side (decide (head = 0)) head dir) foldedTape := by
  intro position
  rw [hrel position, foldedCellOfTapeAt_move]

theorem nextID_write {q q' : SourceLabel} {side : Side} {marked : Bool}
    {left right new : SourceSymbol} {id : PostID}
    (hstate : id.state = some (foldedState side q))
    (hcell : id.tape id.head = foldedSymbol marked left right)
    (hq : q ∈ labels)
    (hstep : tm0 q (read side left right) = some (q', Turing.TM0.Stmt.write new)) :
    program.nextID id =
      { tape := Function.update id.tape id.head (writeCell side marked new left right)
        head := id.head
        state := some (foldedState side q') } := by
  rw [PostProgram.nextID_of_running hstate, hcell]
  rw [step_of_source_step hq hstep]
  rfl

theorem nextID_move {q q' : SourceLabel} {side : Side} {marked : Bool}
    {left right : SourceSymbol} {dir : Turing.Dir} {id : PostID}
    (hstate : id.state = some (foldedState side q))
    (hcell : id.tape id.head = foldedSymbol marked left right)
    (hq : q ∈ labels)
    (hstep : tm0 q (read side left right) = some (q', Turing.TM0.Stmt.move dir)) :
    program.nextID id =
      { tape := id.tape
        head := moveHead side marked id.head dir
        state := some (foldedState (nextSide side marked dir) q') } := by
  rw [PostProgram.nextID_of_running hstate, hcell]
  rw [step_of_source_step hq hstep]
  cases side <;> cases marked <;> cases dir <;>
    simp [rowOfStep, moveStmt, moveHead, nextSide, PostProgram.applyStmt,
      Move.apply, hcell]

theorem nextID_halt {q : SourceLabel} {side : Side} {marked : Bool}
    {left right : SourceSymbol} {id : PostID}
    (hstate : id.state = some (foldedState side q))
    (hcell : id.tape id.head = foldedSymbol marked left right)
    (hq : q ∈ labels) (hstep : tm0 q (read side left right) = none) :
    (program.nextID id).state = none := by
  rw [PostProgram.nextID_of_running hstate, hcell]
  rw [step_of_no_source_step hq hstep]

theorem FoldedConfigRel_write_step
    {cfg : Turing.TM0.Cfg SourceSymbol SourceLabel} {id : PostID}
    {q' : SourceLabel} {new : SourceSymbol} (hrel : FoldedConfigRel cfg id)
    (hstep : tm0 cfg.q cfg.Tape.head = some (q', Turing.TM0.Stmt.write new)) :
    FoldedConfigRel { q := q', Tape := cfg.Tape.write new } (program.nextID id) := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  have hread : read side left right = cfg.Tape.head := by
    exact read_active_cell cfg.Tape side id.head
  have hstep' : tm0 cfg.q (read side left right) =
      some (q', Turing.TM0.Stmt.write new) := by simpa [hread] using hstep
  have hcell : id.tape id.head =
      foldedSymbol (decide (id.head = 0)) left right := by
    rw [htape id.head]
    rfl
  rw [nextID_write hstate hcell hq hstep']
  exact ⟨side, next_mem_labels hq hstep, rfl, FoldedTapeRel_write new htape⟩

theorem FoldedConfigRel_move_step
    {cfg : Turing.TM0.Cfg SourceSymbol SourceLabel} {id : PostID}
    {q' : SourceLabel} {dir : Turing.Dir} (hrel : FoldedConfigRel cfg id)
    (hstep : tm0 cfg.q cfg.Tape.head = some (q', Turing.TM0.Stmt.move dir)) :
    FoldedConfigRel { q := q', Tape := cfg.Tape.move dir } (program.nextID id) := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let marked := decide (id.head = 0)
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  have hread : read side left right = cfg.Tape.head :=
    read_active_cell cfg.Tape side id.head
  have hstep' : tm0 cfg.q (read side left right) =
      some (q', Turing.TM0.Stmt.move dir) := by simpa [hread] using hstep
  have hcell : id.tape id.head = foldedSymbol marked left right := by
    rw [htape id.head]
    rfl
  rw [nextID_move hstate hcell hq hstep']
  exact ⟨nextSide side marked dir, next_mem_labels hq hstep, rfl,
    FoldedTapeRel_move dir htape⟩

theorem FoldedConfigRel_step
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol SourceLabel} {id : PostID}
    (hrel : FoldedConfigRel cfg id) (hstep : Turing.TM0.step tm0 cfg = some cfg') :
    FoldedConfigRel cfg' (program.nextID id) := by
  cases hm : tm0 cfg.q cfg.Tape.head with
  | none => simp [Turing.TM0.step, hm] at hstep
  | some next =>
      rcases next with ⟨q', stmt⟩
      cases stmt with
      | write new =>
          have hcfg : cfg' = { q := q', Tape := cfg.Tape.write new } := by
            simpa [Turing.TM0.step, hm] using hstep.symm
          subst cfg'
          exact FoldedConfigRel_write_step hrel hm
      | move dir =>
          have hcfg : cfg' = { q := q', Tape := cfg.Tape.move dir } := by
            simpa [Turing.TM0.step, hm] using hstep.symm
          subst cfg'
          exact FoldedConfigRel_move_step hrel hm

theorem FoldedConfigRel_halt_step
    {cfg : Turing.TM0.Cfg SourceSymbol SourceLabel} {id : PostID}
    (hrel : FoldedConfigRel cfg id) (hstep : Turing.TM0.step tm0 cfg = none) :
    (program.nextID id).state = none := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let marked := decide (id.head = 0)
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  have hread : read side left right = cfg.Tape.head :=
    read_active_cell cfg.Tape side id.head
  have hm : tm0 cfg.q cfg.Tape.head = none := by
    cases hm : tm0 cfg.q cfg.Tape.head with
    | none => rfl
    | some next => simp [Turing.TM0.step, hm] at hstep
  have hm' : tm0 cfg.q (read side left right) = none := by simpa [hread] using hm
  have hcell : id.tape id.head = foldedSymbol marked left right := by
    rw [htape id.head]
    rfl
  exact nextID_halt hstate hcell hq hm'

theorem FoldedConfigRel_reaches
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol SourceLabel} {id : PostID}
    (hrel : FoldedConfigRel cfg id)
    (hreach : StateTransition.Reaches (Turing.TM0.step tm0) cfg cfg') :
    ∃ steps, FoldedConfigRel cfg' (Nat.iterate program.nextID steps id) := by
  induction hreach with
  | refl => exact ⟨0, hrel⟩
  | tail _ hstep ih =>
      rcases ih with ⟨steps, hrel'⟩
      refine ⟨steps + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      exact FoldedConfigRel_step hrel' (by simpa using hstep)

theorem FoldedConfigRel_reaches_halt
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol SourceLabel} {id : PostID}
    (hrel : FoldedConfigRel cfg id)
    (hreach : StateTransition.Reaches (Turing.TM0.step tm0) cfg cfg')
    (hhalt : Turing.TM0.step tm0 cfg' = none) :
    ∃ steps, (Nat.iterate program.nextID steps id).state = none := by
  rcases FoldedConfigRel_reaches hrel hreach with ⟨steps, hrel'⟩
  refine ⟨steps + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact FoldedConfigRel_halt_step hrel' hhalt

theorem tm0_reaches_halt_of_post_halts
    {cfg : Turing.TM0.Cfg SourceSymbol SourceLabel} {id : PostID}
    (hrel : FoldedConfigRel cfg id) : ∀ steps,
    (Nat.iterate program.nextID steps id).state = none →
      ∃ cfg', StateTransition.Reaches (Turing.TM0.step tm0) cfg cfg' ∧
        Turing.TM0.step tm0 cfg' = none
  | 0, hhalt => by
      rcases hrel with ⟨side, _hq, hstate, _htape⟩
      simp [hstate] at hhalt
  | steps + 1, hhalt => by
      cases hstep : Turing.TM0.step tm0 cfg with
      | none => exact ⟨cfg, Relation.ReflTransGen.refl, hstep⟩
      | some cfg' =>
          have hrel' := FoldedConfigRel_step hrel hstep
          have hhalt' :
              (Nat.iterate program.nextID steps (program.nextID id)).state = none := by
            simpa [Function.iterate_succ_apply] using hhalt
          rcases tm0_reaches_halt_of_post_halts hrel' steps hhalt' with
            ⟨terminal, hreach, hterminal⟩
          exact ⟨terminal, Relation.ReflTransGen.head (by simpa using hstep) hreach,
            hterminal⟩

def inputWord : List SourceSymbol → List Nat
  | [] => []
  | first :: rest =>
      foldedSymbol true default first ::
        rest.map (foldedSymbol false default)

private theorem foldedOrigin_primrec :
    Primrec (fun source : SourceSymbol => foldedSymbol true default source) := by
  unfold foldedSymbol
  exact Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp (Primrec.const (symbolCode default)) symbolCode_primrec)

private theorem foldedRight_primrec :
    Primrec (fun source : SourceSymbol => foldedSymbol false default source) := by
  unfold foldedSymbol
  exact Primrec₂.natPair.comp (Primrec.const 0)
    (Primrec₂.natPair.comp (Primrec.const (symbolCode default)) symbolCode_primrec)

theorem inputWord_primrec : Primrec inputWord := by
  have hrest : Primrec (fun rest : List SourceSymbol =>
      rest.map (foldedSymbol false default)) := by
    refine Primrec.list_map Primrec.id ?_
    apply Primrec₂.mk
    exact foldedRight_primrec.comp Primrec.snd
  have hcons : Primrec₂ (fun (_ : List SourceSymbol) =>
      fun p : SourceSymbol × List SourceSymbol =>
        foldedSymbol true default p.1 ::
          p.2.map (foldedSymbol false default)) := by
    apply Primrec₂.mk
    exact Primrec.list_cons.comp
      (foldedOrigin_primrec.comp (Primrec.fst.comp Primrec.snd))
      (hrest.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_casesOn Primrec.id (Primrec.const []) hcons).of_eq
    fun input => by cases input <;> rfl

theorem inputWord_computable : Computable inputWord := inputWord_primrec.to_comp

def initialPostID (input : List SourceSymbol) : PostID where
  tape := MachineInput.tape foldedBlank (inputWord input)
  head := 0
  state := some (foldedState .right default)

private def inputAt (input : List SourceSymbol) (position : Nat) : SourceSymbol :=
  input.getI position

theorem foldedCellOfTapeAt_init (input : List SourceSymbol) (position : Nat) :
    foldedCellOfTapeAt (Turing.TM0.init (Λ := SourceLabel) input).Tape .right 0 position =
      if position = 0 then foldedSymbol true default (inputAt input 0)
      else foldedSymbol false default (inputAt input position) := by
  cases position with
  | zero =>
      have hleft : sourceOffset .right 0 (leftAbs 0) = Int.negSucc 0 := by
        simp [sourceOffset, activeAbs, leftAbs, rightAbs]
      have hright : sourceOffset .right 0 (rightAbs 0) = 0 := by
        simp [sourceOffset, activeAbs, rightAbs]
      rw [foldedCellOfTapeAt, hleft, hright]
      have hget : input.headI = input.getI 0 := (List.getI_zero_eq_headI (l := input)).symm
      simp [inputAt, Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂,
        Turing.Tape.mk', Turing.Tape.nth, hget]
  | succ position =>
      have hleft : sourceOffset .right 0 (leftAbs (position + 1)) =
          Int.negSucc (position + 1) := by
        simp [sourceOffset, activeAbs, leftAbs, rightAbs]
        omega
      have hright : sourceOffset .right 0 (rightAbs (position + 1)) =
          Int.ofNat (position + 1) := by
        simp [sourceOffset, activeAbs, rightAbs]
      rw [foldedCellOfTapeAt, hleft, hright]
      have hget : input.tail.getI position = input.getI (position + 1) := by
        cases input <;> rfl
      simp [inputAt, Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂,
        Turing.Tape.mk', Turing.Tape.nth, hget]

theorem inputWord_tape_eq_foldedCell {input : List SourceSymbol}
    (hinput : input ≠ []) (position : Nat) :
    MachineInput.tape foldedBlank (inputWord input) position =
      foldedCellOfTapeAt (Turing.TM0.init (Λ := SourceLabel) input).Tape .right 0 position := by
  rw [foldedCellOfTapeAt_init]
  cases input with
  | nil => contradiction
  | cons first rest =>
      cases position with
      | zero => simp [MachineInput.tape, inputWord, inputAt]
      | succ position =>
          by_cases hposition : position < rest.length
          · simp [MachineInput.tape, inputWord, inputAt, hposition,
              List.getI_eq_getElem rest hposition]
          · have hdefault : rest.getI position = default :=
              List.getI_eq_default (l := rest) (by omega)
            simp [MachineInput.tape, inputWord, inputAt, hposition, foldedBlank, hdefault]

theorem FoldedConfigRel_initial {input : List SourceSymbol} (hinput : input ≠ []) :
    FoldedConfigRel (Turing.TM0.init (Λ := SourceLabel) input) (initialPostID input) := by
  refine ⟨.right, ?_, rfl, ?_⟩
  · exact default_mem_labels
  · intro position
    exact inputWord_tape_eq_foldedCell hinput position

theorem inputWord_symbol_mem {input : List SourceSymbol} {symbol : Nat}
    (hmem : symbol ∈ inputWord input) : symbol ∈ foldedSymbols := by
  cases input with
  | nil => simp [inputWord] at hmem
  | cons first rest =>
      simp only [inputWord, List.mem_cons, List.mem_map] at hmem
      rcases hmem with rfl | ⟨source, _, rfl⟩
      · exact foldedSymbol_mem true default first
      · exact foldedSymbol_mem false default source

theorem initialPostID_tapeSupported (input : List SourceSymbol) :
    PostProgram.TapeSupported program (initialPostID input) := by
  intro position
  change MachineInput.tape foldedBlank (inputWord input) position ∈
    PostProgram.tableSupportedSymbols program
  cases hget : (inputWord input)[position]? with
  | none =>
      rw [MachineInput.tape, hget]
      exact PostProgram.blank_mem_tableSupportedSymbols program
  | some symbol =>
      rw [MachineInput.tape, hget]
      apply PostProgram.symbol_mem_tableSupportedSymbols
      exact inputWord_symbol_mem (List.mem_iff_getElem?.2 ⟨position, hget⟩)

theorem initialID_eq_tableID (input : List SourceSymbol) :
    MachineInput.initialID program.toTableProgram.toMachine (inputWord input) =
      PostProgram.tableIDOfPostID (initialPostID input) := by
  apply ID.ext <;> rfl

theorem machine_halts_iff_tableHalts (input : List SourceSymbol) :
    MachineInput.Halts program.toTableProgram.toMachine (inputWord input) ↔
      PostMachineInput.tableHalts program (initialPostID input) := by
  unfold MachineInput.Halts PostMachineInput.tableHalts
  apply exists_congr
  intro steps
  simp only [MachineInput.run, PostMachineInput.tableRun]
  rw [initialID_eq_tableID]
  rfl

private theorem part_dom_map_iff {α β : Type} (f : α → β) (p : Part α) :
    (f <$> p).Dom ↔ p.Dom := by
  rw [Part.map_eq_map]
  rfl

theorem postHalts_iff_tm0_eval_dom {input : List SourceSymbol} (hinput : input ≠ []) :
    PostMachineInput.postHalts program (initialPostID input) ↔
      (Turing.TM0.eval tm0 input).Dom := by
  let step := Turing.TM0.step tm0
  let initCfg := Turing.TM0.init (Λ := SourceLabel) input
  have hinitial : FoldedConfigRel initCfg (initialPostID input) :=
    FoldedConfigRel_initial hinput
  constructor
  · rintro ⟨steps, hhalt⟩
    rcases tm0_reaches_halt_of_post_halts hinitial steps hhalt with
      ⟨cfg, hreach, hterminal⟩
    rw [Turing.TM0.eval]
    apply (part_dom_map_iff (fun c => c.Tape.right₀)
      (StateTransition.eval step initCfg)).2
    exact Part.dom_iff_mem.2 ⟨cfg, StateTransition.mem_eval.2 ⟨hreach, hterminal⟩⟩
  · intro hdom
    have hdomState : (StateTransition.eval step initCfg).Dom := by
      rw [Turing.TM0.eval] at hdom
      exact (part_dom_map_iff (fun c => c.Tape.right₀)
        (StateTransition.eval step initCfg)).1 hdom
    let haltCfg := (StateTransition.eval step initCfg).get hdomState
    have hmem : haltCfg ∈ StateTransition.eval step initCfg := Part.get_mem hdomState
    rcases StateTransition.mem_eval.1 hmem with ⟨hreach, hterminal⟩
    exact FoldedConfigRel_reaches_halt hinitial hreach hterminal

theorem machine_halts_iff_tm0_eval_dom {input : List SourceSymbol} (hinput : input ≠ []) :
    MachineInput.Halts program.toTableProgram.toMachine (inputWord input) ↔
      (Turing.TM0.eval tm0 input).Dom := by
  rw [machine_halts_iff_tableHalts]
  rw [PostMachineInput.tableHalts_iff_postHalts (initialPostID_tapeSupported input)]
  exact postHalts_iff_tm0_eval_dom hinput

end UniversalTM0Folded
end LeanWang
