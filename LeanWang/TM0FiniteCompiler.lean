/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PostMachine
import LeanWang.TM0Route

/-!
Finite one-sided TM0 program data extracted from the Mathlib TM0 route.

This file starts the concrete `TM0FiniteCompiler` construction. The current
definitions package the finite numeric headers: symbols, states, blank, and
start. The transition table will be generated from the supported Mathlib TM0
states and the explicit symbol list.
-/

noncomputable section

namespace LeanWang

namespace TM0FiniteCompiler

open TM0Route

/-- Numeric code for a supported translated TM0 state. -/
noncomputable def stateCode (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) : Nat := by
  classical
  exact
    if q = (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) then
      TM0Route.partrecStartedTM0Start
    else
      if hq : q ∈ TM0Route.partrecStartedTM0Labels tc then
        TM0Route.partrecStartedTM0StateCodeOfMem tc q
          (TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hq)
      else
        TM0Route.partrecStartedTM0Start

theorem stateCode_default (tc : Turing.ToPartrec.Code)
    : stateCode tc (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) =
      TM0Route.partrecStartedTM0Start := by
  classical
  simp [stateCode]

theorem stateCode_mem_states (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc) :
    stateCode tc q ∈ TM0Route.partrecStartedTM0States tc := by
  classical
  by_cases h : q = (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
  · simp [stateCode, h, TM0Route.partrecStartedTM0Start_mem_states]
  · simp [stateCode, h, hq, TM0Route.partrecStartedTM0StateCodeOfMem_mem_states tc q
      (TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hq)]

theorem stateCode_ne_start_of_mem_labels_ne_default {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hneq : q ≠ (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))) :
    stateCode tc q ≠ TM0Route.partrecStartedTM0Start := by
  classical
  let hqsupport := TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hq
  have hcode :
      stateCode tc q = TM0Route.partrecStartedTM0StateCodeOfMem tc q hqsupport := by
    simp [stateCode, hneq, hq]
  intro hstart
  have hindexStart :
      TM0Route.partrecStartedTM0StateCodeOfMem tc q hqsupport =
        TM0Route.partrecStartedTM0Start := by
    simpa [hcode] using hstart
  have hget := TM0Route.partrecStartedTM0StateCodeOfMem_get? tc q hqsupport
  rw [hindexStart] at hget
  unfold TM0Route.partrecStartedTM0Start at hget
  rw [TM0Route.partrecStartedTM0LabelSupportList_get_zero] at hget
  cases hget
  exact hneq rfl

theorem stateCode_injective_on_labels {tc : Turing.ToPartrec.Code}
    {q r : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hr : r ∈ TM0Route.partrecStartedTM0Labels tc)
    (hcode : stateCode tc q = stateCode tc r) :
    q = r := by
  classical
  by_cases hqdef :
      q = (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
  · subst q
    by_cases hrdef :
        r = (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    · exact hrdef.symm
    · have hrne := stateCode_ne_start_of_mem_labels_ne_default hr hrdef
      have hstart := stateCode_default tc
      rw [hstart] at hcode
      exact False.elim (hrne hcode.symm)
  · by_cases hrdef :
        r = (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    · subst r
      have hqne := stateCode_ne_start_of_mem_labels_ne_default hq hqdef
      have hstart := stateCode_default tc
      rw [hstart] at hcode
      exact False.elim (hqne hcode)
    · let hqsupport := TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hq
      let hrsupport := TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hr
      have hqcode :
          stateCode tc q = TM0Route.partrecStartedTM0StateCodeOfMem tc q hqsupport := by
        simp [stateCode, hqdef, hq]
      have hrcode :
          stateCode tc r = TM0Route.partrecStartedTM0StateCodeOfMem tc r hrsupport := by
        simp [stateCode, hrdef, hr]
      have hindex :
          TM0Route.partrecStartedTM0StateCodeOfMem tc q hqsupport =
            TM0Route.partrecStartedTM0StateCodeOfMem tc r hrsupport := by
        simpa [hqcode, hrcode] using hcode
      have hgetq := TM0Route.partrecStartedTM0StateCodeOfMem_get? tc q hqsupport
      have hgetr := TM0Route.partrecStartedTM0StateCodeOfMem_get? tc r hrsupport
      rw [hindex, hgetr] at hgetq
      cases hgetq
      rfl

theorem next_label_mem_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    q' ∈ TM0Route.partrecStartedTM0Labels tc := by
  exact (TM0Route.partrecStartedTM0_supports tc).2
    (show (q', stmt) ∈ TM0Route.partrecStartedTM0Machine tc q a by
      rw [hstep]
      simp)
    hq

def moveOfDir : Turing.Dir → Move
  | Turing.Dir.left => Move.left
  | Turing.Dir.right => Move.right

def stmtOfTM0Stmt :
    Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol) →
      PostStmt
  | Turing.TM0.Stmt.move d => PostStmt.move (moveOfDir d)
  | Turing.TM0.Stmt.write a => PostStmt.write (TM0Route.partrecStartedTM0SymbolCode a)

noncomputable def rowOfStep (tc : Turing.ToPartrec.Code)
    (q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    (a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
    (stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)) :
    PostTransition where
  state := stateCode tc q
  read := TM0Route.partrecStartedTM0SymbolCode a
  next := stateCode tc q'
  stmt := stmtOfTM0Stmt stmt

noncomputable def transitionOfStep (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    (a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol) :
    Option PostTransition :=
  match _hstep : TM0Route.partrecStartedTM0Machine tc q a with
  | none => none
  | some (q', stmt) => some (rowOfStep tc q q' a stmt)

theorem rowOfStep_matchesInput {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)} :
    (rowOfStep tc q q' a stmt).matchesInput
      (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) = true := by
  simp [rowOfStep, PostTransition.matchesInput]

theorem rowOfStep_state {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)} :
    (rowOfStep tc q q' a stmt).state = stateCode tc q := rfl

theorem rowOfStep_read {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)} :
    (rowOfStep tc q q' a stmt).read =
      TM0Route.partrecStartedTM0SymbolCode a := rfl

theorem rowOfStep_next {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)} :
    (rowOfStep tc q q' a stmt).next = stateCode tc q' := rfl

theorem rowOfStep_stmt {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)} :
    (rowOfStep tc q q' a stmt).stmt = stmtOfTM0Stmt stmt := rfl

theorem exists_transitionOfStep_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {hq : q ∈ TM0Route.partrecStartedTM0Labels tc}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    ∃ e : PostTransition,
      transitionOfStep tc q a = some e ∧
        e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) = true ∧
        e.next ∈ TM0Route.partrecStartedTM0States tc ∧
        e.stmt = stmtOfTM0Stmt stmt := by
  unfold transitionOfStep
  cases hm : TM0Route.partrecStartedTM0Machine tc q a with
  | none =>
      rw [hm] at hstep
      cases hstep
  | some p =>
      rcases p with ⟨r, s⟩
      rw [hm] at hstep
      cases hstep
      refine ⟨rowOfStep tc q q' a stmt, ?_, ?_, ?_, ?_⟩
      · simp
      · exact rowOfStep_matchesInput
      · rw [rowOfStep_next]
        exact stateCode_mem_states tc q' (next_label_mem_of_step hq hm)
      · exact rowOfStep_stmt

theorem transitionOfStep_eq_some_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    transitionOfStep tc q a = some (rowOfStep tc q q' a stmt) := by
  unfold transitionOfStep
  cases hm : TM0Route.partrecStartedTM0Machine tc q a with
  | none =>
      rw [hm] at hstep
      cases hstep
  | some p =>
      rcases p with ⟨r, s⟩
      rw [hm] at hstep
      cases hstep
      rfl

theorem transitionOfStep_eq_none_of_no_step {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = none) :
    transitionOfStep tc q a = none := by
  unfold transitionOfStep
  cases hm : TM0Route.partrecStartedTM0Machine tc q a with
  | none => rfl
  | some p =>
      rw [hm] at hstep
      cases hstep

theorem transitionOfStep_state_of_some {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {e : PostTransition}
    (he : transitionOfStep tc q a = some e) :
    e.state = stateCode tc q := by
  unfold transitionOfStep at he
  split at he
  · cases he
  · cases he
    rfl

theorem transitionOfStep_read_of_some {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {e : PostTransition}
    (he : transitionOfStep tc q a = some e) :
    e.read = TM0Route.partrecStartedTM0SymbolCode a := by
  unfold transitionOfStep at he
  split at he
  · cases he
  · cases he
    rfl

theorem transitionOfStep_matchesInput_self_of_some {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {e : PostTransition}
    (he : transitionOfStep tc q a = some e) :
    e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) = true := by
  have hstate := transitionOfStep_state_of_some he
  have hread := transitionOfStep_read_of_some he
  cases e
  simp [PostTransition.matchesInput] at hstate hread ⊢
  simp [hstate, hread]

theorem transitionOfStep_matchesInput_of_symbol_ne {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a b : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {e : PostTransition}
    (hne : b ≠ a)
    (he : transitionOfStep tc q b = some e) :
    e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) = false := by
  have hstate := transitionOfStep_state_of_some he
  have hread := transitionOfStep_read_of_some he
  have hread_ne :
      TM0Route.partrecStartedTM0SymbolCode b ≠ TM0Route.partrecStartedTM0SymbolCode a := by
    intro hcode
    exact hne (TM0Route.partrecStartedTM0SymbolCode_injective hcode)
  cases e
  simp [PostTransition.matchesInput] at hstate hread ⊢
  simp [hstate, hread, hread_ne]

theorem transitionOfStep_matchesInput_of_stateCode_ne {tc : Turing.ToPartrec.Code}
    {q r : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a b : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {e : PostTransition}
    (hne : stateCode tc r ≠ stateCode tc q)
    (he : transitionOfStep tc r b = some e) :
    e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) = false := by
  have hstate := transitionOfStep_state_of_some he
  cases e
  simp [PostTransition.matchesInput] at hstate ⊢
  simp [hstate, hne]

private theorem find?_append_of_eq_some {α : Type} {xs ys : List α} {p : α → Bool} {a : α}
    (h : xs.find? p = some a) :
    (xs ++ ys).find? p = some a := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      by_cases hp : p x = true
      · have hx : x = a := by
          simpa [hp] using h
        subst a
        simp [hp]
      · have htail : xs.find? p = some a := by
          simpa [hp] using h
        simp [hp, htail]

private theorem find?_append_of_eq_none {α : Type} {xs ys : List α} {p : α → Bool}
    (h : xs.find? p = none) :
    (xs ++ ys).find? p = ys.find? p := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      by_cases hp : p x = true
      · simp [hp] at h
      · have htail : xs.find? p = none := by
          simpa [hp] using h
        simpa [hp] using ih htail

noncomputable def transitionsForState (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) : List PostTransition :=
  TM0Route.partrecStartedTM0SymbolList.filterMap fun a =>
    transitionOfStep tc q a

private theorem find?_filterMap_transitionOfStep_of_step_aux {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (symbols : List
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol))
    (ha : a ∈ symbols)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    (symbols.filterMap fun b => transitionOfStep tc q b).find?
        (fun e =>
          e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a)) =
      some (rowOfStep tc q q' a stmt) := by
  induction symbols with
  | nil =>
      cases ha
  | cons b symbols ih =>
      simp only [List.mem_cons] at ha
      by_cases hba : b = a
      · subst b
        have hb := transitionOfStep_eq_some_of_step hstep
        simp [hb, rowOfStep_matchesInput]
      · have ha_tail : a ∈ symbols := by
          rcases ha with h | h
          · exact False.elim (hba h.symm)
          · exact h
        have ih_tail := ih ha_tail
        cases hb : transitionOfStep tc q b with
        | none =>
            simp [hb, ih_tail]
        | some e =>
            have hmiss := transitionOfStep_matchesInput_of_symbol_ne hba hb
            simp [hb, hmiss, ih_tail]

theorem transitionsForState_find?_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    (transitionsForState tc q).find?
        (fun e =>
          e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a)) =
      some (rowOfStep tc q q' a stmt) := by
  unfold transitionsForState
  exact find?_filterMap_transitionOfStep_of_step_aux
    TM0Route.partrecStartedTM0SymbolList (TM0Route.mem_partrecStartedTM0SymbolList a) hstep

private theorem find?_filterMap_transitionOfStep_eq_none_aux {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    (symbols : List
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol))
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = none) :
    (symbols.filterMap fun b => transitionOfStep tc q b).find?
        (fun e =>
          e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a)) =
      none := by
  induction symbols with
  | nil =>
      simp
  | cons b symbols ih =>
      by_cases hba : b = a
      · subst b
        have hb := transitionOfStep_eq_none_of_no_step hstep
        simp [hb, ih]
      · cases hb : transitionOfStep tc q b with
        | none =>
            simp [hb, ih]
        | some e =>
            have hmiss := transitionOfStep_matchesInput_of_symbol_ne hba hb
            simp [hb, hmiss, ih]

theorem transitionsForState_find?_eq_none_of_no_step {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = none) :
    (transitionsForState tc q).find?
        (fun e =>
          e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a)) =
      none := by
  unfold transitionsForState
  exact find?_filterMap_transitionOfStep_eq_none_aux
    TM0Route.partrecStartedTM0SymbolList hstep

private theorem find?_filterMap_transitionOfStep_eq_none_of_stateCode_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q r : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    (symbols : List
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol))
    (hne : stateCode tc r ≠ stateCode tc q) :
    (symbols.filterMap fun b => transitionOfStep tc r b).find?
        (fun e =>
          e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a)) =
      none := by
  induction symbols with
  | nil =>
      simp
  | cons b symbols ih =>
      cases hb : transitionOfStep tc r b with
      | none =>
          simp [hb, ih]
      | some e =>
          have hmiss := transitionOfStep_matchesInput_of_stateCode_ne (a := a) hne hb
          simp [hb, hmiss, ih]

theorem transitionsForState_find?_eq_none_of_stateCode_ne {tc : Turing.ToPartrec.Code}
    {q r : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    (hne : stateCode tc r ≠ stateCode tc q) :
    (transitionsForState tc r).find?
        (fun e =>
          e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a)) =
      none := by
  unfold transitionsForState
  exact find?_filterMap_transitionOfStep_eq_none_of_stateCode_ne_aux
    TM0Route.partrecStartedTM0SymbolList hne

theorem exists_mem_transitionsForState_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {hq : q ∈ TM0Route.partrecStartedTM0Labels tc}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    ∃ e ∈ transitionsForState tc q,
      e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) = true ∧
        e.next ∈ TM0Route.partrecStartedTM0States tc ∧
        e.stmt = stmtOfTM0Stmt stmt := by
  rcases exists_transitionOfStep_of_step (hq := hq) hstep with
    ⟨e, heq, hmatch, hnext, hstmt⟩
  refine ⟨e, ?_, hmatch, hnext, hstmt⟩
  unfold transitionsForState
  rw [List.mem_filterMap]
  exact ⟨a, TM0Route.mem_partrecStartedTM0SymbolList a, heq⟩

noncomputable def transitionTable (tc : Turing.ToPartrec.Code) : List PostTransition :=
  (TM0Route.partrecStartedTM0LabelList tc).flatMap fun q =>
    transitionsForState tc q

private theorem find?_flatMap_transitionsForState_of_step_aux {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (labels : List (Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)))
    (hall : ∀ r, r ∈ labels → r ∈ TM0Route.partrecStartedTM0Labels tc)
    (hqmem : q ∈ labels)
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    (labels.flatMap fun r => transitionsForState tc r).find?
        (fun e =>
          e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a)) =
      some (rowOfStep tc q q' a stmt) := by
  revert hall hqmem
  induction labels with
  | nil =>
      intro hall hqmem
      cases hqmem
  | cons r labels ih =>
      intro hall hqmem
      simp only [List.mem_cons] at hqmem
      have hall_tail : ∀ s, s ∈ labels → s ∈ TM0Route.partrecStartedTM0Labels tc := by
        intro s hs
        exact hall s (by simp [hs])
      by_cases hrq : r = q
      · subst r
        have hhead := transitionsForState_find?_of_step hstep
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hqmem_tail : q ∈ labels := by
          rcases hqmem with h | h
          · exact False.elim (hrq h.symm)
          · exact h
        have hr : r ∈ TM0Route.partrecStartedTM0Labels tc :=
          hall r (by simp)
        have hstate : stateCode tc r ≠ stateCode tc q := by
          intro hcode
          exact hrq (stateCode_injective_on_labels hr hq hcode)
        have hhead := transitionsForState_find?_eq_none_of_stateCode_ne
          (tc := tc) (q := q) (r := r) (a := a) hstate
        have htail := ih hall_tail hqmem_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem transitionTable_find?_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    (transitionTable tc).find?
        (fun e =>
          e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a)) =
      some (rowOfStep tc q q' a stmt) := by
  unfold transitionTable
  exact find?_flatMap_transitionsForState_of_step_aux
    (TM0Route.partrecStartedTM0LabelList tc)
    (fun r hr => (TM0Route.mem_partrecStartedTM0LabelList tc r).1 hr)
    hqlist ((TM0Route.mem_partrecStartedTM0LabelList tc q).1 hqlist) hstep

private theorem find?_flatMap_transitionsForState_eq_none_aux {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    (labels : List (Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)))
    (hall : ∀ r, r ∈ labels → r ∈ TM0Route.partrecStartedTM0Labels tc)
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = none) :
    (labels.flatMap fun r => transitionsForState tc r).find?
        (fun e =>
          e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a)) =
      none := by
  revert hall
  induction labels with
  | nil =>
      intro hall
      simp
  | cons r labels ih =>
      intro hall
      have hall_tail : ∀ s, s ∈ labels → s ∈ TM0Route.partrecStartedTM0Labels tc := by
        intro s hs
        exact hall s (by simp [hs])
      by_cases hrq : r = q
      · subst r
        have hhead := transitionsForState_find?_eq_none_of_no_step hstep
        have htail := ih hall_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail
      · have hr : r ∈ TM0Route.partrecStartedTM0Labels tc :=
          hall r (by simp)
        have hstate : stateCode tc r ≠ stateCode tc q := by
          intro hcode
          exact hrq (stateCode_injective_on_labels hr hq hcode)
        have hhead := transitionsForState_find?_eq_none_of_stateCode_ne
          (tc := tc) (q := q) (r := r) (a := a) hstate
        have htail := ih hall_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem transitionTable_find?_eq_none_of_no_step {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = none) :
    (transitionTable tc).find?
        (fun e =>
          e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a)) =
      none := by
  unfold transitionTable
  exact find?_flatMap_transitionsForState_eq_none_aux
    (TM0Route.partrecStartedTM0LabelList tc)
    (fun r hr => (TM0Route.mem_partrecStartedTM0LabelList tc r).1 hr)
    hq hstep

theorem exists_mem_transitionTable_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {hq : q ∈ TM0Route.partrecStartedTM0Labels tc}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    ∃ e ∈ transitionTable tc,
      e.matchesInput (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) = true ∧
        e.next ∈ TM0Route.partrecStartedTM0States tc ∧
        e.stmt = stmtOfTM0Stmt stmt := by
  rcases exists_mem_transitionsForState_of_step (hq := hq) hstep with
    ⟨e, hemem, hmatch, hnext, hstmt⟩
  refine ⟨e, ?_, hmatch, hnext, hstmt⟩
  unfold transitionTable
  rw [List.mem_flatMap]
  refine ⟨q, hqlist, ?_⟩
  exact hemem

theorem mem_transitionTable_state_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ transitionTable tc) :
    e.state ∈ TM0Route.partrecStartedTM0States tc := by
  unfold transitionTable transitionsForState at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, _hqmem, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨a, _hamem, hrow⟩
  unfold transitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    exact stateCode_mem_states tc q ((TM0Route.mem_partrecStartedTM0LabelList tc q).1 _hqmem)

theorem mem_transitionTable_read_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ transitionTable tc) :
    e.read ∈ TM0Route.partrecStartedTM0Symbols := by
  unfold transitionTable transitionsForState at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, _hqmem, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨a, _hamem, hrow⟩
  unfold transitionOfStep at hrow
  split at hrow
  · cases hrow
  · cases hrow
    exact TM0Route.partrecStartedTM0SymbolCode_mem_symbols a

theorem mem_transitionTable_next_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ transitionTable tc) :
    e.next ∈ TM0Route.partrecStartedTM0States tc := by
  unfold transitionTable transitionsForState at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, _hqmem, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨a, _hamem, hrow⟩
  unfold transitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    exact stateCode_mem_states tc q' (next_label_mem_of_step
      ((TM0Route.mem_partrecStartedTM0LabelList tc q).1 _hqmem) hstep)

theorem mem_transitionTable_write_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ transitionTable tc) :
    match e.stmt with
    | PostStmt.move _ => True
    | PostStmt.write b => b ∈ TM0Route.partrecStartedTM0Symbols := by
  unfold transitionTable transitionsForState at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, _hqmem, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨a, _hamem, hrow⟩
  unfold transitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    cases stmt with
    | move d =>
        simp [rowOfStep, stmtOfTM0Stmt]
    | write b =>
        simpa [rowOfStep, stmtOfTM0Stmt] using
          TM0Route.partrecStartedTM0SymbolCode_mem_symbols b

/--
Finite program header for the TM0 route.

The table is empty for now; subsequent chunks will replace it by the finite
transition rows obtained by enumerating supported labels and tape symbols.
-/
def programHeader (tc : Turing.ToPartrec.Code) : FiniteTM0Program where
  symbols := TM0Route.partrecStartedTM0Symbols
  states := TM0Route.partrecStartedTM0States tc
  blank := TM0Route.partrecStartedTM0Blank
  start := TM0Route.partrecStartedTM0Start
  table := transitionTable tc

@[simp]
theorem programHeader_symbols (tc : Turing.ToPartrec.Code) :
    (programHeader tc).symbols = TM0Route.partrecStartedTM0Symbols := rfl

@[simp]
theorem programHeader_states (tc : Turing.ToPartrec.Code) :
    (programHeader tc).states = TM0Route.partrecStartedTM0States tc := rfl

@[simp]
theorem programHeader_blank (tc : Turing.ToPartrec.Code) :
    (programHeader tc).blank = TM0Route.partrecStartedTM0Blank := rfl

@[simp]
theorem programHeader_start (tc : Turing.ToPartrec.Code) :
    (programHeader tc).start = TM0Route.partrecStartedTM0Start := rfl

@[simp]
theorem programHeader_table (tc : Turing.ToPartrec.Code) :
    (programHeader tc).table = transitionTable tc := rfl

theorem programHeader_blank_mem_symbols (tc : Turing.ToPartrec.Code) :
    (programHeader tc).blank ∈ (programHeader tc).symbols := by
  simp [TM0Route.partrecStartedTM0Blank_mem_symbols]

theorem programHeader_start_mem_states (tc : Turing.ToPartrec.Code) :
    (programHeader tc).start ∈ (programHeader tc).states := by
  simp [TM0Route.partrecStartedTM0Start_mem_states]

/-- Candidate finite one-sided TM0 program produced by the Mathlib TM0 route. -/
def program (tc : Turing.ToPartrec.Code) : FiniteTM0Program :=
  programHeader tc

@[simp]
theorem program_symbols (tc : Turing.ToPartrec.Code) :
    (program tc).symbols = TM0Route.partrecStartedTM0Symbols := rfl

@[simp]
theorem program_states (tc : Turing.ToPartrec.Code) :
    (program tc).states = TM0Route.partrecStartedTM0States tc := rfl

@[simp]
theorem program_blank (tc : Turing.ToPartrec.Code) :
    (program tc).blank = TM0Route.partrecStartedTM0Blank := rfl

@[simp]
theorem program_start (tc : Turing.ToPartrec.Code) :
    (program tc).start = TM0Route.partrecStartedTM0Start := rfl

@[simp]
theorem program_table (tc : Turing.ToPartrec.Code) :
    (program tc).table = transitionTable tc := rfl

theorem program_blank_mem_symbols (tc : Turing.ToPartrec.Code) :
    (program tc).blank ∈ (program tc).symbols := by
  exact programHeader_blank_mem_symbols tc

theorem program_start_mem_states (tc : Turing.ToPartrec.Code) :
    (program tc).start ∈ (program tc).states := by
  exact programHeader_start_mem_states tc

theorem program_transition?_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    (program tc).transition?
        (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) =
      some (rowOfStep tc q q' a stmt) := by
  simp [PostProgram.transition?, transitionTable_find?_of_step hqlist hstep]

theorem program_transition?_eq_none_of_no_step {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = none) :
    (program tc).transition?
        (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) =
      none := by
  simp [PostProgram.transition?, transitionTable_find?_eq_none_of_no_step hq hstep]

theorem program_step_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    (program tc).step (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) =
      some (stateCode tc q', stmtOfTM0Stmt stmt) := by
  have hq : q ∈ TM0Route.partrecStartedTM0Labels tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q).1 hqlist
  have hfind := program_transition?_of_step hqlist hstep
  have hnext : stateCode tc q' ∈ TM0Route.partrecStartedTM0States tc :=
    stateCode_mem_states tc q' (next_label_mem_of_step hq hstep)
  cases stmt with
  | move d =>
      simp [PostProgram.step, hfind, rowOfStep, stmtOfTM0Stmt, hnext]
  | write b =>
      have hwrite : TM0Route.partrecStartedTM0SymbolCode b ∈
          TM0Route.partrecStartedTM0Symbols :=
        TM0Route.partrecStartedTM0SymbolCode_mem_symbols b
      simp [PostProgram.step, hfind, rowOfStep, stmtOfTM0Stmt, hnext, hwrite]

theorem program_step_eq_none_of_no_step {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = none) :
    (program tc).step (stateCode tc q) (TM0Route.partrecStartedTM0SymbolCode a) =
      none := by
  have hfind := program_transition?_eq_none_of_no_step hq hstep
  simp [PostProgram.step, hfind]

end TM0FiniteCompiler

end LeanWang
