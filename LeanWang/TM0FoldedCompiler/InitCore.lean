/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.InitSearch

/-!
Core folded initialization facts and shared `find?` helpers.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

namespace FoldSide

theorem code_injective : Function.Injective code := by
  intro s t h
  cases s <;> cases t <;> simp [code] at h ⊢

end FoldSide

/--
Code a folded tape cell.

The Boolean marker distinguishes the origin cell, which is the only place where
a simulated left/right move can cross between the two folded sides without
moving the local one-sided head.
-/
theorem foldedSymbolCode_injective :
    Function.Injective (fun p : Bool × SourceSymbol × SourceSymbol =>
      foldedSymbolCode p.1 p.2.1 p.2.2) := by
  intro p r h
  rcases p with ⟨marked, left, right⟩
  rcases r with ⟨marked', left', right'⟩
  unfold foldedSymbolCode at h
  have hpair := Nat.pair_eq_pair.mp h
  have hmarked : marked = marked' := by
    cases marked <;> cases marked' <;> simp at hpair ⊢
  have hsymbols := Nat.pair_eq_pair.mp hpair.2
  have hleft : left = left' :=
    TM0Route.partrecStartedTM0SymbolCode_injective hsymbols.1
  have hright : right = right' :=
    TM0Route.partrecStartedTM0SymbolCode_injective hsymbols.2
  cases hmarked
  cases hleft
  cases hright
  rfl

theorem foldedSimStateCode_injective_on_labels {tc : Turing.ToPartrec.Code}
    {side side' : FoldSide} {q q' : SourceLabel tc}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hq' : q' ∈ TM0Route.partrecStartedTM0LabelList tc)
    (h : foldedSimStateCode tc side q = foldedSimStateCode tc side' q') :
    side = side' ∧ q = q' := by
  unfold foldedSimStateCode taggedState stateTagSim at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  have hparts := Nat.pair_eq_pair.mp hpayload
  have hside : side = side' :=
    FoldSide.code_injective hparts.1
  have hqset : q ∈ TM0Route.partrecStartedTM0Labels tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q).1 hq
  have hq'set : q' ∈ TM0Route.partrecStartedTM0Labels tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q').1 hq'
  have hqeq : q = q' :=
    TM0FiniteCompiler.stateCode_injective_on_labels hqset hq'set hparts.2
  exact ⟨hside, hqeq⟩

/-- First prelude state: write the marked origin cell. -/
theorem foldedStartState_mem_states (tc : Turing.ToPartrec.Code) :
    foldedStartState ∈ foldedStateList tc := by
  simp [foldedStateList, foldedStateListOfCodes, foldedInitStateList,
    foldedStartState, initWriteOriginState]

theorem initReturnState_zero_mem_states (tc : Turing.ToPartrec.Code) :
    initReturnState 0 ∈ foldedStateList tc := by
  simp [foldedStateList, foldedStateListOfCodes, foldedInitStateList]

theorem initMoveRightState_mem_states {tc : Turing.ToPartrec.Code} {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length) :
    initMoveRightState i ∈ foldedStateList tc := by
  unfold foldedStateList foldedStateListOfCodes foldedInitStateList
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  simp

theorem initWriteRightState_mem_states {tc : Turing.ToPartrec.Code} {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length) :
    initWriteRightState i ∈ foldedStateList tc := by
  unfold foldedStateList foldedStateListOfCodes foldedInitStateList
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  simp

theorem initReturnState_mem_states {tc : Turing.ToPartrec.Code} {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length) :
    initReturnState i ∈ foldedStateList tc := by
  unfold foldedStateList foldedStateListOfCodes foldedInitStateList
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  simp

@[simp]
theorem mkRow_matchesInput (state read next : Nat) (stmt : PostStmt) :
    (mkRow state read next stmt).matchesInput state read = true := by
  simp [mkRow, PostTransition.matchesInput]

theorem mkRow_matchesInput_of_state_ne {state state' read read' next : Nat}
    {stmt : PostStmt} (h : state ≠ state') :
    (mkRow state read next stmt).matchesInput state' read' = false := by
  simp [mkRow, PostTransition.matchesInput, h]

theorem find?_append_of_eq_some {α : Type} {xs ys : List α} {p : α → Bool} {a : α}
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

theorem find?_append_of_eq_none {α : Type} {xs ys : List α} {p : α → Bool}
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

theorem find?_eq_none_of_forall_matchesInput_false
    {xs : List PostTransition} {q a : Nat}
    (h : ∀ e ∈ xs, e.matchesInput q a = false) :
    xs.find? (fun e => e.matchesInput q a) = none := by
  induction xs with
  | nil =>
      simp
  | cons e xs ih =>
      have hhead : e.matchesInput q a = false := h e (by simp)
      have htail : xs.find? (fun e => e.matchesInput q a) = none := by
        apply ih
        intro e he
        exact h e (by simp [he])
      simp [hhead, htail]

theorem initWriteOriginState_ne_initMoveRightState (i : Nat) :
    initWriteOriginState ≠ initMoveRightState i := by
  intro h
  unfold initWriteOriginState initMoveRightState taggedState stateTagInit at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  omega

theorem initWriteOriginState_ne_initWriteRightState (i : Nat) :
    initWriteOriginState ≠ initWriteRightState i := by
  intro h
  unfold initWriteOriginState initWriteRightState taggedState stateTagInit at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  omega

theorem initWriteOriginState_ne_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) :
    initWriteOriginState ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initWriteOriginState foldedSimStateCode taggedState stateTagInit stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

/-- First initialization row: mark the origin and write the first input symbol. -/
theorem initMoveRightState_injective :
    Function.Injective initMoveRightState := by
  intro i j h
  unfold initMoveRightState taggedState stateTagInit at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  omega

theorem initMoveRightState_ne_initWriteRightState (i j : Nat) :
    initMoveRightState i ≠ initWriteRightState j := by
  intro h
  unfold initMoveRightState initWriteRightState taggedState stateTagInit at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  omega

theorem initMoveRightState_ne_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initMoveRightState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initMoveRightState foldedSimStateCode taggedState stateTagInit stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega


end TM0FoldedCompiler

end LeanWang
