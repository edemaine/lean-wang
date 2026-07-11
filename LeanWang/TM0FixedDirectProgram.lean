/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.SimSemantics

/-!
# A direct finite program for one fixed Mathlib TM0 machine

For a fixed source code, computability of the program data is irrelevant: a
constant finite `PostProgram` is computable. We therefore enumerate the known
finite reachable-label support directly and emit the semantic folded row for
each label, side, marker, and folded symbol. This avoids position codes,
statement decoders, and all generated-row machinery.
-/

noncomputable section

namespace LeanWang
namespace TM0FixedDirectProgram

open TM0Route TM0FoldedCompiler

def rowsForLabel (tc : Turing.ToPartrec.Code) (q : SourceLabel tc) :
    List PostTransition :=
  foldSideList.flatMap fun side =>
    [false, true].flatMap fun marked =>
      partrecStartedTM0SymbolList.flatMap fun left =>
        partrecStartedTM0SymbolList.filterMap fun right =>
          simTransitionOfStep tc q side marked left right

def rows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  (partrecStartedTM0LabelList tc).flatMap (rowsForLabel tc)

/-- The direct folded program for one fixed translated Mathlib TM0 machine. -/
def program (tc : Turing.ToPartrec.Code) : PostProgram where
  symbols := foldedSymbolList
  states := foldedStateList tc
  blank := foldedBlank
  start := foldedSimStartState tc
  table := rows tc

@[simp] theorem program_symbols (tc : Turing.ToPartrec.Code) :
    (program tc).symbols = foldedSymbolList := rfl

@[simp] theorem program_states (tc : Turing.ToPartrec.Code) :
    (program tc).states = foldedStateList tc := rfl

@[simp] theorem program_blank (tc : Turing.ToPartrec.Code) :
    (program tc).blank = foldedBlank := rfl

@[simp] theorem program_start (tc : Turing.ToPartrec.Code) :
    (program tc).start = foldedSimStartState tc := rfl

theorem mem_rowsForLabel_state {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {e : PostTransition}
    (he : e ∈ rowsForLabel tc q) :
    ∃ side, e.state = foldedSimStateCode tc side q := by
  unfold rowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨side, _hside, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨marked, _hmarked, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨left, _hleft, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨right, _hright, htransition⟩
  unfold simTransitionOfStep at htransition
  split at htransition
  · contradiction
  · rename_i q' stmt hstep
    cases htransition
    refine ⟨side, ?_⟩
    cases stmt <;> rfl

theorem mem_rowsForLabel_step {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {e : PostTransition}
    (he : e ∈ rowsForLabel tc q) :
    ∃ side marked left right q' stmt,
      partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt) ∧
      e = simRowOfStep tc side marked q q' left right stmt := by
  unfold rowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨side, _hside, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨marked, _hmarked, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨left, _hleft, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨right, _hright, htransition⟩
  unfold simTransitionOfStep at htransition
  split at htransition
  · contradiction
  · rename_i q' stmt hstep
    cases htransition
    exact ⟨side, marked, left, right, q', stmt, hstep, rfl⟩

theorem foldedSimStateCode_ne_of_label_ne
    {tc : Turing.ToPartrec.Code} {q r : SourceLabel tc}
    (hq : q ∈ partrecStartedTM0LabelList tc)
    (hr : r ∈ partrecStartedTM0LabelList tc) (hne : r ≠ q)
    (side side' : FoldSide) :
    foldedSimStateCode tc side' r ≠ foldedSimStateCode tc side q := by
  intro hstate
  unfold foldedSimStateCode taggedState at hstate
  have hpayload := (Nat.pair_eq_pair.mp hstate).2
  have hparts := Nat.pair_eq_pair.mp hpayload
  have hcode : TM0FiniteCompiler.stateCode tc r =
      TM0FiniteCompiler.stateCode tc q := hparts.2
  have hrLabels := (mem_partrecStartedTM0LabelList tc r).1 hr
  have hqLabels := (mem_partrecStartedTM0LabelList tc q).1 hq
  exact hne (TM0FiniteCompiler.stateCode_injective_on_labels
    hrLabels hqLabels hcode)

theorem rowsForLabel_find?_eq_none_of_label_ne
    {tc : Turing.ToPartrec.Code} {q r : SourceLabel tc}
    (hq : q ∈ partrecStartedTM0LabelList tc)
    (hr : r ∈ partrecStartedTM0LabelList tc) (hne : r ≠ q)
    (side : FoldSide) (marked : Bool) (left right : SourceSymbol) :
    (rowsForLabel tc r).find? (fun e =>
      e.matchesInput (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right)) = none := by
  apply program_find?_eq_none_of_forall_matchesInput_false
  intro e he
  rcases mem_rowsForLabel_state he with ⟨side', hstate⟩
  unfold PostTransition.matchesInput
  rw [hstate]
  simp [foldedSimStateCode_ne_of_label_ne hq hr hne side side']

private theorem rows_find?_of_step_aux
    {tc : Turing.ToPartrec.Code} {q q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (labels : List (SourceLabel tc))
    (hlabels : ∀ r ∈ labels, r ∈ partrecStartedTM0LabelList tc)
    (hq : q ∈ labels)
    (hstep : partrecStartedTM0Machine tc q (foldedRead side left right) =
      some (q', stmt)) :
    (labels.flatMap (rowsForLabel tc)).find? (fun e =>
      e.matchesInput (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction labels with
  | nil => cases hq
  | cons r labels ih =>
      simp only [List.mem_cons] at hq
      by_cases hrq : r = q
      · subst r
        have hhead := program_find?_flatMap_simTransition_side_of_step_aux
          (marked := marked) foldSideList (mem_foldSideList side) hstep
        simpa only [List.flatMap_cons, rowsForLabel] using
          program_find?_append_of_eq_some hhead
      · have hqtail : q ∈ labels := hq.resolve_left (Ne.symm hrq)
        have hhead := rowsForLabel_find?_eq_none_of_label_ne
          (hlabels q (by simp [hqtail])) (hlabels r (by simp)) hrq
          side marked left right
        simp only [List.flatMap_cons]
        rw [program_find?_append_of_eq_none hhead]
        exact ih (fun s hs => hlabels s (by simp [hs])) hqtail

theorem rows_find?_of_step
    {tc : Turing.ToPartrec.Code} {q q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hq : q ∈ partrecStartedTM0LabelList tc)
    (hstep : partrecStartedTM0Machine tc q (foldedRead side left right) =
      some (q', stmt)) :
    (rows tc).find? (fun e =>
      e.matchesInput (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  unfold rows
  exact rows_find?_of_step_aux (partrecStartedTM0LabelList tc)
    (fun _ h => h) hq hstep

theorem rowsForLabel_find?_eq_none_of_no_step
    {tc : Turing.ToPartrec.Code} {q : SourceLabel tc}
    (side : FoldSide) (marked : Bool) (left right : SourceSymbol)
    (hstep : partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    (rowsForLabel tc q).find? (fun e =>
      e.matchesInput (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right)) = none := by
  apply program_find?_eq_none_of_forall_matchesInput_false
  intro e he
  rcases mem_rowsForLabel_step he with
    ⟨side', marked', left', right', q', stmt, hsource, rfl⟩
  by_cases hmatch :
      (simRowOfStep tc side' marked' q q' left' right' stmt).matchesInput
        (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) = false
  · exact hmatch
  · have htrue :
        (simRowOfStep tc side' marked' q q' left' right' stmt).matchesInput
          (foldedSimStateCode tc side q)
          (foldedSymbolCode marked left right) = true :=
      Bool.eq_true_of_not_eq_false hmatch
    unfold PostTransition.matchesInput at htrue
    simp only [Bool.and_eq_true, beq_iff_eq] at htrue
    have hstate : foldedSimStateCode tc side' q =
        foldedSimStateCode tc side q := by
      cases stmt <;> exact htrue.1
    have hread : foldedSymbolCode marked' left' right' =
        foldedSymbolCode marked left right := by
      cases stmt <;> exact htrue.2
    have hside : side' = side :=
      foldedSimStateCode_side_of_same_label_eq hstate
    have hparts := foldedSymbolCode_eq hread
    subst side'
    rcases hparts with ⟨rfl, rfl, rfl⟩
    rw [hstep] at hsource
    contradiction

private theorem rows_find?_eq_none_of_no_step_aux
    {tc : Turing.ToPartrec.Code} {q : SourceLabel tc}
    (labels : List (SourceLabel tc))
    (hlabels : ∀ r ∈ labels, r ∈ partrecStartedTM0LabelList tc)
    (hq : q ∈ partrecStartedTM0LabelList tc)
    (side : FoldSide) (marked : Bool) (left right : SourceSymbol)
    (hstep : partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    (labels.flatMap (rowsForLabel tc)).find? (fun e =>
      e.matchesInput (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right)) = none := by
  induction labels with
  | nil => simp
  | cons r labels ih =>
      by_cases hrq : r = q
      · subst r
        have hhead := rowsForLabel_find?_eq_none_of_no_step
          side marked left right hstep
        simp only [List.flatMap_cons]
        rw [program_find?_append_of_eq_none hhead]
        exact ih (fun s hs => hlabels s (by simp [hs]))
      · have hhead := rowsForLabel_find?_eq_none_of_label_ne
          hq (hlabels r (by simp)) hrq
          side marked left right
        simp only [List.flatMap_cons]
        rw [program_find?_append_of_eq_none hhead]
        exact ih (fun s hs => hlabels s (by simp [hs]))

theorem rows_find?_eq_none_of_no_step
    {tc : Turing.ToPartrec.Code} {q : SourceLabel tc}
    (hq : q ∈ partrecStartedTM0LabelList tc)
    (side : FoldSide) (marked : Bool) (left right : SourceSymbol)
    (hstep : partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    (rows tc).find? (fun e =>
      e.matchesInput (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right)) = none := by
  unfold rows
  exact rows_find?_eq_none_of_no_step_aux (partrecStartedTM0LabelList tc)
    (fun _ h => h) hq side marked left right hstep

end TM0FixedDirectProgram
end LeanWang
