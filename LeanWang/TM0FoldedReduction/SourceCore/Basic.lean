/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.NatPartrecToToPartrec
import LeanWang.TM0FoldedProgram
import LeanWang.OllingerRobinsonScaffold
import Mathlib.Computability.Reduce

/-!
Packaging the folded finite-TM0 construction as the machine-side reduction.

`TM0FoldedProgram` provides the executable finite program data. This file
isolates the exact obligations needed to instantiate the main theorem surface:
computability of that program map and its semantic correctness against Mathlib's
translated TM0 evaluator.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/-- The remaining obligations for the folded finite-TM0 route. -/
structure Obligations where
  program_computable :
    Computable (fun tc : Turing.ToPartrec.Code => TM0FoldedCompiler.program tc)
  correct : ∀ tc : Turing.ToPartrec.Code,
    (TM0FoldedCompiler.program tc).HaltsEmpty ↔
      (Turing.TM0.eval
        (TM0Route.partrecStartedTM0Machine tc)
        TM0Route.partrecStartedTM0Input).Dom

/--
The exact obligations needed for the final reduction from `Nat.Partrec.Code`.

This avoids asking for computability of the folded finite-program construction
on every `Turing.ToPartrec.Code`; the undecidability proof only uses codes
reached by the computable translation `NatPartrecToToPartrec.translate`.
-/
structure SourceObligations where
  program_computable :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c))
  correct : ∀ c : Code,
    (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)).HaltsEmpty ↔
      (Nat.Partrec.Code.eval c 0).Dom

/--
Source-level obligations for the generated position-coded folded program.

This is the same reduction interface as `SourceObligations`, but it uses
`positionProgramData` directly. It is intended for the generated descriptor
route, where semantic correctness is proved by showing canonical execution
selects the generated rows, rather than by proving the generated row list is
equal to the canonical row list.
-/
structure PositionSourceObligations where
  program_computable :
    Computable (fun c : Code =>
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c))
  correct : ∀ c : Code,
    (TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)).HaltsEmpty ↔
      (Nat.Partrec.Code.eval c 0).Dom

/--
Semantic source correctness follows from any folded finite-TM0 semantic theorem
for the normalized program data, composed with the already-proved source-code
translation chain.

This keeps `TM0FoldedReduction` independent of the heavy folded simulation
proof file: a final module can import that proof and supply `hcorrect` without
making the reduction API itself expensive to rebuild.
-/
theorem sourceProgramData_correct_of_programData_tm0_correct
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom)
    (c : Code) :
    (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)).HaltsEmpty ↔
      (Nat.Partrec.Code.eval c 0).Dom :=
  (hcorrect (NatPartrecToToPartrec.translate c)).trans
    ((TM0Route.partrecStartedTM0_eval_dom_iff_tm2
        (NatPartrecToToPartrec.translate c)).trans
      ((TM0Route.partrecStartedTM2_eval_dom_iff_partrec
          (NatPartrecToToPartrec.translate c)).trans
        (NatPartrecToToPartrec.translate_tm2_dom c)))

/--
Build the exact source obligations from the two facts that remain to be supplied
by the folded finite-TM0 construction: source-level program-data computability
and normalized program-data semantic correctness.
-/
def sourceObligationsOfProgramData
    (hprogram : Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations where
  program_computable := hprogram
  correct := sourceProgramData_correct_of_programData_tm0_correct hcorrect

/--
Semantic source correctness for the generated position-coded program, composed
with the already-proved source-code translation chain.
-/
theorem sourcePositionProgramData_correct_of_positionProgramData_tm0_correct
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom)
    (c : Code) :
    (TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)).HaltsEmpty ↔
      (Nat.Partrec.Code.eval c 0).Dom :=
  (hcorrect (NatPartrecToToPartrec.translate c)).trans
    ((TM0Route.partrecStartedTM0_eval_dom_iff_tm2
        (NatPartrecToToPartrec.translate c)).trans
      ((TM0Route.partrecStartedTM2_eval_dom_iff_partrec
          (NatPartrecToToPartrec.translate c)).trans
        (NatPartrecToToPartrec.translate_tm2_dom c)))

/--
Build the generated-position source obligations from source-level program-data
computability and semantic correctness against Mathlib's translated TM0
evaluator.
-/
def positionSourceObligationsOfProgramData
    (hprogram : Computable (fun c : Code =>
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations where
  program_computable := hprogram
  correct := sourcePositionProgramData_correct_of_positionProgramData_tm0_correct hcorrect

/-- Broad folded-route obligations imply the source-code obligations actually used. -/
def Obligations.toSource (h : Obligations) : SourceObligations where
  program_computable := by
    exact (h.program_computable.comp NatPartrecToToPartrec.translate_computable).of_eq
      fun c => (TM0FoldedCompiler.programData_eq_program
        (NatPartrecToToPartrec.translate c)).symm
  correct := by
    intro c
    rw [TM0FoldedCompiler.programData_eq_program]
    exact (h.correct (NatPartrecToToPartrec.translate c)).trans
      ((TM0Route.partrecStartedTM0_eval_dom_iff_tm2
          (NatPartrecToToPartrec.translate c)).trans
        ((TM0Route.partrecStartedTM2_eval_dom_iff_partrec
            (NatPartrecToToPartrec.translate c)).trans
          (NatPartrecToToPartrec.translate_tm2_dom c)))

/-- Source-code descriptor list for the folded finite-TM0 reduction. -/
def sourceSimStepData (c : Code) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepData (NatPartrecToToPartrec.translate c)

/-- Source-code normalized folded program data. -/
def sourceProgramData (c : Code) : FiniteTM0Program :=
  TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)

/-- Source-code folded program generated from position-coded descriptors. -/
def sourcePositionProgramData (c : Code) : FiniteTM0Program :=
  TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)

theorem sourceProgramData_eq (c : Code) :
    sourceProgramData c =
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c) :=
  rfl

theorem sourcePositionProgramData_eq (c : Code) :
    sourcePositionProgramData c =
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c) :=
  rfl

theorem sourceSimStepData_eq (c : Code) :
    sourceSimStepData c =
      TM0FoldedCompiler.simStepData (NatPartrecToToPartrec.translate c) :=
  rfl

/-- Source-code statement-support count for the folded finite-TM0 route. -/
def sourceStatementCount (c : Code) : Nat :=
  TM0Route.partrecStartedTM0StatementCount (NatPartrecToToPartrec.translate c)

/-- Source-code label count, excluding the forced default support label. -/
def sourceLabelCount (c : Code) : Nat :=
  TM0Route.partrecStartedTM0LabelCount (NatPartrecToToPartrec.translate c)

/-- Source-code support-label count, including the forced default support label. -/
def sourceLabelSupportCount (c : Code) : Nat :=
  TM0Route.partrecStartedTM0LabelSupportCount (NatPartrecToToPartrec.translate c)

/-- Source-code numeric folded state count. -/
def sourceStateCount (c : Code) : Nat :=
  TM0Route.partrecStartedTM0StateCount (NatPartrecToToPartrec.translate c)

/-- Source-code numeric folded state list. -/
def sourceStates (c : Code) : List Nat :=
  TM0Route.partrecStartedTM0States (NatPartrecToToPartrec.translate c)

theorem sourceStatementCount_eq (c : Code) :
    sourceStatementCount c =
      TM0Route.partrecStartedTM0StatementCount (NatPartrecToToPartrec.translate c) :=
  rfl

theorem sourceStatementCount_pos (c : Code) : 0 < sourceStatementCount c :=
  TM0Route.partrecStartedTM0StatementCount_pos (NatPartrecToToPartrec.translate c)

theorem sourceStatementCount_one_lt (c : Code) : 1 < sourceStatementCount c :=
  TM0Route.partrecStartedTM0StatementCount_one_lt (NatPartrecToToPartrec.translate c)

theorem sourceLabelCount_eq (c : Code) :
    sourceLabelCount c =
      TM0Route.partrecStartedTM0LabelCount (NatPartrecToToPartrec.translate c) :=
  rfl

theorem sourceStateCount_eq (c : Code) :
    sourceStateCount c =
      TM0Route.partrecStartedTM0StateCount (NatPartrecToToPartrec.translate c) :=
  rfl

theorem sourceStates_eq (c : Code) :
    sourceStates c =
      TM0Route.partrecStartedTM0States (NatPartrecToToPartrec.translate c) :=
  rfl

theorem sourceStatementCount_primrec : Primrec sourceStatementCount :=
  TM0Route.partrecStartedTM0StatementCount_primrec.comp
    NatPartrecToToPartrec.translate_primrec

theorem sourceLabelCount_primrec : Primrec sourceLabelCount :=
  TM0Route.partrecStartedTM0LabelCount_primrec.comp
    NatPartrecToToPartrec.translate_primrec

theorem sourceLabelSupportCount_primrec : Primrec sourceLabelSupportCount :=
  TM0Route.partrecStartedTM0LabelSupportCount_primrec.comp
    NatPartrecToToPartrec.translate_primrec

theorem sourceStateCount_primrec : Primrec sourceStateCount :=
  TM0Route.partrecStartedTM0StateCount_primrec.comp
    NatPartrecToToPartrec.translate_primrec

theorem sourceStates_primrec : Primrec sourceStates :=
  TM0Route.partrecStartedTM0States_primrec.comp
    NatPartrecToToPartrec.translate_primrec

/--
Arithmetic decoder for the flat TM0 label index used by the source route.

The dependent label decoder in `TM0Route` enumerates statement support blocks,
one block for each `PartrecVar`. This helper exposes just the non-dependent
index arithmetic: a flat offset `i` names statement offset `k + i / |vars|`
and variable slot `i % |vars|`, provided the bounded statement fuel reaches
that block.
-/
def sourceLabelIndexFromSplit? (fuel k i : Nat) : Option (Nat × TM0Route.PartrecVar) :=
  let width := TM0Route.partrecVarList.length
  let block := i / width
  if block < fuel then
    (TM0Route.partrecVarList[i % width]?).map fun v => (k + block, v)
  else
    none

/-- Started arithmetic decoder for source-level flat TM0 label indices. -/
def sourceLabelIndexStartSplit? (c : Code) (i : Nat) :
    Option (Nat × TM0Route.PartrecVar) :=
  sourceLabelIndexFromSplit? (sourceStatementCount c) 0 i

theorem sourceLabelIndexFromSplit?_primrec :
    Primrec (fun p : Nat × Nat × Nat =>
      sourceLabelIndexFromSplit? p.1 p.2.1 p.2.2) := by
  let width : Nat := TM0Route.partrecVarList.length
  let fuel : Nat × Nat × Nat → Nat := fun p => p.1
  let kFn : Nat × Nat × Nat → Nat := fun p => p.2.1
  let iFn : Nat × Nat × Nat → Nat := fun p => p.2.2
  let block : Nat × Nat × Nat → Nat := fun p => iFn p / width
  let slot : Nat × Nat × Nat → Nat := fun p => iFn p % width
  have hfuel : Primrec fuel := Primrec.fst
  have hk : Primrec kFn := Primrec.fst.comp Primrec.snd
  have hi : Primrec iFn := Primrec.snd.comp Primrec.snd
  have hblock : Primrec block := Primrec.nat_div.comp hi (Primrec.const width)
  have hslot : Primrec slot := Primrec.nat_mod.comp hi (Primrec.const width)
  have hwithin : PrimrecPred (fun p : Nat × Nat × Nat => block p < fuel p) :=
    Primrec.nat_lt.comp hblock hfuel
  have hlookup : Primrec (fun p : Nat × Nat × Nat =>
      TM0Route.partrecVarList[slot p]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp hslot
  have hsome : Primrec₂ (fun p : Nat × Nat × Nat => fun v : TM0Route.PartrecVar =>
      (kFn p + block p, v)) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.nat_add.comp (hk.comp Primrec.fst) (hblock.comp Primrec.fst))
      Primrec.snd
  have hthen : Primrec (fun p : Nat × Nat × Nat =>
      (TM0Route.partrecVarList[slot p]?).map fun v => (kFn p + block p, v)) :=
    Primrec.option_map hlookup hsome
  exact (Primrec.ite hwithin hthen (Primrec.const none)).of_eq fun p => by
    simp [sourceLabelIndexFromSplit?, width, fuel, kFn, iFn, block, slot]

theorem sourceLabelIndexStartSplit?_primrec :
    Primrec (fun p : Code × Nat => sourceLabelIndexStartSplit? p.1 p.2) := by
  unfold sourceLabelIndexStartSplit?
  exact sourceLabelIndexFromSplit?_primrec.comp
    (Primrec.pair (sourceStatementCount_primrec.comp Primrec.fst)
      (Primrec.pair (Primrec.const 0) Primrec.snd))

theorem sourceLabelIndexFromSplit?_eq_some
    {fuel k i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    (h : sourceLabelIndexFromSplit? fuel k i = some (stmtIndex, v)) :
    stmtIndex = k + i / TM0Route.partrecVarList.length ∧
      i / TM0Route.partrecVarList.length < fuel ∧
      TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]? = some v := by
  unfold sourceLabelIndexFromSplit? at h
  by_cases hblock : i / TM0Route.partrecVarList.length < fuel
  · rw [if_pos hblock] at h
    cases hvar : TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]? with
    | none =>
        simp [hvar] at h
    | some v' =>
        have hpair :
            (k + i / TM0Route.partrecVarList.length, v') = (stmtIndex, v) := by
          simpa [hvar] using h
        have hstmt : k + i / TM0Route.partrecVarList.length = stmtIndex :=
          congrArg Prod.fst hpair
        have hv' : v' = v := congrArg Prod.snd hpair
        exact ⟨hstmt.symm, hblock, by simp [hv']⟩
  · rw [if_neg hblock] at h
    simp at h

theorem sourceLabelCount_eq_statementCount_mul (c : Code) :
    sourceLabelCount c =
      sourceStatementCount c * TM0Route.partrecVarList.length := by
  rfl

theorem sourcePartrecVarList_length_pos :
    0 < TM0Route.partrecVarList.length := by
  simp [TM0Route.partrecVarList]

theorem sourceLabelIndexFromSplit?_of_getElem?
    {fuel k i : Nat} {v : TM0Route.PartrecVar}
    (hblock : i / TM0Route.partrecVarList.length < fuel)
    (hv : TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]? = some v) :
    sourceLabelIndexFromSplit? fuel k i =
      some (k + i / TM0Route.partrecVarList.length, v) := by
  simp [sourceLabelIndexFromSplit?, hblock, hv]

theorem sourceLabelIndexFromSplit?_of_block_var_get?
    {fuel k block i : Nat} {v : TM0Route.PartrecVar}
    (hblock : block < fuel)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceLabelIndexFromSplit? fuel k (TM0Route.partrecVarList.length * block + i) =
      some (k + block, v) := by
  rcases List.getElem?_eq_some_iff.1 hv with ⟨hi, _hget⟩
  have hwidth : 0 < TM0Route.partrecVarList.length := sourcePartrecVarList_length_pos
  have hdiv :
      (TM0Route.partrecVarList.length * block + i) /
          TM0Route.partrecVarList.length = block := by
    rw [Nat.mul_add_div hwidth]
    simp [Nat.div_eq_of_lt hi]
  have hmod :
      (TM0Route.partrecVarList.length * block + i) %
          TM0Route.partrecVarList.length = i := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hi
  have hvmod :
      (TM0Route.partrecVarList)[
          (TM0Route.partrecVarList.length * block + i) %
            TM0Route.partrecVarList.length]? = some v := by
    simpa [hmod] using hv
  simpa [hdiv] using
    sourceLabelIndexFromSplit?_of_getElem?
      (fuel := fuel) (k := k) (i := TM0Route.partrecVarList.length * block + i)
      (by simpa [hdiv] using hblock) hvmod

theorem sourceLabelIndexFromSplit?_var_mem
    {fuel k i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    (h : sourceLabelIndexFromSplit? fuel k i = some (stmtIndex, v)) :
    v ∈ TM0Route.partrecVarList := by
  rcases sourceLabelIndexFromSplit?_eq_some h with ⟨_hstmt, _hblock, hv⟩
  exact List.mem_iff_getElem?.2 ⟨i % TM0Route.partrecVarList.length, hv⟩

theorem sourceLabelIndexFromSplit?_stmtIndex_lt
    {fuel k i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    (h : sourceLabelIndexFromSplit? fuel k i = some (stmtIndex, v)) :
    stmtIndex < k + fuel := by
  rcases sourceLabelIndexFromSplit?_eq_some h with ⟨hstmt, hblock, _hv⟩
  rw [hstmt]
  omega

theorem sourceLabelIndexFromSplit?_lt_bound
    {fuel k i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    (h : sourceLabelIndexFromSplit? fuel k i = some (stmtIndex, v)) :
    i < fuel * TM0Route.partrecVarList.length := by
  rcases sourceLabelIndexFromSplit?_eq_some h with ⟨_hstmt, hblock, _hv⟩
  exact (Nat.div_lt_iff_lt_mul sourcePartrecVarList_length_pos).1 hblock

theorem sourceLabelIndexFromSplit?_block_lt_of_lt_bound
    {fuel i : Nat} (hi : i < fuel * TM0Route.partrecVarList.length) :
    i / TM0Route.partrecVarList.length < fuel :=
  (Nat.div_lt_iff_lt_mul sourcePartrecVarList_length_pos).2 hi

theorem sourceLabelIndexFromSplit?_exists_of_lt_bound
    {fuel k i : Nat} (hi : i < fuel * TM0Route.partrecVarList.length) :
    ∃ stmtIndex v, sourceLabelIndexFromSplit? fuel k i = some (stmtIndex, v) := by
  have hblock := sourceLabelIndexFromSplit?_block_lt_of_lt_bound hi
  have hmod :
      i % TM0Route.partrecVarList.length < TM0Route.partrecVarList.length :=
    Nat.mod_lt i sourcePartrecVarList_length_pos
  let v : TM0Route.PartrecVar :=
    TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]'hmod
  have hv :
      TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]? = some v := by
    simp [v, List.getElem?_eq_getElem (l := TM0Route.partrecVarList) hmod]
  exact ⟨k + i / TM0Route.partrecVarList.length, v,
    sourceLabelIndexFromSplit?_of_getElem? hblock hv⟩

theorem sourceLabelIndexFromSplit?_isSome_iff_lt_bound
    {fuel k i : Nat} :
    (sourceLabelIndexFromSplit? fuel k i).isSome ↔
      i < fuel * TM0Route.partrecVarList.length := by
  constructor
  · intro hsome
    cases h : sourceLabelIndexFromSplit? fuel k i with
    | none =>
        simp [h] at hsome
    | some q =>
        exact sourceLabelIndexFromSplit?_lt_bound
          (fuel := fuel) (k := k) (i := i)
          (stmtIndex := q.1) (v := q.2) h
  · intro hi
    rcases sourceLabelIndexFromSplit?_exists_of_lt_bound (k := k) hi with
      ⟨stmtIndex, v, hsplit⟩
    simp [hsplit]

theorem sourceLabelIndexFromSplit?_eq_none_iff_bound_le
    {fuel k i : Nat} :
    sourceLabelIndexFromSplit? fuel k i = none ↔
      fuel * TM0Route.partrecVarList.length ≤ i := by
  constructor
  · intro hnone
    by_contra hnot
    have hi : i < fuel * TM0Route.partrecVarList.length := Nat.lt_of_not_ge hnot
    rcases sourceLabelIndexFromSplit?_exists_of_lt_bound (k := k) hi with
      ⟨stmtIndex, v, hsplit⟩
    rw [hsplit] at hnone
    simp at hnone
  · intro hle
    cases h : sourceLabelIndexFromSplit? fuel k i with
    | none =>
        rfl
    | some q =>
        have hi :
            i < fuel * TM0Route.partrecVarList.length :=
          sourceLabelIndexFromSplit?_lt_bound
            (fuel := fuel) (k := k) (i := i)
            (stmtIndex := q.1) (v := q.2) h
        exact False.elim ((Nat.not_lt_of_ge hle) hi)

theorem sourceLabelIndexStartSplit?_stmtIndex_lt
    {c : Code} {i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    (h : sourceLabelIndexStartSplit? c i = some (stmtIndex, v)) :
    stmtIndex < sourceStatementCount c := by
  unfold sourceLabelIndexStartSplit? at h
  have hlt := sourceLabelIndexFromSplit?_stmtIndex_lt h
  simpa using hlt

theorem sourceLabelIndexStartSplit?_eq_some
    {c : Code} {i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    (h : sourceLabelIndexStartSplit? c i = some (stmtIndex, v)) :
    stmtIndex = i / TM0Route.partrecVarList.length ∧
      i / TM0Route.partrecVarList.length < sourceStatementCount c ∧
      TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]? = some v := by
  unfold sourceLabelIndexStartSplit? at h
  simpa using sourceLabelIndexFromSplit?_eq_some h

theorem sourceLabelIndexStartSplit?_var_mem
    {c : Code} {i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    (h : sourceLabelIndexStartSplit? c i = some (stmtIndex, v)) :
    v ∈ TM0Route.partrecVarList := by
  unfold sourceLabelIndexStartSplit? at h
  exact sourceLabelIndexFromSplit?_var_mem h

theorem sourceLabelIndexStartSplit?_of_getElem?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hblock : i / TM0Route.partrecVarList.length < sourceStatementCount c)
    (hv : TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]? = some v) :
    sourceLabelIndexStartSplit? c i =
      some (i / TM0Route.partrecVarList.length, v) := by
  unfold sourceLabelIndexStartSplit?
  simpa using sourceLabelIndexFromSplit?_of_getElem?
    (fuel := sourceStatementCount c) (k := 0) (i := i) hblock hv

theorem sourceLabelIndexStartSplit?_of_block_var_get?
    {c : Code} {block i : Nat} {v : TM0Route.PartrecVar}
    (hblock : block < sourceStatementCount c)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceLabelIndexStartSplit? c (TM0Route.partrecVarList.length * block + i) =
      some (block, v) := by
  rcases List.getElem?_eq_some_iff.1 hv with ⟨hi, _hget⟩
  have hwidth : 0 < TM0Route.partrecVarList.length := sourcePartrecVarList_length_pos
  have hdiv :
      (TM0Route.partrecVarList.length * block + i) /
          TM0Route.partrecVarList.length = block := by
    rw [Nat.mul_add_div hwidth]
    simp [Nat.div_eq_of_lt hi]
  have hmod :
      (TM0Route.partrecVarList.length * block + i) %
          TM0Route.partrecVarList.length = i := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hi
  have hvmod :
      (TM0Route.partrecVarList)[
          (TM0Route.partrecVarList.length * block + i) %
            TM0Route.partrecVarList.length]? = some v := by
    simpa [hmod] using hv
  simpa [hdiv] using
    sourceLabelIndexStartSplit?_of_getElem?
      (c := c) (i := TM0Route.partrecVarList.length * block + i)
      (by simpa [hdiv] using hblock) hvmod

theorem sourceLabelIndexStartSplit?_of_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceLabelIndexStartSplit? c i = some (0, v) := by
  simpa using
    sourceLabelIndexStartSplit?_of_block_var_get? (c := c) (block := 0)
      (i := i) (v := v) (sourceStatementCount_pos c) hv

theorem sourceLabelIndexStartSplit?_of_one_add_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceLabelIndexStartSplit? c (TM0Route.partrecVarList.length + i) = some (1, v) := by
  simpa [Nat.mul_one] using
    sourceLabelIndexStartSplit?_of_block_var_get? (c := c) (block := 1)
      (i := i) (v := v) (sourceStatementCount_one_lt c) hv

theorem sourceLabelIndexStartSplit?_block_lt_of_lt_labelCount
    {c : Code} {i : Nat} (hi : i < sourceLabelCount c) :
    i / TM0Route.partrecVarList.length < sourceStatementCount c := by
  rw [sourceLabelCount_eq_statementCount_mul] at hi
  exact (Nat.div_lt_iff_lt_mul sourcePartrecVarList_length_pos).2 hi

theorem sourceLabelIndexStartSplit?_exists_of_lt_labelCount
    {c : Code} {i : Nat} (hi : i < sourceLabelCount c) :
    ∃ stmtIndex v, sourceLabelIndexStartSplit? c i = some (stmtIndex, v) := by
  have hblock := sourceLabelIndexStartSplit?_block_lt_of_lt_labelCount hi
  have hmod :
      i % TM0Route.partrecVarList.length < TM0Route.partrecVarList.length :=
    Nat.mod_lt i sourcePartrecVarList_length_pos
  let v : TM0Route.PartrecVar :=
    TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]'hmod
  have hv :
      TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]? = some v := by
    simp [v, List.getElem?_eq_getElem (l := TM0Route.partrecVarList) hmod]
  exact ⟨i / TM0Route.partrecVarList.length, v,
    sourceLabelIndexStartSplit?_of_getElem? hblock hv⟩

theorem sourceLabelIndexStartSplit?_lt_labelCount
    {c : Code} {i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    (h : sourceLabelIndexStartSplit? c i = some (stmtIndex, v)) :
    i < sourceLabelCount c := by
  unfold sourceLabelIndexStartSplit? at h
  rw [sourceLabelCount_eq_statementCount_mul]
  exact sourceLabelIndexFromSplit?_lt_bound h

theorem sourceLabelIndexStartSplit?_isSome_iff_lt_labelCount
    {c : Code} {i : Nat} :
    (sourceLabelIndexStartSplit? c i).isSome ↔ i < sourceLabelCount c := by
  constructor
  · intro hsome
    cases h : sourceLabelIndexStartSplit? c i with
    | none =>
        simp [h] at hsome
    | some q =>
        exact sourceLabelIndexStartSplit?_lt_labelCount (c := c) (i := i)
          (stmtIndex := q.1) (v := q.2) h
  · intro hi
    rcases sourceLabelIndexStartSplit?_exists_of_lt_labelCount hi with
      ⟨stmtIndex, v, hsplit⟩
    simp [hsplit]

theorem sourceLabelIndexStartSplit?_eq_none_iff_labelCount_le
    {c : Code} {i : Nat} :
    sourceLabelIndexStartSplit? c i = none ↔ sourceLabelCount c ≤ i := by
  unfold sourceLabelIndexStartSplit?
  rw [sourceLabelIndexFromSplit?_eq_none_iff_bound_le,
    sourceLabelCount_eq_statementCount_mul]

theorem sourceLabelAtByStatementFrom?_of_split
    {c : Code} {fuel k i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hsplit : sourceLabelIndexFromSplit? fuel k i = some (stmtIndex, v))
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) stmtIndex = some stmt) :
    TM0Route.partrecStartedTM0LabelAtByStatementFrom?
        (NatPartrecToToPartrec.translate c) fuel k i =
      some ((stmt, v) :
        Turing.TM1to0.Λ'
          (TM0Route.partrecStartedTM1Machine (NatPartrecToToPartrec.translate c))) := by
  rcases sourceLabelIndexFromSplit?_eq_some hsplit with ⟨hstmtIndex, hblock, hv⟩
  exact TM0Route.partrecStartedTM0LabelAtByStatementFrom?_of_div_mod
    (NatPartrecToToPartrec.translate c) hblock hv (by simpa [hstmtIndex] using hstmt)

theorem sourceLabelAtByStatementStart?_of_split
    {c : Code} {i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hsplit : sourceLabelIndexStartSplit? c i = some (stmtIndex, v))
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) stmtIndex = some stmt) :
    TM0Route.partrecStartedTM0LabelAtByStatement?
        (NatPartrecToToPartrec.translate c) i =
      some ((stmt, v) :
        Turing.TM1to0.Λ'
          (TM0Route.partrecStartedTM1Machine (NatPartrecToToPartrec.translate c))) := by
  unfold sourceLabelIndexStartSplit? at hsplit
  rw [← TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero_eq]
  exact sourceLabelAtByStatementFrom?_of_split hsplit hstmt

theorem sourceLabelAtByStatementFromWithSearchCode?_of_split
    {c : Code} {fuel k i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hsplit : sourceLabelIndexFromSplit? fuel k i = some (stmtIndex, v))
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) stmtIndex = some stmt) :
    TM0FoldedCompiler.labelAtByStatementFromWithSearchCode?
        (NatPartrecToToPartrec.translate c) fuel k i =
      some ((((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))),
        TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))) := by
  unfold TM0FoldedCompiler.labelAtByStatementFromWithSearchCode?
  rw [sourceLabelAtByStatementFrom?_of_split hsplit hstmt]
  rfl

theorem sourceLabelAtByStatementFromWithSearchCode?_of_block_var_get?
    {c : Code} {fuel k block i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hblock : block < fuel)
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) (k + block) = some stmt) :
    TM0FoldedCompiler.labelAtByStatementFromWithSearchCode?
        (NatPartrecToToPartrec.translate c) fuel k
        (TM0Route.partrecVarList.length * block + i) =
      some ((((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))),
        TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))) := by
  exact sourceLabelAtByStatementFromWithSearchCode?_of_split
    (sourceLabelIndexFromSplit?_of_block_var_get? hblock hv) hstmt

theorem sourceLabelAtByStatementStartWithSearchCode?_of_split
    {c : Code} {i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hsplit : sourceLabelIndexStartSplit? c i = some (stmtIndex, v))
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) stmtIndex = some stmt) :
    TM0FoldedCompiler.labelAtByStatementFromWithSearchCode?
        (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i =
      some ((((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))),
        TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))) := by
  unfold sourceLabelIndexStartSplit? at hsplit
  simpa using sourceLabelAtByStatementFromWithSearchCode?_of_split hsplit hstmt

theorem sourceLabelAtByStatementStartWithSearchCode?_of_block_var_get?
    {c : Code} {block i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hblock : block < sourceStatementCount c)
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) block = some stmt) :
    TM0FoldedCompiler.labelAtByStatementFromWithSearchCode?
        (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0
        (TM0Route.partrecVarList.length * block + i) =
      some ((((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))),
        TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))) := by
  exact sourceLabelAtByStatementStartWithSearchCode?_of_split
    (sourceLabelIndexStartSplit?_of_block_var_get? (c := c) hblock hv) hstmt

theorem sourceStatementAt_zero (c : Code) :
    TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) 0 =
      some (none : Option (Turing.TM1.Stmt
        (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
        (Turing.TM2to1.Λ'
          TM0Route.PartrecStack TM0Route.PartrecStackSymbol
          (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
          TM0Route.PartrecVar)
        TM0Route.PartrecVar)) := by
  exact TM0Route.partrecStartedTM0StatementAt?_zero (NatPartrecToToPartrec.translate c)

def sourceStartedTM1StartLabel (c : Code) :
    Turing.TM2to1.Λ'
      TM0Route.PartrecStack TM0Route.PartrecStackSymbol
      (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
      TM0Route.PartrecVar :=
  Turing.TM2to1.Λ'.normal
    (TM0Route.StartedLabel.wrap (NatPartrecToToPartrec.translate c)
      (PartrecToTM2Support.startLabel (NatPartrecToToPartrec.translate c)))

def sourceStatementOne (c : Code) :
    Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar) :=
  some (TM0Route.partrecStartedTM1Machine
    (NatPartrecToToPartrec.translate c) (sourceStartedTM1StartLabel c))

theorem sourceStatementAt_one (c : Code) :
    TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) 1 =
      some (sourceStatementOne c) := by
  simpa [sourceStatementOne, sourceStartedTM1StartLabel] using
    TM0Route.partrecStartedTM0StatementAt?_one (NatPartrecToToPartrec.translate c)

theorem sourceStatementAt?_exists_of_lt
    {c : Code} {i : Nat} (hi : i < sourceStatementCount c) :
    ∃ stmt,
      TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) i = some stmt := by
  rw [TM0Route.partrecStartedTM0StatementAt?_eq_getElem?]
  have hlen :
      i < (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).length := by
    simpa [sourceStatementCount, TM0Route.partrecStartedTM0StatementList_length] using hi
  exact ⟨(TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c))[i]'hlen, List.getElem?_eq_getElem hlen⟩

theorem sourceLabelAtByStatementStartWithSearchCode?_of_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    TM0FoldedCompiler.labelAtByStatementFromWithSearchCode?
        (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i =
      some (((((none : Option (Turing.TM1.Stmt
          (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
          (Turing.TM2to1.Λ'
            TM0Route.PartrecStack TM0Route.PartrecStackSymbol
            (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
            TM0Route.PartrecVar)
          TM0Route.PartrecVar)), v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))),
        TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((none, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))) := by
  exact sourceLabelAtByStatementStartWithSearchCode?_of_split
    (sourceLabelIndexStartSplit?_of_var_get? (c := c) hv) (sourceStatementAt_zero c)

theorem sourceLabelAtByStatementStartWithSearchCode?_of_one_add_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    TM0FoldedCompiler.labelAtByStatementFromWithSearchCode?
        (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0
        (TM0Route.partrecVarList.length + i) =
      some ((((sourceStatementOne c, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))),
        TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((sourceStatementOne c, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))) := by
  exact sourceLabelAtByStatementStartWithSearchCode?_of_split
    (sourceLabelIndexStartSplit?_of_one_add_var_get? (c := c) hv) (sourceStatementAt_one c)

theorem sourceLabelAtByStatementFromWithPositionCode?_of_split
    {c : Code} {fuel k i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hsplit : sourceLabelIndexFromSplit? fuel k i = some (stmtIndex, v))
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) stmtIndex = some stmt) :
    TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) fuel k i =
      some ((((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))),
        TM0FoldedCompiler.labelPositionCode stmtIndex
          (i % TM0Route.partrecVarList.length) stmt v)) := by
  rcases sourceLabelIndexFromSplit?_eq_some hsplit with ⟨hstmtIndex, hblock, hv⟩
  simpa [hstmtIndex] using
    TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_of_div_mod
      (NatPartrecToToPartrec.translate c) hblock hv
      (by simpa [hstmtIndex] using hstmt)

theorem sourceLabelAtByStatementFromWithPositionCode?_of_block_var_get?
    {c : Code} {fuel k block i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hblock : block < fuel)
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) (k + block) = some stmt) :
    TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) fuel k
        (TM0Route.partrecVarList.length * block + i) =
      some ((((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))),
        TM0FoldedCompiler.labelPositionCode (k + block) i stmt v)) := by
  rcases List.getElem?_eq_some_iff.1 hv with ⟨hi, _hget⟩
  have hmod :
      (TM0Route.partrecVarList.length * block + i) %
          TM0Route.partrecVarList.length = i := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hi
  rw [sourceLabelAtByStatementFromWithPositionCode?_of_split
    (sourceLabelIndexFromSplit?_of_block_var_get? hblock hv) hstmt]
  simp [hmod]

theorem sourceLabelAtByStatementStartWithPositionCode?_of_split
    {c : Code} {i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hsplit : sourceLabelIndexStartSplit? c i = some (stmtIndex, v))
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) stmtIndex = some stmt) :
    TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i =
      some ((((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))),
        TM0FoldedCompiler.labelPositionCode stmtIndex
          (i % TM0Route.partrecVarList.length) stmt v)) := by
  unfold sourceLabelIndexStartSplit? at hsplit
  simpa using
    sourceLabelAtByStatementFromWithPositionCode?_of_split hsplit hstmt

theorem sourceLabelAtByStatementFrom?_eq_none_of_start_labelCount_le
    {c : Code} {i : Nat} (hi : sourceLabelCount c ≤ i) :
    TM0Route.partrecStartedTM0LabelAtByStatementFrom?
        (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i =
      none := by
  change TM0Route.partrecStartedTM0LabelAtByStatementFrom?
      (NatPartrecToToPartrec.translate c)
      (TM0Route.partrecStartedTM0StatementCount
        (NatPartrecToToPartrec.translate c)) 0 i = none
  rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero_eq]
  rw [TM0Route.partrecStartedTM0LabelAtByStatement?_eq_labelAt]
  rw [TM0Route.partrecStartedTM0LabelAt?_eq_getElem?]
  rw [List.getElem?_eq_none_iff]
  simpa [sourceLabelCount, TM0Route.partrecStartedTM0LabelList_length] using hi

theorem sourceLabelAtByStatementStartWithPositionCode?_eq_none_of_labelCount_le
    {c : Code} {i : Nat} (hi : sourceLabelCount c ≤ i) :
    TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i =
      none := by
  cases hdecode :
      TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i with
  | none =>
      rfl
  | some q =>
      have hfst :
          TM0Route.partrecStartedTM0LabelAtByStatementFrom?
              (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i =
            some q.1 := by
        simpa [hdecode] using
          (TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_fst_eq
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i).symm
      rw [sourceLabelAtByStatementFrom?_eq_none_of_start_labelCount_le hi] at hfst
      cases hfst

/--
Source-code version of the fully offset descriptor decoder.

This is the computability target that the final reduction actually needs:
before decoding finite TM0 labels, compose the source `Nat.Partrec.Code` with
the fixed translation to Mathlib `ToPartrec.Code`.
-/
def sourceSimStepDataForLabelIndexFrom
    (c : Code) (fuel k i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexFrom
    (NatPartrecToToPartrec.translate c) fuel k i

/--
Source-code version of the fully offset descriptor decoder factored through
numeric folded state codes.
-/
def sourceSimStepDataForLabelIndexFromWithCode
    (c : Code) (fuel k i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
    (NatPartrecToToPartrec.translate c) fuel k i

/--
Source-code version of the fully offset descriptor decoder whose current-state
code is computed by bounded support search.
-/
def sourceSimStepDataForLabelIndexFromWithSearchCode
    (c : Code) (fuel k i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
    (NatPartrecToToPartrec.translate c) fuel k i

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_of_split
    {c : Code} {fuel k i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hsplit : sourceLabelIndexFromSplit? fuel k i = some (stmtIndex, v))
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) stmtIndex = some stmt) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        stmt v := by
  unfold sourceSimStepDataForLabelIndexFromWithSearchCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
  rw [sourceLabelAtByStatementFromWithSearchCode?_of_split hsplit hstmt]
  rfl

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_of_block_var_get?
    {c : Code} {fuel k block i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hblock : block < fuel)
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) (k + block) = some stmt) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k
        (TM0Route.partrecVarList.length * block + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        stmt v := by
  exact sourceSimStepDataForLabelIndexFromWithSearchCode_of_split
    (sourceLabelIndexFromSplit?_of_block_var_get? hblock hv) hstmt

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_zero
    (c : Code) (k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c 0 k i = [] := by
  unfold sourceSimStepDataForLabelIndexFromWithSearchCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
    TM0FoldedCompiler.labelAtByStatementFromWithSearchCode?
  simp [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero]

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_var_none
    {c : Code} {fuel k i : Nat}
    (hv : TM0Route.partrecVarList[i]? = none) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c (fuel + 1) k i =
      sourceSimStepDataForLabelIndexFromWithSearchCode c fuel (k + 1)
        (i - TM0Route.partrecVarList.length) := by
  unfold sourceSimStepDataForLabelIndexFromWithSearchCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
    TM0FoldedCompiler.labelAtByStatementFromWithSearchCode?
  rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_succ]
  simp [hv]

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_none
    {c : Code} {fuel k i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c (fuel + 1) k i = [] := by
  unfold sourceSimStepDataForLabelIndexFromWithSearchCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
    TM0FoldedCompiler.labelAtByStatementFromWithSearchCode?
  rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_succ]
  simp [hv, hstmt]

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_some
    {c : Code} {fuel k i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = some stmt) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c (fuel + 1) k i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        stmt v := by
  simpa using
    sourceSimStepDataForLabelIndexFromWithSearchCode_of_block_var_get?
      (c := c) (fuel := fuel + 1) (k := k) (block := 0)
      (i := i) (v := v) (by omega) hv (by simpa using hstmt)

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_eq_nil_of_statementCount_le
    (c : Code) (fuel k i : Nat) (hk : sourceStatementCount c ≤ k) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k i = [] := by
  induction fuel generalizing k i with
  | zero =>
      exact sourceSimStepDataForLabelIndexFromWithSearchCode_zero c k i
  | succ fuel ih =>
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_var_none
            (c := c) (fuel := fuel) (k := k) (i := i) hv]
          exact ih (k + 1) (i - TM0Route.partrecVarList.length) (by omega)
      | some v =>
          exact sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_none
            (c := c) (fuel := fuel) (k := k) (i := i) (v := v) hv
            (TM0Route.partrecStartedTM0StatementAt?_eq_none_of_count_le
              (NatPartrecToToPartrec.translate c) (by simpa [sourceStatementCount] using hk))

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_statementCount_add
    (c : Code) (fuel offset i : Nat) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c fuel
      (sourceStatementCount c + offset) i = [] :=
  sourceSimStepDataForLabelIndexFromWithSearchCode_eq_nil_of_statementCount_le
    c fuel (sourceStatementCount c + offset) i (Nat.le_add_right _ _)

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_statementCount_add_primrec :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1
        (sourceStatementCount p.1 + p.2.2.1) p.2.2.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourceSimStepDataForLabelIndexFromWithSearchCode_statementCount_add
      p.1 p.2.1 p.2.2.1 p.2.2.2).symm

end TM0FoldedReduction

end LeanWang
