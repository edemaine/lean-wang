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

def sourceSearchCodeOneRowsVar
    (c : Code) (k : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  match TM0Route.partrecStartedTM0StatementAt?
      (NatPartrecToToPartrec.translate c) k with
  | none => []
  | some stmt =>
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
        stmt v

theorem sourceSearchCodeOneRowsVar_stmt_none
    {c : Code} {k : Nat} {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourceSearchCodeOneRowsVar c k v = [] := by
  simp [sourceSearchCodeOneRowsVar, hstmt]

theorem sourceSearchCodeOneRowsVar_eq_nil_of_statementCount_le
    {c : Code} {k : Nat} (v : TM0Route.PartrecVar)
    (hk : sourceStatementCount c ≤ k) :
    sourceSearchCodeOneRowsVar c k v = [] := by
  exact sourceSearchCodeOneRowsVar_stmt_none
    (TM0Route.partrecStartedTM0StatementAt?_eq_none_of_count_le
      (NatPartrecToToPartrec.translate c) (by simpa [sourceStatementCount] using hk))

theorem sourceSearchCodeOneRowsVar_statementCount_add
    (c : Code) (offset : Nat) (v : TM0Route.PartrecVar) :
    sourceSearchCodeOneRowsVar c (sourceStatementCount c + offset) v = [] :=
  sourceSearchCodeOneRowsVar_eq_nil_of_statementCount_le v (Nat.le_add_right _ _)

theorem sourceSearchCodeOneRowsVar_statementCount_add_primrec :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 (sourceStatementCount p.1 + p.2.1) p.2.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourceSearchCodeOneRowsVar_statementCount_add p.1 p.2.1 p.2.2).symm

def sourceSearchCodeInteriorRowsVar
    (c : Code) (j : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  sourceSearchCodeOneRowsVar c (j + 1) v

theorem sourceSearchCodeInteriorRowsVar_primrec_of_oneRows
    (hrows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeInteriorRowsVar p.1 p.2.1 p.2.2) := by
  have hj : Primrec (fun p : Code × Nat × TM0Route.PartrecVar => p.2.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  exact hrows.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair hj (Primrec.snd.comp Primrec.snd)))

def sourceSearchCodeBoundedInteriorRowsVar
    (c : Code) (j : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  if j + 1 < sourceStatementCount c then
    sourceSearchCodeInteriorRowsVar c j v
  else
    []

theorem sourceSearchCodeBoundedInteriorRowsVar_eq_interior
    {c : Code} {j : Nat} {v : TM0Route.PartrecVar}
    (hj : j + 1 < sourceStatementCount c) :
    sourceSearchCodeBoundedInteriorRowsVar c j v =
      sourceSearchCodeInteriorRowsVar c j v := by
  simp [sourceSearchCodeBoundedInteriorRowsVar, hj]

theorem sourceSearchCodeBoundedInteriorRowsVar_eq_nil
    {c : Code} {j : Nat} {v : TM0Route.PartrecVar}
    (hj : ¬ j + 1 < sourceStatementCount c) :
    sourceSearchCodeBoundedInteriorRowsVar c j v = [] := by
  simp [sourceSearchCodeBoundedInteriorRowsVar, hj]

theorem sourceSearchCodeBoundedInteriorRowsVar_primrec_of_interior
    (hinterior : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeInteriorRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 p.2.1 p.2.2) := by
  have hbound : PrimrecPred (fun p : Code × Nat × TM0Route.PartrecVar =>
      p.2.1 + 1 < sourceStatementCount p.1) :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
      (sourceStatementCount_primrec.comp Primrec.fst)
  have hnil : Primrec (fun _p : Code × Nat × TM0Route.PartrecVar =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  exact (Primrec.ite hbound hinterior hnil).of_eq fun p => by
    rfl

theorem sourceSearchCodeOneRowsVar_stmt_some
    {c : Code} {k : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = some stmt) :
    sourceSearchCodeOneRowsVar c k v =
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
  simp [sourceSearchCodeOneRowsVar, hstmt]

theorem sourceSearchCodeOneRowsVar_stmt_some_none
    {c : Code} {k : Nat} {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = some
          (none : Option (Turing.TM1.Stmt
            (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
            (Turing.TM2to1.Λ'
              TM0Route.PartrecStack TM0Route.PartrecStackSymbol
              (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
              TM0Route.PartrecVar)
            TM0Route.PartrecVar))) :
    sourceSearchCodeOneRowsVar c k v = [] := by
  rw [sourceSearchCodeOneRowsVar_stmt_some hstmt]
  exact TM0FoldedCompiler.simStepDataForStmtLabelWithCode_none
    (NatPartrecToToPartrec.translate c)
    (TM0FiniteCompiler.stateCodeBySupportSearch
      (NatPartrecToToPartrec.translate c)
      (TM0Route.partrecStartedTM0StatementCount
        (NatPartrecToToPartrec.translate c))
      (((none : Option (Turing.TM1.Stmt
          (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
          (Turing.TM2to1.Λ'
            TM0Route.PartrecStack TM0Route.PartrecStackSymbol
            (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
            TM0Route.PartrecVar)
          TM0Route.PartrecVar)), v) :
        Turing.TM1to0.Λ'
          (TM0Route.partrecStartedTM1Machine
            (NatPartrecToToPartrec.translate c))))
    v

theorem sourceSearchCodeOneRowsVar_zero
    (c : Code) (v : TM0Route.PartrecVar) :
    sourceSearchCodeOneRowsVar c 0 v = [] := by
  exact sourceSearchCodeOneRowsVar_stmt_some_none (sourceStatementAt_zero c)

theorem sourceSearchCodeOneRowsVar_zero_primrec :
    Primrec (fun p : Code × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 0 p.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourceSearchCodeOneRowsVar_zero p.1 p.2).symm

theorem sourceSearchCodeOneRowsVar_eq_boundedInterior
    (c : Code) (k : Nat) (v : TM0Route.PartrecVar) :
    sourceSearchCodeOneRowsVar c k v =
      if k = 0 then
        []
      else
        sourceSearchCodeBoundedInteriorRowsVar c (k - 1) v := by
  by_cases hzero : k = 0
  · simp [hzero, sourceSearchCodeOneRowsVar_zero]
  · by_cases hlt : k < sourceStatementCount c
    · have hkpred : k - 1 + 1 = k := Nat.sub_one_add_one hzero
      simp [hzero, sourceSearchCodeBoundedInteriorRowsVar,
        sourceSearchCodeInteriorRowsVar, hkpred, hlt]
    · have hle : sourceStatementCount c ≤ k := Nat.le_of_not_gt hlt
      have hrows : sourceSearchCodeOneRowsVar c k v = [] :=
        sourceSearchCodeOneRowsVar_eq_nil_of_statementCount_le v hle
      have hkpred : k - 1 + 1 = k := Nat.sub_one_add_one hzero
      simp [hzero, sourceSearchCodeBoundedInteriorRowsVar, hkpred, hlt, hrows]

theorem sourceSearchCodeOneRowsVar_primrec_of_boundedInterior
    (hinterior : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2) := by
  have hzero : PrimrecPred (fun p : Code × Nat × TM0Route.PartrecVar =>
      p.2.1 = 0) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  have hnil : Primrec (fun _p : Code × Nat × TM0Route.PartrecVar =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hkPred : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      p.2.1 - 1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have helse : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 (p.2.1 - 1) p.2.2) :=
    hinterior.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair hkPred (Primrec.snd.comp Primrec.snd)))
  exact (Primrec.ite hzero hnil helse).of_eq fun p => by
    exact (sourceSearchCodeOneRowsVar_eq_boundedInterior p.1 p.2.1 p.2.2).symm

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_one_eq_varRows
    (c : Code) (k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c 1 k i =
      match TM0Route.partrecVarList[i]? with
      | none => []
      | some v => sourceSearchCodeOneRowsVar c k v := by
  cases hv : TM0Route.partrecVarList[i]? with
  | none =>
      rw [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_var_none
        (c := c) (fuel := 0) (k := k) (i := i) hv]
      simp [sourceSimStepDataForLabelIndexFromWithSearchCode_zero]
  | some v =>
      cases hstmt : TM0Route.partrecStartedTM0StatementAt?
          (NatPartrecToToPartrec.translate c) k with
      | none =>
          rw [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_none
            (c := c) (fuel := 0) (k := k) (i := i) (v := v) hv hstmt]
          simp [sourceSearchCodeOneRowsVar_stmt_none hstmt]
      | some stmt =>
          rw [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_some
            (c := c) (fuel := 0) (k := k) (i := i) (v := v)
            (stmt := stmt) hv hstmt]
          simp [sourceSearchCodeOneRowsVar_stmt_some hstmt]

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_one_zero
    (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c 1 0 i = [] := by
  rw [sourceSimStepDataForLabelIndexFromWithSearchCode_one_eq_varRows]
  cases h : TM0Route.partrecVarList[i]? with
  | none => rfl
  | some v => exact sourceSearchCodeOneRowsVar_zero c v

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_one_zero_primrec :
    Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 0 p.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourceSimStepDataForLabelIndexFromWithSearchCode_one_zero p.1 p.2).symm

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_one_primrec_of_varRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2) := by
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun _p : Code × Nat × Nat =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun v : TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 v) := by
    apply Primrec₂.mk
    exact hvarRows.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    rw [sourceSimStepDataForLabelIndexFromWithSearchCode_one_eq_varRows]
    cases TM0Route.partrecVarList[p.2.2]? <;> rfl

/-- State for the source-level bounded-search descriptor decoder.

The first two fields are the current statement offset and variable-list offset.
The optional row list records that the decoder has already resolved; `none`
means the scan should continue with the next statement block.
-/
abbrev SourceSearchCodeDecoderState :=
  Nat × Nat × Option (List TM0FoldedCompiler.SimStepData)

def sourceSearchCodeDecoderRows (s : SourceSearchCodeDecoderState) :
    List TM0FoldedCompiler.SimStepData :=
  s.2.2.getD []

def sourceSearchCodeDecoderInit (k i : Nat) : SourceSearchCodeDecoderState :=
  (k, i, none)

def sourceSearchCodeDecoderStepVar
    (c : Code) (k i : Nat) (v : TM0Route.PartrecVar) :
    SourceSearchCodeDecoderState :=
  match TM0Route.partrecStartedTM0StatementAt?
      (NatPartrecToToPartrec.translate c) k with
  | none => (k, i, some [])
  | some stmt =>
      (k, i, some
        (TM0FoldedCompiler.simStepDataForStmtLabelWithCode
          (NatPartrecToToPartrec.translate c)
          (TM0FiniteCompiler.stateCodeBySupportSearch
            (NatPartrecToToPartrec.translate c)
            (TM0Route.partrecStartedTM0StatementCount
              (NatPartrecToToPartrec.translate c))
            ((stmt, v) :
              Turing.TM1to0.Λ'
                (TM0Route.partrecStartedTM1Machine
                  (NatPartrecToToPartrec.translate c))))
          stmt v))

def sourceSearchCodeDecoderStepNone (c : Code) (k i : Nat) :
    SourceSearchCodeDecoderState :=
  match TM0Route.partrecVarList[i]? with
  | none => (k + 1, i - TM0Route.partrecVarList.length, none)
  | some v => sourceSearchCodeDecoderStepVar c k i v

def sourceSearchCodeDecoderStepNoneRows (c : Code) (k i : Nat) :
    SourceSearchCodeDecoderState :=
  match TM0Route.partrecVarList[i]? with
  | none => (k + 1, i - TM0Route.partrecVarList.length, none)
  | some _ => (k, i, some (sourceSimStepDataForLabelIndexFromWithSearchCode c 1 k i))

/-- One accumulator step for the source-level bounded-search descriptor decoder. -/
def sourceSearchCodeDecoderStep (c : Code)
    (s : SourceSearchCodeDecoderState) : SourceSearchCodeDecoderState :=
  match s.2.2 with
  | some rows => (s.1, s.2.1, some rows)
  | none => sourceSearchCodeDecoderStepNone c s.1 s.2.1

theorem sourceSearchCodeDecoderStep_resolved
    (c : Code) (k i : Nat) (rows : List TM0FoldedCompiler.SimStepData) :
    sourceSearchCodeDecoderStep c (k, i, some rows) = (k, i, some rows) := by
  rfl

theorem sourceSearchCodeDecoderStep_var_none
    {c : Code} {k i : Nat}
    (hv : TM0Route.partrecVarList[i]? = none) :
    sourceSearchCodeDecoderStep c (k, i, none) =
      (k + 1, i - TM0Route.partrecVarList.length, none) := by
  simp [sourceSearchCodeDecoderStep, sourceSearchCodeDecoderStepNone, hv]

theorem sourceSearchCodeDecoderStep_stmt_none
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourceSearchCodeDecoderStep c (k, i, none) =
      (k, i, some []) := by
  simp [sourceSearchCodeDecoderStep, sourceSearchCodeDecoderStepNone,
    sourceSearchCodeDecoderStepVar, hv, hstmt]

theorem sourceSearchCodeDecoderStep_stmt_some
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
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
    sourceSearchCodeDecoderStep c (k, i, none) =
      (k, i, some
        (TM0FoldedCompiler.simStepDataForStmtLabelWithCode
          (NatPartrecToToPartrec.translate c)
          (TM0FiniteCompiler.stateCodeBySupportSearch
            (NatPartrecToToPartrec.translate c)
            (TM0Route.partrecStartedTM0StatementCount
              (NatPartrecToToPartrec.translate c))
            ((stmt, v) :
              Turing.TM1to0.Λ'
                (TM0Route.partrecStartedTM1Machine
                  (NatPartrecToToPartrec.translate c))))
          stmt v)) := by
  simp [sourceSearchCodeDecoderStep, sourceSearchCodeDecoderStepNone,
    sourceSearchCodeDecoderStepVar, hv, hstmt]

theorem sourceSearchCodeDecoderStepVar_eq_oneRows
    (c : Code) (k i : Nat) (v : TM0Route.PartrecVar) :
    sourceSearchCodeDecoderStepVar c k i v =
      (k, i, some (sourceSearchCodeOneRowsVar c k v)) := by
  unfold sourceSearchCodeDecoderStepVar sourceSearchCodeOneRowsVar
  cases TM0Route.partrecStartedTM0StatementAt? (NatPartrecToToPartrec.translate c) k <;> rfl

theorem sourceSearchCodeDecoderStepVar_primrec_of_oneRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeDecoderStepVar p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hrows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2.2) :=
    hvarRows.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.pair
    (Primrec.fst.comp Primrec.snd)
    (Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.option_some.comp hrows))).of_eq fun p => by
        exact (sourceSearchCodeDecoderStepVar_eq_oneRows
          p.1 p.2.1 p.2.2.1 p.2.2.2).symm

theorem sourceSearchCodeDecoderStepNone_primrec_of_stepVar
    (hvar : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeDecoderStepVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourceSearchCodeDecoderStepNone p.1 p.2.1 p.2.2) := by
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun p : Code × Nat × Nat =>
      (p.2.1 + 1, p.2.2 - TM0Route.partrecVarList.length,
        (none : Option (List TM0FoldedCompiler.SimStepData)))) := by
    exact Primrec.pair
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair
        (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.const TM0Route.partrecVarList.length))
        (Primrec.const (none : Option (List TM0FoldedCompiler.SimStepData))))
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun v : TM0Route.PartrecVar =>
      sourceSearchCodeDecoderStepVar p.1 p.2.1 p.2.2 v) := by
    apply Primrec₂.mk
    exact hvar.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd)))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases h : TM0Route.partrecVarList[p.2.2]? <;>
      simp [sourceSearchCodeDecoderStepNone, h]

theorem sourceSearchCodeDecoderStep_primrec_of_stepNone
    (hnone : Primrec (fun p : Code × Nat × Nat =>
      sourceSearchCodeDecoderStepNone p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2) := by
  have hopt : Primrec (fun p : Code × SourceSearchCodeDecoderState => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hnoneCase : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStepNone p.1 p.2.1 p.2.2.1) := by
    exact hnone.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hsome : Primrec₂
      (fun p : Code × SourceSearchCodeDecoderState =>
        fun rows : List TM0FoldedCompiler.SimStepData =>
          (p.2.1, p.2.2.1, some rows)) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.option_some.comp Primrec.snd))
  exact (Primrec.option_casesOn hopt hnoneCase hsome).of_eq fun p => by
    cases h : p.2.2.2 <;> simp [sourceSearchCodeDecoderStep, h]

theorem sourceSearchCodeDecoderStep_primrec_of_stepVar
    (hvar : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeDecoderStepVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2) :=
  sourceSearchCodeDecoderStep_primrec_of_stepNone
    (sourceSearchCodeDecoderStepNone_primrec_of_stepVar hvar)

theorem sourceSearchCodeDecoderStep_primrec_of_oneVarRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2) :=
  sourceSearchCodeDecoderStep_primrec_of_stepVar
    (sourceSearchCodeDecoderStepVar_primrec_of_oneRows hvarRows)

theorem sourceSearchCodeDecoderStepNone_eq_rows (c : Code) (k i : Nat) :
    sourceSearchCodeDecoderStepNone c k i =
      sourceSearchCodeDecoderStepNoneRows c k i := by
  unfold sourceSearchCodeDecoderStepNone sourceSearchCodeDecoderStepNoneRows
  cases hv : TM0Route.partrecVarList[i]? with
  | none =>
      rfl
  | some v =>
      unfold sourceSearchCodeDecoderStepVar
      cases hstmt : TM0Route.partrecStartedTM0StatementAt?
          (NatPartrecToToPartrec.translate c) k with
      | none =>
          simp [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_none
            (c := c) (fuel := 0) (k := k) (i := i) (v := v) hv hstmt]
      | some stmt =>
          simp [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_some
            (c := c) (fuel := 0) (k := k) (i := i) (v := v)
            (stmt := stmt) hv hstmt]

theorem sourceSearchCodeDecoderStepNone_primrec_of_oneRows
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourceSearchCodeDecoderStepNone p.1 p.2.1 p.2.2) := by
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun p : Code × Nat × Nat =>
      (p.2.1 + 1, p.2.2 - TM0Route.partrecVarList.length,
        (none : Option (List TM0FoldedCompiler.SimStepData)))) := by
    exact Primrec.pair
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair
        (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.const TM0Route.partrecVarList.length))
        (Primrec.const (none : Option (List TM0FoldedCompiler.SimStepData))))
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun _v : TM0Route.PartrecVar =>
      (p.2.1, p.2.2,
        some (sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2))) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp
          (hrows.comp
            (Primrec.pair (Primrec.fst.comp Primrec.fst)
              (Primrec.pair
                (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
                (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))))
  have hrowsStep : Primrec (fun p : Code × Nat × Nat =>
      sourceSearchCodeDecoderStepNoneRows p.1 p.2.1 p.2.2) :=
    (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
      cases h : TM0Route.partrecVarList[p.2.2]? <;>
        simp [sourceSearchCodeDecoderStepNoneRows, h]
  exact hrowsStep.of_eq fun p =>
    (sourceSearchCodeDecoderStepNone_eq_rows p.1 p.2.1 p.2.2).symm

theorem sourceSearchCodeDecoderStep_primrec_of_oneRows
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2) :=
  sourceSearchCodeDecoderStep_primrec_of_stepNone
    (sourceSearchCodeDecoderStepNone_primrec_of_oneRows hrows)

def sourceSearchCodeDecoderStateFrom
    (c : Code) (fuel : Nat) (s : SourceSearchCodeDecoderState) :
    SourceSearchCodeDecoderState :=
  fuel.rec s (fun _ s => sourceSearchCodeDecoderStep c s)

theorem sourceSearchCodeDecoderStateFrom_succ_eq_step
    (c : Code) (fuel : Nat) (s : SourceSearchCodeDecoderState) :
    sourceSearchCodeDecoderStateFrom c (fuel + 1) s =
      sourceSearchCodeDecoderStateFrom c fuel (sourceSearchCodeDecoderStep c s) := by
  induction fuel generalizing s with
  | zero =>
      rfl
  | succ fuel ih =>
      change sourceSearchCodeDecoderStep c
          (sourceSearchCodeDecoderStateFrom c (fuel + 1) s) =
        sourceSearchCodeDecoderStep c
          (sourceSearchCodeDecoderStateFrom c fuel
          (sourceSearchCodeDecoderStep c s))
      rw [ih]

theorem sourceSearchCodeDecoderStateFrom_resolved
    (c : Code) (fuel k i : Nat) (rows : List TM0FoldedCompiler.SimStepData) :
    sourceSearchCodeDecoderStateFrom c fuel (k, i, some rows) =
      (k, i, some rows) := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      change sourceSearchCodeDecoderStep c
          (sourceSearchCodeDecoderStateFrom c fuel (k, i, some rows)) =
        (k, i, some rows)
      rw [ih]
      exact sourceSearchCodeDecoderStep_resolved c k i rows

theorem sourceSearchCodeDecoderRows_stateFrom_none_eq
    (c : Code) (fuel k i : Nat) :
    sourceSearchCodeDecoderRows
        (sourceSearchCodeDecoderStateFrom c fuel (k, i, none)) =
      sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k i := by
  induction fuel generalizing k i with
  | zero =>
      simp [sourceSearchCodeDecoderStateFrom, sourceSearchCodeDecoderRows,
        sourceSimStepDataForLabelIndexFromWithSearchCode_zero]
  | succ fuel ih =>
      rw [sourceSearchCodeDecoderStateFrom_succ_eq_step]
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [sourceSearchCodeDecoderStep_var_none hv]
          rw [ih]
          rw [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_var_none hv]
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt?
              (NatPartrecToToPartrec.translate c) k with
          | none =>
              rw [sourceSearchCodeDecoderStep_stmt_none hv hstmt]
              rw [sourceSearchCodeDecoderStateFrom_resolved]
              simp [sourceSearchCodeDecoderRows,
                sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_none hv hstmt]
          | some stmt =>
              rw [sourceSearchCodeDecoderStep_stmt_some hv hstmt]
              rw [sourceSearchCodeDecoderStateFrom_resolved]
              simp [sourceSearchCodeDecoderRows,
                sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_some
                  hv hstmt]

def sourceSearchCodeDecoderState (c : Code) (fuel k i : Nat) :
    SourceSearchCodeDecoderState :=
  sourceSearchCodeDecoderStateFrom c fuel (sourceSearchCodeDecoderInit k i)

def sourceSearchCodeDecoder (c : Code) (fuel k i : Nat) :
    List TM0FoldedCompiler.SimStepData :=
  sourceSearchCodeDecoderRows (sourceSearchCodeDecoderState c fuel k i)

theorem sourceSearchCodeDecoderRows_primrec :
    Primrec sourceSearchCodeDecoderRows := by
  unfold sourceSearchCodeDecoderRows
  have hopt : Primrec (fun s : SourceSearchCodeDecoderState => s.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hnone : Primrec (fun _s : SourceSearchCodeDecoderState =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂
      (fun _s : SourceSearchCodeDecoderState =>
        fun rows : List TM0FoldedCompiler.SimStepData => rows) :=
    Primrec₂.right
  exact (Primrec.option_casesOn hopt hnone hsome).of_eq fun s => by
    cases s.2.2 <;> rfl

set_option maxHeartbeats 800000 in
-- The final equality unfolds the `nat_rec'` accumulator over nested product projections.
theorem sourceSearchCodeDecoder_primrec_of_step
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSearchCodeDecoder p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let fuel : Code × Nat × Nat × Nat → Nat := fun p => p.2.1
  let kFn : Code × Nat × Nat × Nat → Nat := fun p => p.2.2.1
  let iFn : Code × Nat × Nat × Nat → Nat := fun p => p.2.2.2
  have hfuel : Primrec fuel := Primrec.fst.comp Primrec.snd
  have hk : Primrec kFn := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec iFn := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hbase : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSearchCodeDecoderInit (kFn p) (iFn p)) := by
    unfold sourceSearchCodeDecoderInit
    exact Primrec.pair hk (Primrec.pair hi (Primrec.const none))
  have hiterStep : Primrec₂
      (fun p : Code × Nat × Nat × Nat =>
        fun s : Nat × SourceSearchCodeDecoderState =>
          sourceSearchCodeDecoderStep p.1 s.2) := by
    apply Primrec₂.mk
    exact hstep.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
  have hstate : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSearchCodeDecoderState p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    exact (Primrec.nat_rec' hfuel hbase hiterStep).of_eq fun p => by
      unfold sourceSearchCodeDecoderState sourceSearchCodeDecoderInit fuel kFn iFn
      rfl
  exact (sourceSearchCodeDecoderRows_primrec.comp hstate).of_eq fun p => by
    unfold sourceSearchCodeDecoder
    rfl

theorem sourceSearchCodeDecoder_primrec_of_oneVarRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSearchCodeDecoder p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  sourceSearchCodeDecoder_primrec_of_step
    (sourceSearchCodeDecoderStep_primrec_of_oneVarRows hvarRows)

theorem sourceSearchCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithSearchCode
    (c : Code) (fuel k i : Nat) :
    sourceSearchCodeDecoder c fuel k i =
      sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k i := by
  unfold sourceSearchCodeDecoder sourceSearchCodeDecoderState sourceSearchCodeDecoderInit
  exact sourceSearchCodeDecoderRows_stateFrom_none_eq c fuel k i

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_decoder_step
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  (sourceSearchCodeDecoder_primrec_of_step hstep).of_eq fun p =>
    sourceSearchCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithSearchCode
      p.1 p.2.1 p.2.2.1 p.2.2.2

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_oneVarRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_decoder_step
    (sourceSearchCodeDecoderStep_primrec_of_oneVarRows hvarRows)

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_oneRows
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_decoder_step
    (sourceSearchCodeDecoderStep_primrec_of_oneRows hrows)

/--
Source-code version of the offset descriptor decoder whose current-state code
is the explicit statement/variable position.
-/
def sourceSimStepDataForLabelIndexFromWithPositionCode
    (c : Code) (fuel k i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
    (NatPartrecToToPartrec.translate c) fuel k i

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_of_split
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
    sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode stmtIndex
          (i % TM0Route.partrecVarList.length) stmt v) stmt v := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
  rw [sourceLabelAtByStatementFromWithPositionCode?_of_split hsplit hstmt]
  rfl

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_of_block_var_get?
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
    sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k
        (TM0Route.partrecVarList.length * block + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode (k + block) i stmt v) stmt v := by
  rw [sourceSimStepDataForLabelIndexFromWithPositionCode_of_split
    (sourceLabelIndexFromSplit?_of_block_var_get? hblock hv) hstmt]
  rcases List.getElem?_eq_some_iff.1 hv with ⟨hi, _hget⟩
  have hmod :
      (TM0Route.partrecVarList.length * block + i) %
          TM0Route.partrecVarList.length = i := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hi
  simp [hmod]

def sourcePositionCodeOneRowsIndexVar
    (c : Code) (k i : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  match TM0Route.partrecStartedTM0StatementAt?
      (NatPartrecToToPartrec.translate c) k with
  | none => []
  | some stmt =>
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode k i stmt v)
        stmt v

theorem sourcePositionCodeOneRowsIndexVar_stmt_none
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourcePositionCodeOneRowsIndexVar c k i v = [] := by
  simp [sourcePositionCodeOneRowsIndexVar, hstmt]

theorem sourcePositionCodeOneRowsIndexVar_eq_nil_of_statementCount_le
    {c : Code} {k i : Nat} (v : TM0Route.PartrecVar)
    (hk : sourceStatementCount c ≤ k) :
    sourcePositionCodeOneRowsIndexVar c k i v = [] := by
  exact sourcePositionCodeOneRowsIndexVar_stmt_none
    (TM0Route.partrecStartedTM0StatementAt?_eq_none_of_count_le
      (NatPartrecToToPartrec.translate c) (by simpa [sourceStatementCount] using hk))

theorem sourcePositionCodeOneRowsIndexVar_statementCount_add
    (c : Code) (offset i : Nat) (v : TM0Route.PartrecVar) :
    sourcePositionCodeOneRowsIndexVar c (sourceStatementCount c + offset) i v = [] :=
  sourcePositionCodeOneRowsIndexVar_eq_nil_of_statementCount_le v
    (Nat.le_add_right _ _)

theorem sourcePositionCodeOneRowsIndexVar_statementCount_add_primrec :
    Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1
        (sourceStatementCount p.1 + p.2.1) p.2.2.1 p.2.2.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourcePositionCodeOneRowsIndexVar_statementCount_add
      p.1 p.2.1 p.2.2.1 p.2.2.2).symm

theorem sourcePositionCodeOneRowsIndexVar_stmt_some
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = some stmt) :
    sourcePositionCodeOneRowsIndexVar c k i v =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode k i stmt v)
        stmt v := by
  simp [sourcePositionCodeOneRowsIndexVar, hstmt]

theorem sourcePositionCodeOneRowsIndexVar_zero
    (c : Code) (i : Nat) (v : TM0Route.PartrecVar) :
    sourcePositionCodeOneRowsIndexVar c 0 i v = [] := by
  rw [sourcePositionCodeOneRowsIndexVar_stmt_some (sourceStatementAt_zero c)]
  exact TM0FoldedCompiler.simStepDataForStmtLabelWithCode_none
    (NatPartrecToToPartrec.translate c)
    (TM0FoldedCompiler.labelPositionCode 0 i
      (none : Option (Turing.TM1.Stmt
        (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
        (Turing.TM2to1.Λ'
          TM0Route.PartrecStack TM0Route.PartrecStackSymbol
          (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
          TM0Route.PartrecVar)
        TM0Route.PartrecVar))
      v)
    v

theorem sourcePositionCodeOneRowsIndexVar_zero_primrec :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 0 p.2.1 p.2.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourcePositionCodeOneRowsIndexVar_zero p.1 p.2.1 p.2.2).symm

def sourcePositionCodeInteriorRowsIndexVar
    (c : Code) (j i : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  sourcePositionCodeOneRowsIndexVar c (j + 1) i v

theorem sourcePositionCodeInteriorRowsIndexVar_primrec_of_oneRows
    (hrows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hj : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar => p.2.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  exact hrows.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair hj
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

def sourcePositionCodeBoundedInteriorRowsIndexVar
    (c : Code) (j i : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  if j + 1 < sourceStatementCount c then
    sourcePositionCodeInteriorRowsIndexVar c j i v
  else
    []

theorem sourcePositionCodeBoundedInteriorRowsIndexVar_eq_interior
    {c : Code} {j i : Nat} {v : TM0Route.PartrecVar}
    (hj : j + 1 < sourceStatementCount c) :
    sourcePositionCodeBoundedInteriorRowsIndexVar c j i v =
      sourcePositionCodeInteriorRowsIndexVar c j i v := by
  simp [sourcePositionCodeBoundedInteriorRowsIndexVar, hj]

theorem sourcePositionCodeBoundedInteriorRowsIndexVar_eq_nil
    {c : Code} {j i : Nat} {v : TM0Route.PartrecVar}
    (hj : ¬ j + 1 < sourceStatementCount c) :
    sourcePositionCodeBoundedInteriorRowsIndexVar c j i v = [] := by
  simp [sourcePositionCodeBoundedInteriorRowsIndexVar, hj]

theorem sourcePositionCodeBoundedInteriorRowsIndexVar_primrec_of_interior
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hbound : PrimrecPred (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      p.2.1 + 1 < sourceStatementCount p.1) :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
      (sourceStatementCount_primrec.comp Primrec.fst)
  have hnil : Primrec (fun _p : Code × Nat × Nat × TM0Route.PartrecVar =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  exact (Primrec.ite hbound hinterior hnil).of_eq fun p => by
    rfl

theorem sourcePositionCodeOneRowsIndexVar_eq_boundedInterior
    (c : Code) (k i : Nat) (v : TM0Route.PartrecVar) :
    sourcePositionCodeOneRowsIndexVar c k i v =
      if k = 0 then
        []
      else
        sourcePositionCodeBoundedInteriorRowsIndexVar c (k - 1) i v := by
  by_cases hzero : k = 0
  · simp [hzero, sourcePositionCodeOneRowsIndexVar_zero]
  · by_cases hlt : k < sourceStatementCount c
    · have hkpred : k - 1 + 1 = k := Nat.sub_one_add_one hzero
      simp [hzero, sourcePositionCodeBoundedInteriorRowsIndexVar,
        sourcePositionCodeInteriorRowsIndexVar, hkpred, hlt]
    · have hle : sourceStatementCount c ≤ k := Nat.le_of_not_gt hlt
      have hrows : sourcePositionCodeOneRowsIndexVar c k i v = [] :=
        sourcePositionCodeOneRowsIndexVar_eq_nil_of_statementCount_le v hle
      have hkpred : k - 1 + 1 = k := Nat.sub_one_add_one hzero
      simp [hzero, sourcePositionCodeBoundedInteriorRowsIndexVar, hkpred, hlt, hrows]

theorem sourcePositionCodeOneRowsIndexVar_primrec_of_boundedInterior
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hzero : PrimrecPred (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      p.2.1 = 0) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  have hnil : Primrec (fun _p : Code × Nat × Nat × TM0Route.PartrecVar =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hkPred : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      p.2.1 - 1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have helse : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar p.1 (p.2.1 - 1) p.2.2.1 p.2.2.2) :=
    hinterior.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair hkPred
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact (Primrec.ite hzero hnil helse).of_eq fun p => by
    exact (sourcePositionCodeOneRowsIndexVar_eq_boundedInterior
      p.1 p.2.1 p.2.2.1 p.2.2.2).symm

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_one_eq_indexVarRows
    (c : Code) (k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c 1 k i =
      match TM0Route.partrecVarList[i]? with
      | none => []
      | some v => sourcePositionCodeOneRowsIndexVar c k i v := by
  cases hv : TM0Route.partrecVarList[i]? with
  | none =>
      unfold sourceSimStepDataForLabelIndexFromWithPositionCode
        TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
      rw [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_succ_of_var_none
        (tc := NatPartrecToToPartrec.translate c) (fuel := 0) (k := k) (i := i) hv]
      simp [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_zero]
  | some v =>
      change sourceSimStepDataForLabelIndexFromWithPositionCode c 1 k i =
        sourcePositionCodeOneRowsIndexVar c k i v
      cases hstmt : TM0Route.partrecStartedTM0StatementAt?
          (NatPartrecToToPartrec.translate c) k with
      | none =>
          unfold sourceSimStepDataForLabelIndexFromWithPositionCode
            TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
          rw [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_succ_of_stmt_none
            (tc := NatPartrecToToPartrec.translate c) (fuel := 0)
            (k := k) (i := i) (v := v) hv hstmt]
          simp [sourcePositionCodeOneRowsIndexVar_stmt_none hstmt]
      | some stmt =>
          rw [sourcePositionCodeOneRowsIndexVar_stmt_some hstmt]
          simpa using
            sourceSimStepDataForLabelIndexFromWithPositionCode_of_block_var_get?
              (c := c) (fuel := 1) (k := k) (block := 0)
              (i := i) (v := v) (stmt := stmt) (by omega) hv (by simpa using hstmt)

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_one_primrec_of_indexVarRows
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 1 p.2.1 p.2.2) := by
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun _p : Code × Nat × Nat =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun v : TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2 v) := by
    apply Primrec₂.mk
    exact hvarRows.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd)))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    rw [sourceSimStepDataForLabelIndexFromWithPositionCode_one_eq_indexVarRows]
    cases TM0Route.partrecVarList[p.2.2]? <;> rfl

def sourcePositionCodeDecoderStepNone (c : Code) (k i : Nat) :
    SourceSearchCodeDecoderState :=
  match TM0Route.partrecVarList[i]? with
  | none => (k + 1, i - TM0Route.partrecVarList.length, none)
  | some v => (k, i, some (sourcePositionCodeOneRowsIndexVar c k i v))

def sourcePositionCodeDecoderStep (c : Code)
    (s : SourceSearchCodeDecoderState) : SourceSearchCodeDecoderState :=
  match s.2.2 with
  | some rows => (s.1, s.2.1, some rows)
  | none => sourcePositionCodeDecoderStepNone c s.1 s.2.1

theorem sourcePositionCodeDecoderStep_resolved
    (c : Code) (k i : Nat) (rows : List TM0FoldedCompiler.SimStepData) :
    sourcePositionCodeDecoderStep c (k, i, some rows) = (k, i, some rows) := by
  rfl

theorem sourcePositionCodeDecoderStep_var_none
    {c : Code} {k i : Nat}
    (hv : TM0Route.partrecVarList[i]? = none) :
    sourcePositionCodeDecoderStep c (k, i, none) =
      (k + 1, i - TM0Route.partrecVarList.length, none) := by
  simp [sourcePositionCodeDecoderStep, sourcePositionCodeDecoderStepNone, hv]

theorem sourcePositionCodeDecoderStep_stmt_none
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourcePositionCodeDecoderStep c (k, i, none) =
      (k, i, some []) := by
  simp [sourcePositionCodeDecoderStep, sourcePositionCodeDecoderStepNone, hv,
    sourcePositionCodeOneRowsIndexVar_stmt_none hstmt]

theorem sourcePositionCodeDecoderStep_stmt_some
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
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
    sourcePositionCodeDecoderStep c (k, i, none) =
      (k, i, some
        (TM0FoldedCompiler.simStepDataForStmtLabelWithCode
          (NatPartrecToToPartrec.translate c)
          (TM0FoldedCompiler.labelPositionCode k i stmt v) stmt v)) := by
  simp [sourcePositionCodeDecoderStep, sourcePositionCodeDecoderStepNone, hv,
    sourcePositionCodeOneRowsIndexVar_stmt_some hstmt]

theorem sourcePositionCodeDecoderStepNone_primrec_of_indexVarRows
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourcePositionCodeDecoderStepNone p.1 p.2.1 p.2.2) := by
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun p : Code × Nat × Nat =>
      (p.2.1 + 1, p.2.2 - TM0Route.partrecVarList.length,
        (none : Option (List TM0FoldedCompiler.SimStepData)))) := by
    exact Primrec.pair
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair
        (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.const TM0Route.partrecVarList.length))
        (Primrec.const (none : Option (List TM0FoldedCompiler.SimStepData))))
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun v : TM0Route.PartrecVar =>
      (p.2.1, p.2.2, some (sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2 v))) := by
    apply Primrec₂.mk
    have hrow : Primrec (fun p : (Code × Nat × Nat) × TM0Route.PartrecVar =>
        sourcePositionCodeOneRowsIndexVar p.1.1 p.1.2.1 p.1.2.2 p.2) :=
      hvarRows.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.pair
              (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
              Primrec.snd)))
    exact Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp hrow))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases h : TM0Route.partrecVarList[p.2.2]? <;>
      simp [sourcePositionCodeDecoderStepNone, h]

theorem sourcePositionCodeDecoderStep_primrec_of_stepNone
    (hnone : Primrec (fun p : Code × Nat × Nat =>
      sourcePositionCodeDecoderStepNone p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2) := by
  have hopt : Primrec (fun p : Code × SourceSearchCodeDecoderState => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hnoneCase : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStepNone p.1 p.2.1 p.2.2.1) := by
    exact hnone.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hsome : Primrec₂
      (fun p : Code × SourceSearchCodeDecoderState =>
        fun rows : List TM0FoldedCompiler.SimStepData =>
          (p.2.1, p.2.2.1, some rows)) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.option_some.comp Primrec.snd))
  exact (Primrec.option_casesOn hopt hnoneCase hsome).of_eq fun p => by
    cases h : p.2.2.2 <;> simp [sourcePositionCodeDecoderStep, h]

theorem sourcePositionCodeDecoderStep_primrec_of_indexVarRows
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2) :=
  sourcePositionCodeDecoderStep_primrec_of_stepNone
    (sourcePositionCodeDecoderStepNone_primrec_of_indexVarRows hvarRows)

set_option linter.style.longLine false in
/--
Primitive recursiveness of the source-specialized position-code label-index
decoder is enough for the generated position-code accumulator step.

This avoids asking for primitive recursiveness of
`sourcePositionCodeOneRowsIndexVar` at arbitrary numeric variable slots.  The
accumulator step only uses slots that successfully decode through the fixed
`partrecVarList`, and in that branch the one-row payload is exactly the
`fuel = 1` position-code label-index decoder.
-/
theorem sourcePositionCodeDecoderStep_primrec_of_labelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2) := by
  apply sourcePositionCodeDecoderStep_primrec_of_stepNone
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun p : Code × Nat × Nat =>
      (p.2.1 + 1, p.2.2 - TM0Route.partrecVarList.length,
        (none : Option (List TM0FoldedCompiler.SimStepData)))) := by
    exact Primrec.pair
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair
        (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.const TM0Route.partrecVarList.length))
        (Primrec.const (none : Option (List TM0FoldedCompiler.SimStepData))))
  have hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 1 p.2.1 p.2.2) :=
    hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.const 1) Primrec.snd))
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun _v : TM0Route.PartrecVar =>
      (p.2.1, p.2.2,
        some (sourceSimStepDataForLabelIndexFromWithPositionCode p.1 1 p.2.1 p.2.2))) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp (hrows.comp Primrec.fst)))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases h : TM0Route.partrecVarList[p.2.2]? with
    | none =>
        simp [sourcePositionCodeDecoderStepNone, h]
    | some v =>
        simp [sourcePositionCodeDecoderStepNone, h,
          sourceSimStepDataForLabelIndexFromWithPositionCode_one_eq_indexVarRows]

def sourcePositionCodeDecoderStateFrom
    (c : Code) (fuel : Nat) (s : SourceSearchCodeDecoderState) :
    SourceSearchCodeDecoderState :=
  fuel.rec s (fun _ s => sourcePositionCodeDecoderStep c s)

theorem sourcePositionCodeDecoderStateFrom_succ_eq_step
    (c : Code) (fuel : Nat) (s : SourceSearchCodeDecoderState) :
    sourcePositionCodeDecoderStateFrom c (fuel + 1) s =
      sourcePositionCodeDecoderStateFrom c fuel (sourcePositionCodeDecoderStep c s) := by
  induction fuel generalizing s with
  | zero =>
      rfl
  | succ fuel ih =>
      change sourcePositionCodeDecoderStep c
          (sourcePositionCodeDecoderStateFrom c (fuel + 1) s) =
        sourcePositionCodeDecoderStep c
          (sourcePositionCodeDecoderStateFrom c fuel
          (sourcePositionCodeDecoderStep c s))
      rw [ih]

theorem sourcePositionCodeDecoderStateFrom_resolved
    (c : Code) (fuel k i : Nat) (rows : List TM0FoldedCompiler.SimStepData) :
    sourcePositionCodeDecoderStateFrom c fuel (k, i, some rows) =
      (k, i, some rows) := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      change sourcePositionCodeDecoderStep c
          (sourcePositionCodeDecoderStateFrom c fuel (k, i, some rows)) =
        (k, i, some rows)
      rw [ih]
      exact sourcePositionCodeDecoderStep_resolved c k i rows

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_zero
    (c : Code) (k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c 0 k i = [] := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
  simp [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_zero]

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_var_none
    {c : Code} {fuel k i : Nat}
    (hv : TM0Route.partrecVarList[i]? = none) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) k i =
      sourceSimStepDataForLabelIndexFromWithPositionCode c fuel
        (k + 1) (i - TM0Route.partrecVarList.length) := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
  rw [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_succ_of_var_none
    (tc := NatPartrecToToPartrec.translate c) hv]

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_stmt_none
    {c : Code} {fuel k i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) k i = [] := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
  rw [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_succ_of_stmt_none
    (tc := NatPartrecToToPartrec.translate c) hv hstmt]
  rfl

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_stmt_some
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
    sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) k i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode k i stmt v) stmt v := by
  simpa using
    sourceSimStepDataForLabelIndexFromWithPositionCode_of_block_var_get?
      (c := c) (fuel := fuel + 1) (k := k) (block := 0)
      (i := i) (v := v) (stmt := stmt) (by omega) hv (by simpa using hstmt)

theorem sourcePositionCodeDecoderRows_stateFrom_none_eq
    (c : Code) (fuel k i : Nat) :
    sourceSearchCodeDecoderRows
        (sourcePositionCodeDecoderStateFrom c fuel (k, i, none)) =
      sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i := by
  induction fuel generalizing k i with
  | zero =>
      simp [sourcePositionCodeDecoderStateFrom, sourceSearchCodeDecoderRows,
        sourceSimStepDataForLabelIndexFromWithPositionCode_zero]
  | succ fuel ih =>
      rw [sourcePositionCodeDecoderStateFrom_succ_eq_step]
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [sourcePositionCodeDecoderStep_var_none hv]
          rw [ih]
          rw [sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_var_none hv]
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt?
              (NatPartrecToToPartrec.translate c) k with
          | none =>
              rw [sourcePositionCodeDecoderStep_stmt_none hv hstmt]
              rw [sourcePositionCodeDecoderStateFrom_resolved]
              simp [sourceSearchCodeDecoderRows,
                sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_stmt_none
                  hv hstmt]
          | some stmt =>
              rw [sourcePositionCodeDecoderStep_stmt_some hv hstmt]
              rw [sourcePositionCodeDecoderStateFrom_resolved]
              simp [sourceSearchCodeDecoderRows,
                sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_stmt_some
                  hv hstmt]

def sourcePositionCodeDecoderState (c : Code) (fuel k i : Nat) :
    SourceSearchCodeDecoderState :=
  sourcePositionCodeDecoderStateFrom c fuel (sourceSearchCodeDecoderInit k i)

def sourcePositionCodeDecoder (c : Code) (fuel k i : Nat) :
    List TM0FoldedCompiler.SimStepData :=
  sourceSearchCodeDecoderRows (sourcePositionCodeDecoderState c fuel k i)

set_option maxHeartbeats 800000 in
-- The accumulator proof expands a nested `nat_rec'` over product-coded decoder state.
theorem sourcePositionCodeDecoder_primrec_of_step
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourcePositionCodeDecoder p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let fuel : Code × Nat × Nat × Nat → Nat := fun p => p.2.1
  let kFn : Code × Nat × Nat × Nat → Nat := fun p => p.2.2.1
  let iFn : Code × Nat × Nat × Nat → Nat := fun p => p.2.2.2
  have hfuel : Primrec fuel := Primrec.fst.comp Primrec.snd
  have hk : Primrec kFn := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec iFn := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hbase : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSearchCodeDecoderInit (kFn p) (iFn p)) := by
    unfold sourceSearchCodeDecoderInit
    exact Primrec.pair hk (Primrec.pair hi (Primrec.const none))
  have hiterStep : Primrec₂
      (fun p : Code × Nat × Nat × Nat =>
        fun s : Nat × SourceSearchCodeDecoderState =>
          sourcePositionCodeDecoderStep p.1 s.2) := by
    apply Primrec₂.mk
    exact hstep.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
  have hstate : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourcePositionCodeDecoderState p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    exact (Primrec.nat_rec' hfuel hbase hiterStep).of_eq fun p => by
      unfold sourcePositionCodeDecoderState sourceSearchCodeDecoderInit fuel kFn iFn
      rfl
  exact (sourceSearchCodeDecoderRows_primrec.comp hstate).of_eq fun p => by
    unfold sourcePositionCodeDecoder
    rfl

theorem sourcePositionCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithPositionCode
    (c : Code) (fuel k i : Nat) :
    sourcePositionCodeDecoder c fuel k i =
      sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i := by
  unfold sourcePositionCodeDecoder sourcePositionCodeDecoderState sourceSearchCodeDecoderInit
  exact sourcePositionCodeDecoderRows_stateFrom_none_eq c fuel k i

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_decoder_step
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  (sourcePositionCodeDecoder_primrec_of_step hstep).of_eq fun p =>
    sourcePositionCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithPositionCode
      p.1 p.2.1 p.2.2.1 p.2.2.2

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_indexVarRows
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_decoder_step
    (sourcePositionCodeDecoderStep_primrec_of_indexVarRows hvarRows)

/--
The source-uniform primitive-recursion target for one generated position-code
row.  This is the nondependent boundary where the translated source statement
lookup has already been turned into concrete folded TM0 descriptor rows.
-/
abbrev SourcePositionCodeOneRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
    sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Primitive-recursion target for the generated position-code accumulator step. -/
abbrev SourcePositionCodeDecoderStepPrimrec : Prop :=
  Primrec (fun p : Code × SourceSearchCodeDecoderState =>
    sourcePositionCodeDecoderStep p.1 p.2)

set_option linter.style.longLine false in
/-- Primitive-recursion target for the global position-code label-index decoder. -/
abbrev GlobalPositionCodeLabelIndexFromPrimrec : Prop :=
  Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
      p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Primitive-recursion target for interior generated position-code rows. -/
abbrev SourcePositionCodeInteriorRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
    sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Primitive-recursion target for bounded interior generated position-code rows. -/
abbrev SourcePositionCodeBoundedInteriorRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
    sourcePositionCodeBoundedInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)

/--
The statement-list uniqueness fact needed to identify support-search state
codes with position-coded state codes for the translated source TM0 machines.
-/
abbrev SourceStatementListNodup : Prop :=
  ∀ c : Code,
    (TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c)).Nodup

/-- Source-uniform one-row position-code decoder plus statement uniqueness. -/
structure SourcePositionCodeOneRowsWithStatementNodup : Prop where
  rows : SourcePositionCodeOneRowsPrimrec
  statementList_nodup : SourceStatementListNodup

/-- Source-uniform bounded-interior position-code decoder plus statement uniqueness. -/
structure SourcePositionCodeBoundedInteriorRowsWithStatementNodup : Prop where
  rows : SourcePositionCodeBoundedInteriorRowsPrimrec
  statementList_nodup : SourceStatementListNodup

/-- Source-uniform interior position-code decoder plus statement uniqueness. -/
structure SourcePositionCodeInteriorRowsWithStatementNodup : Prop where
  rows : SourcePositionCodeInteriorRowsPrimrec
  statementList_nodup : SourceStatementListNodup

/-- One-row generated position-code rows give the interior-row target. -/
theorem sourcePositionCodeInteriorRowsPrimrec_of_oneRows
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    SourcePositionCodeInteriorRowsPrimrec :=
  sourcePositionCodeInteriorRowsIndexVar_primrec_of_oneRows hrows

/-- Interior generated position-code rows give the bounded-interior target. -/
theorem sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeBoundedInteriorRowsPrimrec :=
  sourcePositionCodeBoundedInteriorRowsIndexVar_primrec_of_interior hinterior

/-- Bounded interior generated position-code rows give the one-row target. -/
theorem sourcePositionCodeOneRowsPrimrec_of_boundedInterior
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    SourcePositionCodeOneRowsPrimrec :=
  sourcePositionCodeOneRowsIndexVar_primrec_of_boundedInterior hbounded

/-- Interior generated position-code rows give the one-row target. -/
theorem sourcePositionCodeOneRowsPrimrec_of_interior
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeOneRowsPrimrec :=
  sourcePositionCodeOneRowsPrimrec_of_boundedInterior
    (sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior hinterior)

/-- A one-row package also supplies the interior package. -/
def sourcePositionCodeInteriorRowsWithStatementNodup_of_oneRows
    (hrows : SourcePositionCodeOneRowsWithStatementNodup) :
    SourcePositionCodeInteriorRowsWithStatementNodup where
  rows := sourcePositionCodeInteriorRowsPrimrec_of_oneRows hrows.rows
  statementList_nodup := hrows.statementList_nodup

/-- An interior package also supplies the bounded-interior package. -/
def sourcePositionCodeBoundedInteriorRowsWithStatementNodup_of_interior
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup) :
    SourcePositionCodeBoundedInteriorRowsWithStatementNodup where
  rows := sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior hinterior.rows
  statementList_nodup := hinterior.statementList_nodup

/-- A bounded-interior package also supplies the one-row package. -/
def sourcePositionCodeOneRowsWithStatementNodup_of_boundedInterior
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithStatementNodup) :
    SourcePositionCodeOneRowsWithStatementNodup where
  rows := sourcePositionCodeOneRowsPrimrec_of_boundedInterior hbounded.rows
  statementList_nodup := hbounded.statementList_nodup

/-- An interior package also supplies the one-row package. -/
def sourcePositionCodeOneRowsWithStatementNodup_of_interior
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup) :
    SourcePositionCodeOneRowsWithStatementNodup :=
  sourcePositionCodeOneRowsWithStatementNodup_of_boundedInterior
    (sourcePositionCodeBoundedInteriorRowsWithStatementNodup_of_interior
      hinterior)

/-- Source-code version of the canonical offset-start descriptor decoder. -/
def sourceSimStepDataForLabelIndexStart
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStart
    (NatPartrecToToPartrec.translate c) i

/-- Source-code version of the canonical numeric-state offset-start decoder. -/
def sourceSimStepDataForLabelIndexStartWithCode
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode
    (NatPartrecToToPartrec.translate c) i

/-- Source-code version of the canonical bounded-search offset-start decoder. -/
def sourceSimStepDataForLabelIndexStartWithSearchCode
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode
    (NatPartrecToToPartrec.translate c) i

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_of_split
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
    sourceSimStepDataForLabelIndexStartWithSearchCode c i =
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
  unfold sourceSimStepDataForLabelIndexStartWithSearchCode
    TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode
  change sourceSimStepDataForLabelIndexFromWithSearchCode c
      (sourceStatementCount c) 0 i =
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
      stmt v
  unfold sourceLabelIndexStartSplit? at hsplit
  exact sourceSimStepDataForLabelIndexFromWithSearchCode_of_split hsplit hstmt

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_of_block_var_get?
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
    sourceSimStepDataForLabelIndexStartWithSearchCode c
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
  exact sourceSimStepDataForLabelIndexStartWithSearchCode_of_split
    (sourceLabelIndexStartSplit?_of_block_var_get? (c := c) hblock hv) hstmt

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_of_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithSearchCode c i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((none, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        (none : Option (Turing.TM1.Stmt
          (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
          (Turing.TM2to1.Λ'
            TM0Route.PartrecStack TM0Route.PartrecStackSymbol
            (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
            TM0Route.PartrecVar)
          TM0Route.PartrecVar))
        v := by
  exact sourceSimStepDataForLabelIndexStartWithSearchCode_of_split
    (sourceLabelIndexStartSplit?_of_var_get? (c := c) hv) (sourceStatementAt_zero c)

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_of_one_add_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithSearchCode c
        (TM0Route.partrecVarList.length + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((sourceStatementOne c, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        (sourceStatementOne c) v := by
  exact sourceSimStepDataForLabelIndexStartWithSearchCode_of_split
    (sourceLabelIndexStartSplit?_of_one_add_var_get? (c := c) hv) (sourceStatementAt_one c)

/-- Source-code version of the canonical position-coded offset-start decoder. -/
def sourceSimStepDataForLabelIndexStartWithPositionCode
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
    (NatPartrecToToPartrec.translate c) i

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_split
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
    sourceSimStepDataForLabelIndexStartWithPositionCode c i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode stmtIndex
          (i % TM0Route.partrecVarList.length) stmt v) stmt v := by
  unfold sourceSimStepDataForLabelIndexStartWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
  change sourceSimStepDataForLabelIndexFromWithPositionCode c
      (sourceStatementCount c) 0 i =
    TM0FoldedCompiler.simStepDataForStmtLabelWithCode
      (NatPartrecToToPartrec.translate c)
      (TM0FoldedCompiler.labelPositionCode stmtIndex
        (i % TM0Route.partrecVarList.length) stmt v) stmt v
  unfold sourceLabelIndexStartSplit? at hsplit
  exact sourceSimStepDataForLabelIndexFromWithPositionCode_of_split hsplit hstmt

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_block_var_get?
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
    sourceSimStepDataForLabelIndexStartWithPositionCode c
        (TM0Route.partrecVarList.length * block + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode block i stmt v) stmt v := by
  rcases List.getElem?_eq_some_iff.1 hv with ⟨hi, _hget⟩
  have hmod :
      (TM0Route.partrecVarList.length * block + i) %
          TM0Route.partrecVarList.length = i := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hi
  rw [sourceSimStepDataForLabelIndexStartWithPositionCode_of_split
    (sourceLabelIndexStartSplit?_of_block_var_get? (c := c) hblock hv) hstmt]
  simp [hmod]

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode 0 i
          (none : Option (Turing.TM1.Stmt
            (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
            (Turing.TM2to1.Λ'
              TM0Route.PartrecStack TM0Route.PartrecStackSymbol
              (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
              TM0Route.PartrecVar)
            TM0Route.PartrecVar)) v)
        (none : Option (Turing.TM1.Stmt
          (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
          (Turing.TM2to1.Λ'
            TM0Route.PartrecStack TM0Route.PartrecStackSymbol
            (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
            TM0Route.PartrecVar)
          TM0Route.PartrecVar))
        v := by
  simpa using
    sourceSimStepDataForLabelIndexStartWithPositionCode_of_block_var_get?
      (c := c) (block := 0) (i := i) (v := v)
      (sourceStatementCount_pos c) hv (sourceStatementAt_zero c)

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_one_add_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c
        (TM0Route.partrecVarList.length + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode 1 i (sourceStatementOne c) v)
        (sourceStatementOne c) v := by
  simpa [Nat.mul_one] using
    sourceSimStepDataForLabelIndexStartWithPositionCode_of_block_var_get?
      (c := c) (block := 1) (i := i) (v := v)
      (sourceStatementCount_one_lt c) hv (sourceStatementAt_one c)

/-- Source-code version of the semantic label-index descriptor decoder. -/
def sourceSimStepDataForLabelIndex
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndex
    (NatPartrecToToPartrec.translate c) i

/-- Source-code indexed descriptor list for the folded finite-TM0 reduction. -/
def sourceSimStepDataByLabelIndex (c : Code) : List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndex c)

/-- Source-code indexed descriptor list through the numeric-state decoder path. -/
def sourceSimStepDataByLabelIndexWithCode (c : Code) :
    List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndexStartWithCode c)

/-- Source-code indexed descriptor list through the bounded-search decoder path. -/
def sourceSimStepDataByLabelIndexWithSearchCode (c : Code) :
    List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndexStartWithSearchCode c)

/-- Source-code indexed descriptor list through the position-coded decoder path. -/
def sourceSimStepDataByLabelIndexWithPositionCode (c : Code) :
    List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndexStartWithPositionCode c)

theorem sourceSimStepDataForLabelIndexStart_eq (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStart c i =
      sourceSimStepDataForLabelIndex c i := by
  unfold sourceSimStepDataForLabelIndexStart sourceSimStepDataForLabelIndex
  exact TM0FoldedCompiler.simStepDataForLabelIndexStart_eq
    (NatPartrecToToPartrec.translate c) i

theorem sourceSimStepDataForLabelIndexStartWithCode_eq (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStartWithCode c i =
      sourceSimStepDataForLabelIndex c i := by
  unfold sourceSimStepDataForLabelIndexStartWithCode sourceSimStepDataForLabelIndex
  exact TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode_eq
    (NatPartrecToToPartrec.translate c) i

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_eq_withCode
    (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStartWithSearchCode c i =
      sourceSimStepDataForLabelIndexStartWithCode c i := by
  unfold sourceSimStepDataForLabelIndexStartWithSearchCode
    sourceSimStepDataForLabelIndexStartWithCode
  exact TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode_eq_withCode
    (NatPartrecToToPartrec.translate c) i

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_eq (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c i =
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
        (NatPartrecToToPartrec.translate c) i :=
  rfl

theorem sourceSimStepDataForLabelIndexFrom_eq_withCode
    (c : Code) (fuel k i : Nat) :
    sourceSimStepDataForLabelIndexFrom c fuel k i =
      sourceSimStepDataForLabelIndexFromWithCode c fuel k i := by
  unfold sourceSimStepDataForLabelIndexFrom sourceSimStepDataForLabelIndexFromWithCode
  exact TM0FoldedCompiler.simStepDataForLabelIndexFrom_eq_withCode
    (NatPartrecToToPartrec.translate c) fuel k i

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_eq_withCode
    (c : Code) (fuel k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k i =
      sourceSimStepDataForLabelIndexFromWithCode c fuel k i := by
  unfold sourceSimStepDataForLabelIndexFromWithSearchCode
    sourceSimStepDataForLabelIndexFromWithCode
  exact TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode_eq_withCode
    (NatPartrecToToPartrec.translate c) fuel k i

theorem sourceSimStepDataByLabelIndex_eq (c : Code) :
    sourceSimStepDataByLabelIndex c = sourceSimStepData c := by
  unfold sourceSimStepDataByLabelIndex sourceSimStepData sourceSimStepDataForLabelIndex
  exact TM0FoldedCompiler.simStepDataByLabelIndex_eq
    (NatPartrecToToPartrec.translate c)

theorem sourceSimStepDataByLabelIndexWithCode_eq (c : Code) :
    sourceSimStepDataByLabelIndexWithCode c = sourceSimStepData c := by
  unfold sourceSimStepDataByLabelIndexWithCode sourceSimStepData
  exact TM0FoldedCompiler.simStepDataByLabelIndexWithCode_eq
    (NatPartrecToToPartrec.translate c)

theorem sourceSimStepDataByLabelIndexWithSearchCode_eq (c : Code) :
    sourceSimStepDataByLabelIndexWithSearchCode c = sourceSimStepData c := by
  unfold sourceSimStepDataByLabelIndexWithSearchCode sourceSimStepData
  exact TM0FoldedCompiler.simStepDataByLabelIndexWithSearchCode_eq
    (NatPartrecToToPartrec.translate c)

theorem sourceSimStepDataByLabelIndexWithPositionCode_eq (c : Code) :
    sourceSimStepDataByLabelIndexWithPositionCode c =
      TM0FoldedCompiler.simStepDataByLabelIndexWithPositionCode
        (NatPartrecToToPartrec.translate c) := by
  rfl

theorem sourceSimStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal
    (c : Code)
    (hmin : ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    sourceSimStepDataByLabelIndexWithPositionCode c =
      sourceSimStepDataByLabelIndexWithCode c := by
  change TM0FoldedCompiler.simStepDataByLabelIndexWithPositionCode
      (NatPartrecToToPartrec.translate c) =
    TM0FoldedCompiler.simStepDataByLabelIndexWithCode
      (NatPartrecToToPartrec.translate c)
  exact
    TM0FoldedCompiler.simStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal
      (NatPartrecToToPartrec.translate c) hmin

theorem sourceSimRowsOfStepDataByLabelIndexWithPositionCode_eq_of_minimal
    (c : Code)
    (hmin : ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    TM0FoldedCompiler.simRowsOfStepData
        (sourceSimStepDataByLabelIndexWithPositionCode c) =
      TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c) := by
  rw [sourceSimStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal c hmin]
  rw [sourceSimStepDataByLabelIndexWithCode_eq c]
  rw [sourceSimStepData_eq c]
  exact (TM0FoldedCompiler.simRows_eq_stepData
    (NatPartrecToToPartrec.translate c)).symm

/--
Primitive recursiveness of the translated source-level offset decoder is enough
for the source-level indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndex_primrec_of_source_labelIndexFrom
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndex := by
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStart p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFrom p.1
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (sourceStatementCount_primrec.comp Primrec.fst)
          (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStart sourceSimStepDataForLabelIndexFrom
        TM0FoldedCompiler.simStepDataForLabelIndexStart
      rfl
  have hlabel : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndex p.1 p.2) :=
    hstart.of_eq fun p => sourceSimStepDataForLabelIndexStart_eq p.1 p.2
  unfold sourceSimStepDataByLabelIndex
  refine Primrec.list_flatMap
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hlabel

/--
Primitive recursiveness of the source-level canonical numeric-state decoder is
enough for the source-level numeric-state indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexStartWithCode
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Primrec sourceSimStepDataByLabelIndexWithCode := by
  unfold sourceSimStepDataByLabelIndexWithCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

/--
Primitive recursiveness of the source-level bounded-search start decoder is
enough for the source-level bounded-search indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_start
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Primrec sourceSimStepDataByLabelIndexWithSearchCode := by
  unfold sourceSimStepDataByLabelIndexWithSearchCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

/--
Primitive recursiveness of the source-level position-coded start decoder is
enough for the source-level position-coded indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_start
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithPositionCode p.1 p.2)) :
    Primrec sourceSimStepDataByLabelIndexWithPositionCode := by
  unfold sourceSimStepDataByLabelIndexWithPositionCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

/--
Primitive recursiveness of the source-level numeric-state offset decoder is
enough for primitive recursiveness of the source-level numeric-state indexed
descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexFromWithCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndexWithCode := by
  apply sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexStartWithCode
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFromWithCode p.1
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (sourceStatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStartWithCode
        sourceSimStepDataForLabelIndexFromWithCode
        TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode
      rfl
  exact hstart

/--
Primitive recursiveness of the source-level bounded-search offset decoder is
enough for primitive recursiveness of the source-level bounded-search indexed
descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_from
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndexWithSearchCode := by
  apply sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_start
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFromWithSearchCode p.1
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (sourceStatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStartWithSearchCode
        sourceSimStepDataForLabelIndexFromWithSearchCode
        TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode
      rfl
  exact hstart

/--
Primitive recursiveness of the source-level position-coded offset decoder is
enough for primitive recursiveness of the source-level position-coded indexed
descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_from
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndexWithPositionCode := by
  apply sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_start
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithPositionCode p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFromWithPositionCode p.1
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (sourceStatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStartWithPositionCode
        sourceSimStepDataForLabelIndexFromWithPositionCode
        TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
      rfl
  exact hstart

/--
The older global offset-decoder target implies the source-specific decoder
target by precomposing with the `Nat.Partrec.Code` translation.
-/
theorem sourceSimStepDataForLabelIndexFrom_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFrom
        rfl

/--
The source-level numeric-state offset decoder implies the source-level semantic
offset decoder by the data-level `WithCode` factoring theorem.
-/
theorem sourceSimStepDataForLabelIndexFrom_primrec_of_source_withCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  hindex.of_eq fun p =>
    (sourceSimStepDataForLabelIndexFrom_eq_withCode p.1 p.2.1 p.2.2.1 p.2.2.2).symm

/--
The older global numeric-state offset-decoder target implies the source-specific
numeric-state decoder target by precomposing with the source translation.
-/
theorem sourceSimStepDataForLabelIndexFromWithCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFromWithCode
        rfl

/--
The older global bounded-search offset-decoder target implies the
source-specific bounded-search decoder target by precomposing with the source
translation.
-/
theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFromWithSearchCode
        rfl

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFromWithPositionCode
        rfl

set_option linter.style.longLine false in
/--
The global position-code label-index decoder target implies the generated
source-code accumulator-step target used by the preferred final route.
-/
theorem sourcePositionCodeDecoderStep_primrec_of_global_labelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2) :=
  sourcePositionCodeDecoderStep_primrec_of_labelIndexFromWithPositionCode
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global hindex)

set_option linter.style.longLine false in
/-- Named version of `sourcePositionCodeDecoderStep_primrec_of_global_labelIndexFromWithPositionCode`. -/
theorem sourcePositionCodeDecoderStepPrimrec_of_globalPositionCodeLabelIndexFromPrimrec
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  sourcePositionCodeDecoderStep_primrec_of_global_labelIndexFromWithPositionCode hindex

theorem sourceLabelAtByStatementFromWithPositionCode_code_mem_states
    {c : Code} {fuel k i : Nat}
    {q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat}
    (h : TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) fuel k i = some q) :
    q.2 ∈ TM0Route.partrecStartedTM0States (NatPartrecToToPartrec.translate c) :=
  TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_code_mem_states
    (NatPartrecToToPartrec.translate c) h

theorem sourceLabelAtByStatementFromWithPositionCode_support_get?
    {c : Code} {fuel k i : Nat}
    {q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat}
    (h : TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) fuel k i = some q) :
    (TM0Route.partrecStartedTM0LabelSupportList
        (NatPartrecToToPartrec.translate c))[q.2]? = some q.1 :=
  TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_support_get?
    (NatPartrecToToPartrec.translate c) h

theorem sourceLabelAtByStatementFromWithPositionCode_minimal_of_statementList_nodup
    {c : Code} {fuel k i : Nat}
    (hnodup : (TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c)).Nodup)
    {q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat}
    (h : TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) fuel k i = some q) :
    ∀ m, m < q.2 →
      (TM0Route.partrecStartedTM0LabelSupportList
        (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1 :=
  TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_minimal_of_statementList_nodup
    (NatPartrecToToPartrec.translate c) hnodup h

theorem sourceLabelSupportList_get_position_of_statementAt?
    {c : Code} {block i : Nat}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) block = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    (TM0Route.partrecStartedTM0LabelSupportList
      (NatPartrecToToPartrec.translate c))[
        1 + block * TM0Route.partrecVarList.length + i]? =
      some ((stmt, v) :
        Turing.TM1to0.Λ'
          (TM0Route.partrecStartedTM1Machine
            (NatPartrecToToPartrec.translate c))) :=
  TM0Route.partrecStartedTM0LabelSupportList_get_position_of_statementAt?
    (NatPartrecToToPartrec.translate c) hstmt hv

theorem sourcePosition_mem_states_of_statementAt?
    {c : Code} {block i : Nat}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) block = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    1 + block * TM0Route.partrecVarList.length + i ∈
      TM0Route.partrecStartedTM0States (NatPartrecToToPartrec.translate c) :=
  TM0Route.partrecStartedTM0_position_mem_states_of_statementAt?
    (NatPartrecToToPartrec.translate c) hstmt hv

theorem sourceStateCodeBySupportSearch_eq_stateCode_of_statementAt?
    {c : Code} {block i : Nat}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) block = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    TM0FiniteCompiler.stateCodeBySupportSearch
        (NatPartrecToToPartrec.translate c)
        (sourceStatementCount c)
        ((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))) =
      TM0FiniteCompiler.stateCode
        (NatPartrecToToPartrec.translate c)
        ((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))) := by
  apply TM0FiniteCompiler.stateCodeBySupportSearch_eq_stateCode
  exact List.mem_iff_getElem?.2
    ⟨1 + block * TM0Route.partrecVarList.length + i,
      sourceLabelSupportList_get_position_of_statementAt? hstmt hv⟩

theorem sourceSearchCodeOneRowsVar_eq_positionCodeOneRowsIndexVar_of_statementList_nodup
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    (hnodup : (TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c)).Nodup)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSearchCodeOneRowsVar c k v =
      sourcePositionCodeOneRowsIndexVar c k i v := by
  cases hstmt : TM0Route.partrecStartedTM0StatementAt?
      (NatPartrecToToPartrec.translate c) k with
  | none =>
      rw [sourceSearchCodeOneRowsVar_stmt_none hstmt,
        sourcePositionCodeOneRowsIndexVar_stmt_none hstmt]
  | some stmt =>
      rw [sourceSearchCodeOneRowsVar_stmt_some hstmt,
        sourcePositionCodeOneRowsIndexVar_stmt_some hstmt]
      have hsearch := sourceStateCodeBySupportSearch_eq_stateCode_of_statementAt?
        (c := c) (block := k) (i := i) (v := v) hstmt hv
      have hmin :
          ∀ m, m < TM0FoldedCompiler.labelPositionCode k i stmt v →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠
                some ((stmt, v) :
                  Turing.TM1to0.Λ'
                    (TM0Route.partrecStartedTM1Machine
                      (NatPartrecToToPartrec.translate c))) :=
        TM0FoldedCompiler.labelPositionCode_minimal_of_statementList_nodup
          (NatPartrecToToPartrec.translate c) hnodup hstmt hv
      have hposition :
          TM0FoldedCompiler.labelPositionCode k i stmt v =
            TM0FiniteCompiler.stateCode
              (NatPartrecToToPartrec.translate c)
              ((stmt, v) :
                Turing.TM1to0.Λ'
                  (TM0Route.partrecStartedTM1Machine
                    (NatPartrecToToPartrec.translate c))) :=
        TM0FoldedCompiler.labelPositionCode_eq_stateCode_of_minimal
          (NatPartrecToToPartrec.translate c) hstmt hv hmin
      have hcode :
          TM0FiniteCompiler.stateCodeBySupportSearch
              (NatPartrecToToPartrec.translate c)
              (sourceStatementCount c)
              ((stmt, v) :
                Turing.TM1to0.Λ'
                  (TM0Route.partrecStartedTM1Machine
                    (NatPartrecToToPartrec.translate c))) =
            TM0FoldedCompiler.labelPositionCode k i stmt v :=
        hsearch.trans hposition.symm
      exact congrArg
        (fun qCode => TM0FoldedCompiler.simStepDataForStmtLabelWithCode
          (NatPartrecToToPartrec.translate c) qCode stmt v) hcode

theorem sourceSearchCodeBoundedInteriorRowsVar_eq_positionCodeBoundedInteriorRowsIndexVar
    {c : Code} {j i : Nat} {v : TM0Route.PartrecVar}
    (hnodup : (TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c)).Nodup)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSearchCodeBoundedInteriorRowsVar c j v =
      sourcePositionCodeBoundedInteriorRowsIndexVar c j i v := by
  by_cases hlt : j + 1 < sourceStatementCount c
  · rw [sourceSearchCodeBoundedInteriorRowsVar_eq_interior hlt,
      sourcePositionCodeBoundedInteriorRowsIndexVar_eq_interior hlt]
    exact sourceSearchCodeOneRowsVar_eq_positionCodeOneRowsIndexVar_of_statementList_nodup
      (c := c) (k := j + 1) (i := i) (v := v) hnodup hv
  · rw [sourceSearchCodeBoundedInteriorRowsVar_eq_nil hlt,
      sourcePositionCodeBoundedInteriorRowsIndexVar_eq_nil hlt]

theorem sourceSearchCodeInteriorRowsVar_eq_positionCodeInteriorRowsIndexVar
    {c : Code} {j i : Nat} {v : TM0Route.PartrecVar}
    (hnodup : (TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c)).Nodup)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSearchCodeInteriorRowsVar c j v =
      sourcePositionCodeInteriorRowsIndexVar c j i v :=
  sourceSearchCodeOneRowsVar_eq_positionCodeOneRowsIndexVar_of_statementList_nodup
    (c := c) (k := j + 1) (i := i) (v := v) hnodup hv

def sourcePartrecVarIndex (v : TM0Route.PartrecVar) : Nat :=
  TM0Route.partrecVarList.findIdx fun w => decide (w = v)

theorem sourcePartrecVarIndex_primrec : Primrec sourcePartrecVarIndex := by
  unfold sourcePartrecVarIndex
  exact Primrec.list_findIdx₁ (l := TM0Route.partrecVarList)
    (Primrec.beq.comp₂ Primrec₂.right Primrec₂.left)

theorem sourcePartrecVarIndex_getElem? (v : TM0Route.PartrecVar) :
    TM0Route.partrecVarList[sourcePartrecVarIndex v]? = some v := by
  unfold sourcePartrecVarIndex
  have hmem : v ∈ TM0Route.partrecVarList := TM0Route.mem_partrecVarList v
  have hidx : TM0Route.partrecVarList.findIdx (fun w => decide (w = v)) <
      TM0Route.partrecVarList.length := by
    exact List.findIdx_lt_length_of_exists ⟨v, hmem, by simp⟩
  have hfind := (List.findIdx_eq (xs := TM0Route.partrecVarList)
    (p := fun w => decide (w = v)) hidx).1 rfl
  exact List.getElem?_eq_some_iff.2 ⟨hidx, of_decide_eq_true hfind.1⟩

theorem sourceSearchCodeOneRowsVar_primrec_of_positionCodeOneRows
    (hrows : SourcePositionCodeOneRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2) := by
  have hidx : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePartrecVarIndex p.2.2) :=
    sourcePartrecVarIndex_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hposition : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar
        p.1 p.2.1 (sourcePartrecVarIndex p.2.2) p.2.2) :=
    hrows.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair hidx (Primrec.snd.comp Primrec.snd))))
  exact hposition.of_eq fun p => by
    have hv :
        TM0Route.partrecVarList[sourcePartrecVarIndex p.2.2]? =
          some p.2.2 :=
      sourcePartrecVarIndex_getElem? p.2.2
    exact (sourceSearchCodeOneRowsVar_eq_positionCodeOneRowsIndexVar_of_statementList_nodup
      (c := p.1) (k := p.2.1) (i := sourcePartrecVarIndex p.2.2)
      (v := p.2.2) (hnodup p.1) hv).symm

set_option linter.style.longLine false in
/--
The generated position-code accumulator step computes the bounded-search
one-row branch on the valid Partrec-variable index path.

This is weaker than `SourcePositionCodeOneRowsPrimrec`, which intentionally
keeps the numeric position-code slot independent of the variable.  It is
nevertheless the exact bridge needed to compare the generated position-code
decoder with the older bounded-search source presentation.
-/
theorem sourceSearchCodeOneRowsVar_primrec_of_positionCodeDecoderStep
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hnodup : SourceStatementListNodup) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2) := by
  have hidx : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePartrecVarIndex p.2.2) :=
    sourcePartrecVarIndex_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hinput : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      (p.2.1, sourcePartrecVarIndex p.2.2,
        (none : Option (List TM0FoldedCompiler.SimStepData)))) :=
    Primrec.pair
      (Primrec.fst.comp Primrec.snd)
      (Primrec.pair hidx (Primrec.const none))
  have hstate : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeDecoderStep p.1
        (p.2.1, sourcePartrecVarIndex p.2.2,
          (none : Option (List TM0FoldedCompiler.SimStepData)))) :=
    hstep.comp (Primrec.pair Primrec.fst hinput)
  have hrows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeDecoderRows
        (sourcePositionCodeDecoderStep p.1
          (p.2.1, sourcePartrecVarIndex p.2.2,
            (none : Option (List TM0FoldedCompiler.SimStepData))))) :=
    sourceSearchCodeDecoderRows_primrec.comp hstate
  exact hrows.of_eq fun p => by
    have hv :
        TM0Route.partrecVarList[sourcePartrecVarIndex p.2.2]? =
          some p.2.2 :=
      sourcePartrecVarIndex_getElem? p.2.2
    simpa only [sourceSearchCodeDecoderRows, sourcePositionCodeDecoderStep,
      sourcePositionCodeDecoderStepNone, hv, Option.getD_some] using
      (sourceSearchCodeOneRowsVar_eq_positionCodeOneRowsIndexVar_of_statementList_nodup
      (c := p.1) (k := p.2.1) (i := sourcePartrecVarIndex p.2.2)
      (v := p.2.2) (hnodup p.1) hv).symm

theorem sourceSearchCodeBoundedInteriorRowsVar_primrec_of_positionCodeBoundedInteriorRows
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 p.2.1 p.2.2) := by
  have hidx : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePartrecVarIndex p.2.2) :=
    sourcePartrecVarIndex_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hposition : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar
        p.1 p.2.1 (sourcePartrecVarIndex p.2.2) p.2.2) :=
    hinterior.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair hidx (Primrec.snd.comp Primrec.snd))))
  exact hposition.of_eq fun p => by
    have hv :
        TM0Route.partrecVarList[sourcePartrecVarIndex p.2.2]? =
          some p.2.2 :=
      sourcePartrecVarIndex_getElem? p.2.2
    exact (sourceSearchCodeBoundedInteriorRowsVar_eq_positionCodeBoundedInteriorRowsIndexVar
      (c := p.1) (j := p.2.1) (i := sourcePartrecVarIndex p.2.2)
      (v := p.2.2) (hnodup p.1) hv).symm

theorem sourceSearchCodeInteriorRowsVar_primrec_of_positionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeInteriorRowsVar p.1 p.2.1 p.2.2) := by
  have hidx : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePartrecVarIndex p.2.2) :=
    sourcePartrecVarIndex_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hposition : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar
        p.1 p.2.1 (sourcePartrecVarIndex p.2.2) p.2.2) :=
    hinterior.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair hidx (Primrec.snd.comp Primrec.snd))))
  exact hposition.of_eq fun p => by
    have hv :
        TM0Route.partrecVarList[sourcePartrecVarIndex p.2.2]? =
          some p.2.2 :=
      sourcePartrecVarIndex_getElem? p.2.2
    exact (sourceSearchCodeInteriorRowsVar_eq_positionCodeInteriorRowsIndexVar
      (c := p.1) (j := p.2.1) (i := sourcePartrecVarIndex p.2.2)
      (v := p.2.2) (hnodup p.1) hv).symm

theorem sourceSimStepDataForLabelIndexStartWithCode_of_block_var_get?
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
    sourceSimStepDataForLabelIndexStartWithCode c
        (TM0Route.partrecVarList.length * block + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCode
          (NatPartrecToToPartrec.translate c)
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        stmt v := by
  rw [← sourceSimStepDataForLabelIndexStartWithSearchCode_eq_withCode]
  rw [sourceSimStepDataForLabelIndexStartWithSearchCode_of_block_var_get?
    (c := c) (block := block) (i := i) (v := v) hblock hv hstmt]
  have hcode := sourceStateCodeBySupportSearch_eq_stateCode_of_statementAt?
    (c := c) (block := block) (i := i) (v := v) hstmt hv
  simpa [sourceStatementCount] using congrArg
    (fun n => TM0FoldedCompiler.simStepDataForStmtLabelWithCode
      (NatPartrecToToPartrec.translate c) n stmt v) hcode

theorem sourceSimStepDataForLabelIndexStartWithCode_of_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithCode c i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCode
          (NatPartrecToToPartrec.translate c)
          (((none : Option (Turing.TM1.Stmt
            (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
            (Turing.TM2to1.Λ'
              TM0Route.PartrecStack TM0Route.PartrecStackSymbol
              (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
              TM0Route.PartrecVar)
            TM0Route.PartrecVar)), v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        (none : Option (Turing.TM1.Stmt
          (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
          (Turing.TM2to1.Λ'
            TM0Route.PartrecStack TM0Route.PartrecStackSymbol
            (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
            TM0Route.PartrecVar)
          TM0Route.PartrecVar))
        v := by
  simpa using
    sourceSimStepDataForLabelIndexStartWithCode_of_block_var_get?
      (c := c) (block := 0) (i := i) (v := v)
      (sourceStatementCount_pos c) hv (sourceStatementAt_zero c)

theorem sourceSimStepDataForLabelIndexStartWithCode_of_one_add_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithCode c
        (TM0Route.partrecVarList.length + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCode
          (NatPartrecToToPartrec.translate c)
          ((sourceStatementOne c, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        (sourceStatementOne c) v := by
  simpa [Nat.mul_one] using
    sourceSimStepDataForLabelIndexStartWithCode_of_block_var_get?
      (c := c) (block := 1) (i := i) (v := v)
      (sourceStatementCount_one_lt c) hv (sourceStatementAt_one c)

theorem sourceLabelAtByStatementFromWithPositionCode_eq_stateCode_of_minimal
    {c : Code} {fuel k i : Nat}
    (hmin : ∀ q :
        TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
      TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
          (NatPartrecToToPartrec.translate c) fuel k i = some q →
        ∀ m, m < q.2 →
          (TM0Route.partrecStartedTM0LabelSupportList
            (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) fuel k i =
      TM0FoldedCompiler.labelAtByStatementFromWithStateCode?
        (NatPartrecToToPartrec.translate c) fuel k i :=
  TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_eq_stateCode_of_minimal
    (NatPartrecToToPartrec.translate c) hmin

theorem sourceMem_simStepDataForLabelIndexFromWithPositionCode_current_support_get?
    {c : Code} {fuel k i : Nat}
    {p : TM0FoldedCompiler.SimStepData}
    (h : p ∈ sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i) :
    ∃ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
      TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
          (NatPartrecToToPartrec.translate c) fuel k i = some q ∧
        p.2.2.1 = q.2 ∧
        (TM0Route.partrecStartedTM0LabelSupportList
          (NatPartrecToToPartrec.translate c))[p.2.2.1]? = some q.1 := by
  exact TM0FoldedCompiler.mem_simStepDataForLabelIndexFromWithPositionCode_current_support_get? h

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_eq_withCode_of_minimal
    {c : Code} {fuel k i : Nat}
    (hmin : ∀ q :
        TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
      TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
          (NatPartrecToToPartrec.translate c) fuel k i = some q →
        ∀ m, m < q.2 →
          (TM0Route.partrecStartedTM0LabelSupportList
            (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i =
      sourceSimStepDataForLabelIndexFromWithCode c fuel k i := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    sourceSimStepDataForLabelIndexFromWithCode
  exact
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode_eq_withCode_of_minimal
      (NatPartrecToToPartrec.translate c) hmin

theorem sourceSimStepDataForLabelIndexFromWithCode_primrec_of_source_searchCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  hindex.of_eq fun p =>
    sourceSimStepDataForLabelIndexFromWithSearchCode_eq_withCode
      p.1 p.2.1 p.2.2.1 p.2.2.2

/--
Global primitive recursiveness of the canonical numeric-state decoder implies
the source-specific canonical numeric-state decoder target by precomposing with
the source-code translation.
-/
theorem sourceSimStepDataForLabelIndexStartWithCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexStartWithCode
        rfl

/--
Global primitive recursiveness of the folded descriptor list is enough for the
source-level normalized folded program-data map used by the final reduction.
-/
theorem sourceProgramData_computable_of_global_simStepData
    (hsteps : Primrec TM0FoldedCompiler.simStepData) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepData hsteps).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_simStepData'
    (hsteps : Primrec TM0FoldedCompiler.simStepData) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_simStepData hsteps).of_eq fun _ => rfl

-- The source-level indexed descriptor list is enough for computability of the
-- normalized folded finite-TM0 program data used by the final reduction.
set_option maxHeartbeats 800000 in
-- The final equality unfolds normalized program data and the descriptor rows.
theorem sourceProgramData_computable_of_source_simStepDataByLabelIndex
    (hsteps : Primrec sourceSimStepDataByLabelIndex) :
    Computable sourceProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (sourceStateCount c)
        (sourceSimStepDataByLabelIndex c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        sourceStateCount_primrec
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourceProgramData sourceStateCount TM0FoldedCompiler.programData
      TM0FoldedCompiler.programDataOfStepData
    rw [sourceSimStepDataByLabelIndex_eq c]
    rw [sourceSimStepData_eq c]
    rw [← TM0FoldedCompiler.simRows_eq_stepData
      (NatPartrecToToPartrec.translate c)]).to_comp

set_option maxHeartbeats 800000 in
-- The final equality unfolds normalized program data and the descriptor rows.
theorem sourceProgramData_computable_of_source_simStepDataByLabelIndexWithCode
    (hsteps : Primrec sourceSimStepDataByLabelIndexWithCode) :
    Computable sourceProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (sourceStateCount c)
        (sourceSimStepDataByLabelIndexWithCode c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        sourceStateCount_primrec
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourceProgramData sourceStateCount TM0FoldedCompiler.programData
      TM0FoldedCompiler.programDataOfStepData
    rw [sourceSimStepDataByLabelIndexWithCode_eq c]
    rw [sourceSimStepData_eq c]
    rw [← TM0FoldedCompiler.simRows_eq_stepData
      (NatPartrecToToPartrec.translate c)]).to_comp

set_option maxHeartbeats 800000 in
-- The bounded-search indexed descriptor list is definitionally canonical after
-- the search-code row equality.
theorem sourceProgramData_computable_of_source_simStepDataByLabelIndexWithSearchCode
    (hsteps : Primrec sourceSimStepDataByLabelIndexWithSearchCode) :
    Computable sourceProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (sourceStateCount c)
        (sourceSimStepDataByLabelIndexWithSearchCode c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        sourceStateCount_primrec
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourceProgramData sourceStateCount TM0FoldedCompiler.programData
      TM0FoldedCompiler.programDataOfStepData
    rw [sourceSimStepDataByLabelIndexWithSearchCode_eq c]
    rw [sourceSimStepData_eq c]
    rw [← TM0FoldedCompiler.simRows_eq_stepData
      (NatPartrecToToPartrec.translate c)]).to_comp

set_option maxHeartbeats 800000 in
-- Position-coded rows need a separate row-equivalence proof because their
-- current-state field is the explicit support position rather than the
-- canonical `idxOf` state code.
theorem sourceProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec sourceSimStepDataByLabelIndexWithPositionCode)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable sourceProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (sourceStateCount c)
        (sourceSimStepDataByLabelIndexWithPositionCode c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        sourceStateCount_primrec
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourceProgramData sourceStateCount TM0FoldedCompiler.programData
      TM0FoldedCompiler.programDataOfStepData
    rw [hrows c]).to_comp

set_option maxHeartbeats 800000 in
-- The final equality unfolds generated program data and the position-coded descriptor rows.
/--
The source-level position-coded indexed descriptor list directly computes the
finite program generated from those descriptors.  No row-equivalence proof is
needed here: extra noncanonical rows remain part of this generated program and
are handled by separate semantic lookup lemmas.
-/
theorem sourcePositionProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec sourceSimStepDataByLabelIndexWithPositionCode) :
    Computable sourcePositionProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (sourceStateCount c)
        (sourceSimStepDataByLabelIndexWithPositionCode c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        sourceStateCount_primrec
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourcePositionProgramData sourceStateCount
      sourceSimStepDataByLabelIndexWithPositionCode
      TM0FoldedCompiler.positionProgramData
    rfl).to_comp

theorem sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_from hindex)

set_option linter.style.longLine false in
/--
The global position-code label-index decoder gives computability of the
source-specialized generated position-coded folded program.
-/
theorem sourcePositionProgramData_computable_of_globalPositionCodeLabelIndexFrom
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global hindex)

set_option linter.style.longLine false in
theorem sourcePositionProgramData_computable_of_globalPositionCodeLabelIndexFrom'
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)) :=
  (sourcePositionProgramData_computable_of_globalPositionCodeLabelIndexFrom hindex).of_eq
    fun _ => rfl

/--
Primitive recursiveness of the source-level canonical numeric-state decoder is
enough for computability of the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_source_labelIndexStartWithCode
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithCode
    (sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexStartWithCode hindex)

theorem sourceProgramData_computable_of_source_labelIndexStartWithCode'
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexStartWithCode hindex).of_eq fun _ => rfl

/--
Primitive recursiveness of the source-level bounded-search start decoder is
enough for computability of the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_source_labelIndexStartWithSearchCode
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithSearchCode
    (sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_start hindex)

theorem sourceProgramData_computable_of_source_labelIndexStartWithSearchCode'
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexStartWithSearchCode hindex).of_eq
    fun _ => rfl

/--
The remaining source-level folded computability target: primitive recursiveness
of the translated fully offset decoder implies computability of the normalized
folded finite-TM0 program data used by the final reduction.
-/
theorem sourceProgramData_computable_of_source_labelIndexFrom
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndex
    (sourceSimStepDataByLabelIndex_primrec_of_source_labelIndexFrom hindex)

theorem sourceProgramData_computable_of_source_labelIndexFrom'
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexFrom hindex).of_eq fun _ => rfl

/--
The numeric-state source-level folded computability target. This is equivalent
to the semantic source decoder target, but exposes the state code fed to the
finite program.
-/
theorem sourceProgramData_computable_of_source_labelIndexFromWithCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithCode
    (sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexFromWithCode hindex)

theorem sourceProgramData_computable_of_source_labelIndexFromWithCode'
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexFromWithCode hindex).of_eq fun _ => rfl

/--
The source-level bounded-search decoder target is enough for computability of
the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_source_labelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithSearchCode
    (sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_from hindex)

theorem sourceProgramData_computable_of_source_labelIndexFromWithSearchCode'
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexFromWithSearchCode hindex).of_eq
    fun _ => rfl

theorem sourceProgramData_computable_of_source_searchCodeDecoderStep
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithSearchCode
    (sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_decoder_step hstep)

theorem sourceProgramData_computable_of_source_searchCodeDecoderStep'
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_searchCodeDecoderStep hstep).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_searchCodeOneRows
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithSearchCode
    (sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_oneRows hrows)

theorem sourceProgramData_computable_of_source_searchCodeOneRows'
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_searchCodeOneRows hrows).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_searchCodeOneVarRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithSearchCode
    (sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_oneVarRows hvarRows)

theorem sourceProgramData_computable_of_source_searchCodeOneVarRows'
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_searchCodeOneVarRows hvarRows).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_searchCodeOneVarRows_of_positionCodeOneRows
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_searchCodeOneVarRows
    (sourceSearchCodeOneRowsVar_primrec_of_positionCodeOneRows hvarRows hnodup)

theorem sourceProgramData_computable_of_source_searchCodeOneVarRows_of_positionCodeOneRows'
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_searchCodeOneVarRows_of_positionCodeOneRows
    hvarRows hnodup).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_searchCodeOneVarRows_of_positionCodeDecoderStep
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hnodup : SourceStatementListNodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_searchCodeOneVarRows
    (sourceSearchCodeOneRowsVar_primrec_of_positionCodeDecoderStep
      hstep hnodup)

theorem sourceProgramData_computable_of_source_searchCodeOneVarRows_of_positionCodeDecoderStep'
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hnodup : SourceStatementListNodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_searchCodeOneVarRows_of_positionCodeDecoderStep
    hstep hnodup).of_eq fun _ => rfl

/--
Packaged one-row generated position-code rows give source-level computability
of the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_positionCodeOneRowsWithStatementNodup
    (hrows : SourcePositionCodeOneRowsWithStatementNodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_searchCodeOneVarRows_of_positionCodeOneRows
    hrows.rows hrows.statementList_nodup

theorem sourceProgramData_computable_of_positionCodeOneRowsWithStatementNodup'
    (hrows : SourcePositionCodeOneRowsWithStatementNodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_positionCodeOneRowsWithStatementNodup
    hrows).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_boundedInteriorRows
    (hinterior : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 p.2.1 p.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_searchCodeOneVarRows
    (sourceSearchCodeOneRowsVar_primrec_of_boundedInterior hinterior)

theorem sourceProgramData_computable_of_source_boundedInteriorRows'
    (hinterior : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 p.2.1 p.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_boundedInteriorRows hinterior).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_boundedInteriorRows_of_positionBoundedRows
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_boundedInteriorRows
    (sourceSearchCodeBoundedInteriorRowsVar_primrec_of_positionCodeBoundedInteriorRows
      hinterior hnodup)

theorem sourceProgramData_computable_of_source_boundedInteriorRows_of_positionBoundedRows'
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_boundedInteriorRows_of_positionBoundedRows
    hinterior hnodup).of_eq fun _ => rfl

/--
Packaged bounded-interior generated position-code rows give source-level
computability of the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_positionCodeBoundedInteriorRowsWithStatementNodup
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithStatementNodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_boundedInteriorRows_of_positionBoundedRows
    hbounded.rows hbounded.statementList_nodup

theorem sourceProgramData_computable_of_positionCodeBoundedInteriorRowsWithStatementNodup'
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithStatementNodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_positionCodeBoundedInteriorRowsWithStatementNodup
    hbounded).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_interiorRows
    (hinterior : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeInteriorRowsVar p.1 p.2.1 p.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_boundedInteriorRows
    (sourceSearchCodeBoundedInteriorRowsVar_primrec_of_interior hinterior)

theorem sourceProgramData_computable_of_source_interiorRows'
    (hinterior : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeInteriorRowsVar p.1 p.2.1 p.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_interiorRows hinterior).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_interiorRows_of_positionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_interiorRows
    (sourceSearchCodeInteriorRowsVar_primrec_of_positionCodeInteriorRows
      hinterior hnodup)

theorem sourceProgramData_computable_of_source_interiorRows_of_positionCodeInteriorRows'
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_interiorRows_of_positionCodeInteriorRows
    hinterior hnodup).of_eq fun _ => rfl

/--
Packaged interior generated position-code rows give source-level computability
of the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_positionCodeInteriorRowsWithStatementNodup
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_interiorRows_of_positionCodeInteriorRows
    hinterior.rows hinterior.statementList_nodup

theorem sourceProgramData_computable_of_positionCodeInteriorRowsWithStatementNodup'
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_positionCodeInteriorRowsWithStatementNodup
    hinterior).of_eq fun _ => rfl

/--
The remaining bounded-search descriptor decoder proof, together with normalized
folded program-data semantic correctness, gives the exact source obligations
needed by the final reduction.
-/
def sourceObligationsOfLabelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_labelIndexFromWithSearchCode' hindex)
    hcorrect

/--
Primitive recursiveness of the accumulator step for the bounded-search
descriptor decoder, together with normalized folded program-data semantic
correctness, gives the exact source obligations needed by the final reduction.
-/
def sourceObligationsOfSearchCodeDecoderStep
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_searchCodeDecoderStep' hstep)
    hcorrect

/--
Primitive recursiveness of the one-fuel bounded-search row decoder, together
with normalized folded program-data semantic correctness, gives the exact
source obligations needed by the final reduction.
-/
def sourceObligationsOfSearchCodeOneRows
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_searchCodeOneRows' hrows)
    hcorrect

/--
Primitive recursiveness of the variable-branch one-fuel bounded-search row
decoder, together with normalized folded program-data semantic correctness,
gives the exact source obligations needed by the final reduction.
-/
def sourceObligationsOfSearchCodeOneVarRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_searchCodeOneVarRows' hvarRows)
    hcorrect

/--
Primitive recursiveness of the one-row position-code decoder, plus statement
support-list nodup, also supplies the variable-branch bounded-search row
obligation. This is useful while the final theorem surface still exposes both
decoder presentations.
-/
def sourceObligationsOfSearchCodeOneVarRowsPositionCodeOneRows
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_searchCodeOneVarRows_of_positionCodeOneRows'
      hvarRows hnodup)
    hcorrect

/--
Primitive recursiveness of the generated position-code accumulator step, plus
statement support-list nodup, also supplies the variable-branch bounded-search
row obligation on the valid Partrec-variable index path.
-/
def sourceObligationsOfSearchCodeOneVarRowsPositionCodeDecoderStep
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hnodup : SourceStatementListNodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_searchCodeOneVarRows_of_positionCodeDecoderStep'
      hstep hnodup)
    hcorrect

/--
Primitive recursiveness of the bounded interior position-code decoder, plus
statement support-list nodup, also supplies the bounded-search row obligation.
-/
def sourceObligationsOfSearchCodeBoundedInteriorRowsPositionCodeBoundedInteriorRows
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_boundedInteriorRows_of_positionBoundedRows'
      hinterior hnodup)
    hcorrect

/--
Primitive recursiveness of the full interior position-code decoder, plus
statement support-list nodup, also supplies the full interior search-row
obligation.
-/
def sourceObligationsOfSearchCodeInteriorRowsPositionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_interiorRows_of_positionCodeInteriorRows'
      hinterior hnodup)
    hcorrect

/--
Primitive recursiveness of the bounded interior one-row decoder, together with
normalized folded program-data semantic correctness, gives the exact source
obligations needed by the final reduction.
-/
def sourceObligationsOfSearchCodeBoundedInteriorRows
    (hinterior : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 p.2.1 p.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_boundedInteriorRows' hinterior)
    hcorrect

/--
Primitive recursiveness of the interior one-row decoder, together with
normalized folded program-data semantic correctness, gives the exact source
obligations needed by the final reduction.
-/
def sourceObligationsOfSearchCodeInteriorRows
    (hinterior : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeInteriorRowsVar p.1 p.2.1 p.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_interiorRows' hinterior)
    hcorrect

/--
The source-level position-coded decoder is enough for computability once its
generated indexed rows are proved to match the semantic folded simulation rows.
-/
theorem sourceProgramData_computable_of_source_labelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_from hindex)
    hrows

theorem sourceProgramData_computable_of_source_labelIndexFromWithPositionCode'
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexFromWithPositionCode
    hindex hrows).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_positionCodeDecoderStep
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithPositionCode
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_decoder_step hstep)
    hrows

theorem sourceProgramData_computable_of_source_positionCodeDecoderStep'
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_positionCodeDecoderStep
    hstep hrows).of_eq fun _ => rfl

/--
Primitive recursiveness of the one-row position-code decoder is enough for
program-data computability once the generated position-coded rows are known to
match the semantic folded simulation rows.
-/
theorem sourceProgramData_computable_of_source_positionCodeOneRows
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithPositionCode
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_indexVarRows
      hvarRows)
    hrows

theorem sourceProgramData_computable_of_source_positionCodeOneRows'
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_positionCodeOneRows
    hvarRows hrows).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_positionCodeBoundedInteriorRows
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_positionCodeOneRows
    (sourcePositionCodeOneRowsIndexVar_primrec_of_boundedInterior hinterior)
    hrows

theorem sourceProgramData_computable_of_source_positionCodeBoundedInteriorRows'
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_positionCodeBoundedInteriorRows
    hinterior hrows).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_positionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_positionCodeBoundedInteriorRows
    (sourcePositionCodeBoundedInteriorRowsIndexVar_primrec_of_interior hinterior)
    hrows

theorem sourceProgramData_computable_of_source_positionCodeInteriorRows'
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_positionCodeInteriorRows
    hinterior hrows).of_eq fun _ => rfl

/--
The position-coded source decoder gives program-data computability once each
decoded position is known to be the first occurrence of that label in the
support list.
-/
theorem sourceProgramData_computable_of_source_labelIndexFromWithPositionCode_minimal
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithPositionCode hindex
    (fun c => sourceSimRowsOfStepDataByLabelIndexWithPositionCode_eq_of_minimal
      c (hmin c))

theorem sourceProgramData_computable_of_source_labelIndexFromWithPositionCode_minimal'
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexFromWithPositionCode_minimal
    hindex hmin).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_positionCodeDecoderStep_minimal
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithPositionCode_minimal
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_decoder_step hstep)
    hmin

theorem sourceProgramData_computable_of_source_positionCodeDecoderStep_minimal'
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_positionCodeDecoderStep_minimal
    hstep hmin).of_eq fun _ => rfl

/--
Primitive recursiveness of the one-row position-code decoder, plus
first-occurrence minimality for every decoded support position, gives
program-data computability.
-/
theorem sourceProgramData_computable_of_source_positionCodeOneRows_minimal
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithPositionCode_minimal
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_indexVarRows
      hvarRows)
    hmin

theorem sourceProgramData_computable_of_source_positionCodeOneRows_minimal'
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_positionCodeOneRows_minimal
    hvarRows hmin).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_positionCodeOneRows_statementListNodup
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_positionCodeOneRows_minimal
    hvarRows
    (by
      intro c i _hi q hq
      exact sourceLabelAtByStatementFromWithPositionCode_minimal_of_statementList_nodup
        (c := c) (hnodup c) hq)

theorem sourceProgramData_computable_of_source_positionCodeOneRows_statementListNodup'
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_positionCodeOneRows_statementListNodup
    hvarRows hnodup).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_positionCodeDecoderStep_statementListNodup
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_positionCodeDecoderStep_minimal
    hstep
    (by
      intro c i _hi q hq
      exact sourceLabelAtByStatementFromWithPositionCode_minimal_of_statementList_nodup
        (c := c) (hnodup c) hq)

theorem sourceProgramData_computable_of_source_positionCodeDecoderStep_statementListNodup'
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_positionCodeDecoderStep_statementListNodup
    hstep hnodup).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_positionCodeBoundedInteriorRows_statementListNodup
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_positionCodeOneRows_statementListNodup
    (sourcePositionCodeOneRowsIndexVar_primrec_of_boundedInterior hinterior)
    hnodup

theorem sourceProgramData_computable_of_source_positionCodeBoundedInteriorRows_statementListNodup'
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_positionCodeBoundedInteriorRows_statementListNodup
    hinterior hnodup).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_positionCodeInteriorRows_statementListNodup
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_positionCodeBoundedInteriorRows_statementListNodup
    (sourcePositionCodeBoundedInteriorRowsIndexVar_primrec_of_interior hinterior)
    hnodup

theorem sourceProgramData_computable_of_source_positionCodeInteriorRows_statementListNodup'
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_positionCodeInteriorRows_statementListNodup
    hinterior hnodup).of_eq fun _ => rfl

/--
Primitive recursiveness of the source-level position-coded descriptor decoder,
together with a proof that those descriptor rows generate the canonical folded
simulation rows and normalized folded program-data semantic correctness, gives
the exact source obligations needed by the final reduction.
-/
def sourceObligationsOfLabelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_labelIndexFromWithPositionCode'
      hindex hrows)
    hcorrect

/--
Primitive recursiveness of the accumulator step for the source-level
position-coded descriptor decoder, together with a proof that the generated
position-coded rows match the canonical folded simulation rows, gives the
exact source obligations needed by the final reduction.
-/
def sourceObligationsOfPositionCodeDecoderStep
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_positionCodeDecoderStep'
      hstep hrows)
    hcorrect

/--
Primitive recursiveness of the one-row position-code decoder, together with a
proof that the generated position-coded rows match the canonical folded
simulation rows, gives the exact source obligations needed by the final
reduction.
-/
def sourceObligationsOfPositionCodeOneRows
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_positionCodeOneRows'
      hvarRows hrows)
    hcorrect

/--
Primitive recursiveness of the bounded interior one-row position-code decoder,
together with a proof that the generated position-coded rows match the
canonical folded simulation rows, gives the exact source obligations needed by
the final reduction.
-/
def sourceObligationsOfPositionCodeBoundedInteriorRows
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_positionCodeBoundedInteriorRows'
      hinterior hrows)
    hcorrect

/--
Primitive recursiveness of the interior one-row position-code decoder, together
with a proof that the generated position-coded rows match the canonical folded
simulation rows, gives the exact source obligations needed by the final
reduction.
-/
def sourceObligationsOfPositionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_positionCodeInteriorRows'
      hinterior hrows)
    hcorrect

/--
Primitive recursiveness of the source-level position-coded descriptor decoder
directly gives the generated-position source obligations.  Unlike
`sourceObligationsOfLabelIndexFromWithPositionCode`, this packages
`positionProgramData` itself and therefore does not require proving equality
with the canonical folded row list.
-/
def positionSourceObligationsOfLabelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfProgramData
    ((sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode
      hindex).of_eq fun _ => rfl)
    hcorrect

/--
Primitive recursiveness of the generated position-code accumulator step gives
the generated-position source obligations.
-/
def positionSourceObligationsOfPositionCodeDecoderStep
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfLabelIndexFromWithPositionCode
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_decoder_step hstep)
    hcorrect

set_option linter.style.longLine false in
/--
Primitive recursiveness of the global position-code label-index decoder gives
the generated-position source obligations directly.
-/
def positionSourceObligationsOfGlobalPositionCodeLabelIndexFrom
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfLabelIndexFromWithPositionCode
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global hindex)
    hcorrect

/--
Primitive recursiveness of the generated one-row position-code decoder gives
the generated-position source obligations.
-/
def positionSourceObligationsOfPositionCodeOneRows
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfLabelIndexFromWithPositionCode
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_indexVarRows
      hvarRows)
    hcorrect

/--
Packaged generated one-row position-code decoder and translated statement-list
uniqueness give the generated-position source obligations.  The uniqueness
field is carried because it is part of the source-side blocker, although the
generated-position construction itself only needs the row decoder.
-/
def positionSourceObligationsOfPositionCodeOneRowsWithStatementNodup
    (hrows : SourcePositionCodeOneRowsWithStatementNodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeOneRows hrows.rows hcorrect

/--
Primitive recursiveness of the generated bounded-interior position-code rows
gives the generated-position source obligations.
-/
def positionSourceObligationsOfPositionCodeBoundedInteriorRows
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeOneRows
    (sourcePositionCodeOneRowsIndexVar_primrec_of_boundedInterior hinterior)
    hcorrect

/--
Packaged generated bounded-interior position-code decoder and translated
statement-list uniqueness give the generated-position source obligations.
-/
def positionSourceObligationsOfPositionCodeBoundedInteriorRowsWithStatementNodup
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithStatementNodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeBoundedInteriorRows
    hbounded.rows hcorrect

/--
Primitive recursiveness of the generated interior position-code rows gives the
generated-position source obligations.
-/
def positionSourceObligationsOfPositionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeBoundedInteriorRows
    (sourcePositionCodeBoundedInteriorRowsIndexVar_primrec_of_interior hinterior)
    hcorrect

/--
Packaged generated interior position-code decoder and translated
statement-list uniqueness give the generated-position source obligations.
-/
def positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodup
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeInteriorRows
    hinterior.rows hcorrect

/--
Primitive recursiveness of the source-level position-coded descriptor decoder
and first-occurrence minimality for every decoded support position are enough
to produce the source obligations needed by the final reduction.
-/
def sourceObligationsOfLabelIndexFromWithPositionCodeMinimal
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_labelIndexFromWithPositionCode_minimal'
      hindex hmin)
    hcorrect

/--
Primitive recursiveness of the accumulator step for the source-level
position-coded descriptor decoder and first-occurrence minimality for every
decoded support position are enough to produce the source obligations needed
by the final reduction.
-/
def sourceObligationsOfPositionCodeDecoderStepMinimal
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_positionCodeDecoderStep_minimal'
      hstep hmin)
    hcorrect

/--
Primitive recursiveness of the one-row position-code decoder and
first-occurrence minimality for every decoded support position are enough to
produce the source obligations needed by the final reduction.
-/
def sourceObligationsOfPositionCodeOneRowsMinimal
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_positionCodeOneRows_minimal'
      hvarRows hmin)
    hcorrect

/--
Primitive recursiveness of the one-row position-code decoder and absence of
duplicates in the translated TM0 statement-support list are enough to produce
the source obligations needed by the final reduction.
-/
def sourceObligationsOfPositionCodeOneRowsStatementListNodup
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_positionCodeOneRows_statementListNodup'
      hvarRows hnodup)
    hcorrect

/--
Packaged one-row position-code decoder and translated statement-list
uniqueness are enough to produce the source obligations needed by the final
reduction.
-/
def sourceObligationsOfPositionCodeOneRowsWithStatementNodup
    (hrows : SourcePositionCodeOneRowsWithStatementNodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfPositionCodeOneRowsStatementListNodup
    hrows.rows hrows.statementList_nodup hcorrect

/--
Primitive recursiveness of the accumulator step for the source-level
position-coded descriptor decoder and absence of duplicates in the translated
TM0 statement-support list are enough to produce the source obligations needed
by the final reduction.
-/
def sourceObligationsOfPositionCodeDecoderStepStatementListNodup
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_positionCodeDecoderStep_statementListNodup'
      hstep hnodup)
    hcorrect

/--
Primitive recursiveness of the bounded interior one-row position-code decoder
and absence of duplicates in the translated TM0 statement-support list are
enough to produce the source obligations needed by the final reduction.
-/
def sourceObligationsOfPositionCodeBoundedInteriorRowsStatementListNodup
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_positionCodeBoundedInteriorRows_statementListNodup'
      hinterior hnodup)
    hcorrect

/--
Packaged bounded-interior position-code decoder and translated statement-list
uniqueness are enough to produce the source obligations needed by the final
reduction.
-/
def sourceObligationsOfPositionCodeBoundedInteriorRowsWithStatementNodup
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithStatementNodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfPositionCodeBoundedInteriorRowsStatementListNodup
    hbounded.rows hbounded.statementList_nodup hcorrect

/--
Primitive recursiveness of the interior one-row position-code decoder and
absence of duplicates in the translated TM0 statement-support list are enough
to produce the source obligations needed by the final reduction.
-/
def sourceObligationsOfPositionCodeInteriorRowsStatementListNodup
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_positionCodeInteriorRows_statementListNodup'
      hinterior hnodup)
    hcorrect

/--
Packaged interior position-code decoder and translated statement-list
uniqueness are enough to produce the source obligations needed by the final
reduction.
-/
def sourceObligationsOfPositionCodeInteriorRowsWithStatementNodup
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfPositionCodeInteriorRowsStatementListNodup
    hinterior.rows hinterior.statementList_nodup hcorrect

/--
The current lowest-level folded computability target, phrased at source-code
level: primitive recursiveness of the fully offset label-index descriptor
decoder implies computability of the normalized folded finite-TM0 program data
used by the final reduction.
-/
theorem sourceProgramData_computable_of_global_labelIndexFrom
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexFrom hindex).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexFrom'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexFrom hindex).of_eq fun _ => rfl

/--
Global canonical numeric-state decoder bridge for the source reduction.
This is the non-source-specialized version of
`sourceProgramData_computable_of_source_labelIndexStartWithCode`.
-/
theorem sourceProgramData_computable_of_global_labelIndexStartWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexStartWithCode
      hindex).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexStartWithCode'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexStartWithCode hindex).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_global_labelIndexFromWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexFromWithCode hindex).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexFromWithCode'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexFromWithCode hindex).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_global_labelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexFromWithSearchCode
    hindex).comp NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexFromWithSearchCode'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexFromWithSearchCode hindex).of_eq fun _ => rfl

/--
Fixed-domino instance produced directly from the generated position-coded
folded program for a source partial-recursive code.
-/
def sourcePositionFixedDominoReduction
    (_h : PositionSourceObligations) (c : Code) : TileSet × WangTile :=
  tableProgramFixedDominoData
    (PostProgram.toTableProgram
      (TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)))

theorem sourcePositionFixedDominoReduction_computable
    (h : PositionSourceObligations) :
    Computable (sourcePositionFixedDominoReduction h) := by
  exact tableProgramFixedDominoData_computable.comp
    (PostProgram.toTableProgram_computable.comp h.program_computable)

theorem sourcePositionFixedDominoReduction_correct
    (h : PositionSourceObligations) (c : Code) :
    TilesQuarterWithSeed (sourcePositionFixedDominoReduction h c).1
        (sourcePositionFixedDominoReduction h c).2 ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  unfold sourcePositionFixedDominoReduction
  rw [tableProgramFixedDominoData_seed_eq]
  rw [tilesQuarterWithSeed_congr
    (tableProgramFixedDominoData_mem_iff
      (PostProgram.toTableProgram
        (TM0FoldedCompiler.positionProgramData
          (NatPartrecToToPartrec.translate c))))]
  rw [tableProgramFixedDomino_correct]
  rw [PostProgram.toTableProgram_toMachine_haltsEmpty_iff]
  rw [h.correct c]

/--
Final scaffolded tileset produced from the generated position-coded folded
program for a source partial-recursive code.
-/
def sourcePositionDominoReduction
    (S : Scaffold) (h : PositionSourceObligations) (c : Code) : TileSet :=
  combineWithScaffold S (sourcePositionFixedDominoReduction h c).1
    (sourcePositionFixedDominoReduction h c).2

theorem sourcePositionDominoReduction_computable
    (S : Scaffold) (h : PositionSourceObligations) :
    Computable (sourcePositionDominoReduction S h) := by
  exact (combineWithScaffold_computable S).comp
    (sourcePositionFixedDominoReduction_computable h)

theorem sourcePositionDominoReduction_correct
    {S : Scaffold} (hS : IsScaffold S) (h : PositionSourceObligations) (c : Code) :
    TilesPlane (sourcePositionDominoReduction S h c) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [sourcePositionDominoReduction]
  exact (scaffold_reduction_correct hS
    (sourcePositionFixedDominoReduction h c).1
    (sourcePositionFixedDominoReduction h c).2).trans
      ((tilesQuarterWithSeed_iff_all_fixedCornerSquares
        (sourcePositionFixedDominoReduction h c).1
        (sourcePositionFixedDominoReduction h c).2).symm.trans
          (sourcePositionFixedDominoReduction_correct h c))

/-- Encoded version of the generated position-coded source folded reduction. -/
def sourcePositionDominoReductionCode
    (S : Scaffold) (h : PositionSourceObligations) (c : Code) : Nat :=
  encodeTileSet (sourcePositionDominoReduction S h c)

theorem sourcePositionDominoReductionCode_computable
    (S : Scaffold) (h : PositionSourceObligations) :
    Computable (sourcePositionDominoReductionCode S h) := by
  exact encodeTileSet_computable.comp (sourcePositionDominoReduction_computable S h)

theorem sourcePositionDominoReductionCode_correct
    {S : Scaffold} (hS : IsScaffold S) (h : PositionSourceObligations) (c : Code) :
    TilesPlane (decodeTileSet (sourcePositionDominoReductionCode S h c)) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [sourcePositionDominoReductionCode, decodeTileSet_encodeTileSet]
  exact sourcePositionDominoReduction_correct hS h c

/--
Encoded domino undecidability from the generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source
    (S : Scaffold) (hS : IsScaffold S) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  intro hdec
  have hencoded : ComputablePred
      (fun c : Code => TilesPlane (decodeTileSet (sourcePositionDominoReductionCode S h c))) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun n : Nat => TilesPlane (decodeTileSet n))
        (sourcePositionDominoReductionCode_computable S h)) hdec
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hencoded.of_eq fun c => sourcePositionDominoReductionCode_correct hS h c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/--
Unencoded domino undecidability from the generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_scaffold_position_source
    (S : Scaffold) (hS : IsScaffold S) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  intro hdec
  have hdomino : ComputablePred
      (fun c : Code => TilesPlane (sourcePositionDominoReduction S h c)) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun T : TileSet => TilesPlane T)
        (sourcePositionDominoReduction_computable S h)) hdec
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hdomino.of_eq fun c => sourcePositionDominoReduction_correct hS h c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/--
Encoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated position-coded source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_presented_position_source
    (I : OllingerRobinson.PresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Unencoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated position-coded source-route obligations.
-/
theorem domino_problem_undecidable_of_presented_position_source
    (I : OllingerRobinson.PresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source
    (I : OllingerRobinson.PresentedFlexibleInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source
    (I : OllingerRobinson.PresentedFlexibleInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Encoded domino undecidability from a checked finite-data
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_checked_position_source
    (I : OllingerRobinson.CheckedPresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_position_source
    I.toPresentedInstance h

/--
Unencoded domino undecidability from a checked finite-data
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_checked_position_source
    (I : OllingerRobinson.CheckedPresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_position_source
    I.toPresentedInstance h

/--
Encoded domino undecidability from a scaffold and the generated position-coded
descriptor decoder.  This uses `positionProgramData` directly, so no
row-equivalence proof against the canonical folded rows is required.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCode
    (S : Scaffold) (hS : IsScaffold S)
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfLabelIndexFromWithPositionCode hindex hcorrect)

/--
Unencoded domino undecidability from a scaffold and the generated
position-coded descriptor decoder.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCode
    (S : Scaffold) (hS : IsScaffold S)
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfLabelIndexFromWithPositionCode hindex hcorrect)

/--
Encoded domino undecidability from a scaffold and the generated position-code
accumulator step.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeDecoderStep
    (S : Scaffold) (hS : IsScaffold S)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeDecoderStep hstep hcorrect)

/--
Unencoded domino undecidability from a scaffold and the generated position-code
accumulator step.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeDecoderStep
    (S : Scaffold) (hS : IsScaffold S)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeDecoderStep hstep hcorrect)

/--
Encoded domino undecidability from a scaffold and the generated one-row
position-code decoder.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeOneRows
    (S : Scaffold) (hS : IsScaffold S)
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRows hvarRows hcorrect)

/--
Unencoded domino undecidability from a scaffold and the generated one-row
position-code decoder.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeOneRows
    (S : Scaffold) (hS : IsScaffold S)
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRows hvarRows hcorrect)

/--
Encoded domino undecidability from a scaffold and the generated bounded
interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeBoundedRows
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRows
      hinterior hcorrect)

/--
Unencoded domino undecidability from a scaffold and the generated bounded
interior position-code rows.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeBoundedRows
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRows
      hinterior hcorrect)

/--
Encoded domino undecidability from a scaffold and the generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRows
      hinterior hcorrect)

/--
Unencoded domino undecidability from a scaffold and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRows
      hinterior hcorrect)

/--
Encoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.PresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    I.presentation.toScaffold I.isScaffold hinterior hcorrect

/--
Unencoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.PresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    I.presentation.toScaffold I.isScaffold hinterior hcorrect

/--
Encoded domino undecidability from a checked finite-data
Ollinger/Robinson scaffold and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_checked_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.CheckedPresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    I.toPresentedInstance hinterior hcorrect

/--
Unencoded domino undecidability from a checked finite-data
Ollinger/Robinson scaffold and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_checked_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.CheckedPresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    I.toPresentedInstance hinterior hcorrect

/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated interior position-code rows.
-/
theorem
encoded_domino_problem_undecidable_of_presented_flexible_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    I.presentation.toScaffold I.isScaffold hinterior hcorrect

/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    I.presentation.toScaffold I.isScaffold hinterior hcorrect

end TM0FoldedReduction

end LeanWang

end
