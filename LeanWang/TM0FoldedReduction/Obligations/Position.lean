/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.OffsetStart

/-!
Position-code and generated-position source-obligation constructors for the
folded TM0-to-Wang reduction.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

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

set_option linter.style.longLine false in
/--
The source-specialized position-code label-index decoder is enough for
program-data computability once the generated indexed rows are known to match
the semantic folded simulation rows.
-/
theorem sourceProgramData_computable_of_sourcePositionCodeLabelIndexFrom
    (hindex : SourcePositionCodeLabelIndexFromPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithPositionCode
    hindex hrows

set_option linter.style.longLine false in
theorem sourceProgramData_computable_of_sourcePositionCodeLabelIndexFrom'
    (hindex : SourcePositionCodeLabelIndexFromPrimrec)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_sourcePositionCodeLabelIndexFrom
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

set_option linter.style.longLine false in
/--
The source-specialized position-code decoder gives program-data computability
once each decoded position is known to be the first occurrence of that label in
the support list.
-/
theorem sourceProgramData_computable_of_sourcePositionCodeLabelIndexFrom_minimal
    (hindex : SourcePositionCodeLabelIndexFromPrimrec)
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithPositionCode_minimal
    hindex hmin

set_option linter.style.longLine false in
theorem sourceProgramData_computable_of_sourcePositionCodeLabelIndexFrom_minimal'
    (hindex : SourcePositionCodeLabelIndexFromPrimrec)
    (hmin : ∀ c : Code, ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_sourcePositionCodeLabelIndexFrom_minimal
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

set_option linter.style.longLine false in
/--
Primitive recursiveness of the source-specialized position-code label-index
decoder gives the generated-position source obligations directly.
-/
def positionSourceObligationsOfSourcePositionCodeLabelIndexFrom
    (hindex : SourcePositionCodeLabelIndexFromPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfLabelIndexFromWithPositionCode hindex hcorrect

set_option linter.style.longLine false in
/--
The support-search-code label-index decoder, together with duplicate-free
source statement supports, gives the generated-position source obligations.
-/
def positionSourceObligationsOfSearchCodeLabelIndexFromWithStatementNodup
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfSourcePositionCodeLabelIndexFrom
    (sourcePositionCodeLabelIndexFromPrimrec_of_searchCodeLabelIndexFrom
      hsearch hnodup)
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
Primitive recursiveness of the generated one-row-at-index decoder gives the
generated-position source obligations.
-/
def positionSourceObligationsOfPositionCodeOneRowsAtIndex
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfSourcePositionCodeLabelIndexFrom
    (sourcePositionCodeLabelIndexFromPrimrec_of_oneRowsAtIndex hrows)
    hcorrect

set_option linter.style.longLine false in
/--
Primitive recursiveness of bounded-interior generated position-code rows at
concrete numeric label slots gives the generated-position source obligations.
-/
def positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndex
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeOneRowsAtIndex
    (sourcePositionCodeOneRowsAtIndexPrimrec_of_boundedInteriorAtIndex hbounded)
    hcorrect

set_option linter.style.longLine false in
/--
Primitive recursiveness of the source-level position-coded start decoder gives
the generated-position source obligations.
-/
def positionSourceObligationsOfPositionCodeLabelIndexStart
    (hstart : SourcePositionCodeLabelIndexStartPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfProgramData
    ((sourcePositionProgramData_computable_of_source_positionCodeLabelIndexStart
      hstart).of_eq fun _ => rfl)
    hcorrect

set_option linter.style.longLine false in
/--
Primitive recursiveness of interior generated position-code rows at concrete
numeric label slots gives the generated-position source obligations.
-/
def positionSourceObligationsOfPositionCodeInteriorRowsAtIndex
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndex
    (sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_interiorAtIndex
      hinterior)
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
  positionSourceObligationsOfProgramData
    ((sourcePositionProgramData_computable_of_source_positionCodeOneRows hvarRows).of_eq
      fun _ => rfl)
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
  positionSourceObligationsOfProgramData
    ((sourcePositionProgramData_computable_of_source_positionCodeBoundedInteriorRows
      hinterior).of_eq fun _ => rfl)
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
  positionSourceObligationsOfProgramData
    ((sourcePositionProgramData_computable_of_source_positionCodeInteriorRows
      hinterior).of_eq fun _ => rfl)
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

end TM0FoldedReduction

end LeanWang
