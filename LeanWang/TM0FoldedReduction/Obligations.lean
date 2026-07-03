/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.OffsetStart

/-!
This module is split out from `LeanWang.TM0FoldedReduction` so Lake can
cache the machine-side reduction layers separately while preserving the old
public import path.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

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

end TM0FoldedReduction

end LeanWang

end
