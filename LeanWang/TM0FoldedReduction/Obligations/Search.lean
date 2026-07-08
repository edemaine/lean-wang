/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.OffsetStart

/-!
Search-code source-obligation constructors for the folded TM0-to-Wang
reduction.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

theorem sourceProgramData_computable_of_source_searchCodeDecoderStep
    (hstep : SourceSearchCodeDecoderStepPrimrec) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithSearchCode
    (sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_decoder_step hstep)

theorem sourceProgramData_computable_of_source_searchCodeDecoderStep'
    (hstep : SourceSearchCodeDecoderStepPrimrec) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_searchCodeDecoderStep hstep).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_searchCodeOneRows
    (hrows : SourceSearchCodeOneRowsPrimrec) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithSearchCode
    (sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_oneRows hrows)

theorem sourceProgramData_computable_of_source_searchCodeOneRows'
    (hrows : SourceSearchCodeOneRowsPrimrec) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_searchCodeOneRows hrows).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_source_searchCodeOneVarRows
    (hvarRows : SourceSearchCodeOneVarRowsPrimrec) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithSearchCode
    (sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_oneVarRows hvarRows)

theorem sourceProgramData_computable_of_source_searchCodeOneVarRows'
    (hvarRows : SourceSearchCodeOneVarRowsPrimrec) :
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

theorem sourceProgramData_computable_of_source_boundedInteriorRows
    (hinterior : SourceSearchCodeBoundedInteriorRowsPrimrec) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_searchCodeOneVarRows
    (sourceSearchCodeOneRowsVar_primrec_of_boundedInterior hinterior)

theorem sourceProgramData_computable_of_source_boundedInteriorRows'
    (hinterior : SourceSearchCodeBoundedInteriorRowsPrimrec) :
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

theorem sourceProgramData_computable_of_source_interiorRows
    (hinterior : SourceSearchCodeInteriorRowsPrimrec) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_boundedInteriorRows
    (sourceSearchCodeBoundedInteriorRowsVar_primrec_of_interior hinterior)

theorem sourceProgramData_computable_of_source_interiorRows'
    (hinterior : SourceSearchCodeInteriorRowsPrimrec) :
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
The remaining bounded-search descriptor decoder proof, together with normalized
folded program-data semantic correctness, gives the exact source obligations
needed by the final reduction.
-/
def sourceObligationsOfLabelIndexFromWithSearchCode
    (hindex : SourceSearchCodeLabelIndexFromPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_labelIndexFromWithSearchCode' hindex)
    hcorrect

set_option linter.style.longLine false in
/--
Primitive recursiveness of the source-level bounded-search start decoder,
together with normalized folded program-data semantic correctness, gives the
exact source obligations needed by the final reduction.
-/
def sourceObligationsOfSearchCodeLabelIndexStart
    (hindex : SourceSearchCodeLabelIndexStartPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_labelIndexStartWithSearchCode'
      hindex)
    hcorrect

/--
Primitive recursiveness of the accumulator step for the bounded-search
descriptor decoder, together with normalized folded program-data semantic
correctness, gives the exact source obligations needed by the final reduction.
-/
def sourceObligationsOfSearchCodeDecoderStep
    (hstep : SourceSearchCodeDecoderStepPrimrec)
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
    (hrows : SourceSearchCodeOneRowsPrimrec)
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
    (hvarRows : SourceSearchCodeOneVarRowsPrimrec)
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
    (hinterior : SourceSearchCodeBoundedInteriorRowsPrimrec)
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
    (hinterior : SourceSearchCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    SourceObligations :=
  sourceObligationsOfProgramData
    (sourceProgramData_computable_of_source_interiorRows' hinterior)
    hcorrect

end TM0FoldedReduction

end LeanWang
