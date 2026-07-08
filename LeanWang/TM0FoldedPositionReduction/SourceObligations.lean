/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction
import LeanWang.TM0FoldedPositionCorrect

/-!
Semantic source-obligation constructors for the generated position-coded folded
reduction.

`TM0FoldedReduction` keeps semantic correctness as an explicit parameter.  This
module imports the folded semantic proof and packages that theorem into the
source-obligation surfaces used by the final theorem wrappers.
-/


namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

theorem programData_haltsEmpty_iff_tm0_eval_dom
    (tc : Turing.ToPartrec.Code) :
    (TM0FoldedCompiler.programData tc).HaltsEmpty ↔
      (Turing.TM0.eval
        (TM0Route.partrecStartedTM0Machine tc)
        TM0Route.partrecStartedTM0Input).Dom := by
  rw [TM0FoldedCompiler.programData_eq_program]
  exact TM0FoldedCompiler.program_haltsEmpty_iff_tm0_eval_dom tc

/--
Ordinary source obligations from only the normalized source-level computability
proof, using the semantic correctness theorem for `programData`.
-/
def sourceObligationsOfProgramDataCorrect
    (hprogram : Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c))) :
    SourceObligations :=
  sourceObligationsOfProgramData hprogram
    programData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the bounded-search label-index decoder gives the
ordinary source obligations once the semantic folded proof is imported.
-/
def sourceObligationsOfLabelIndexFromWithSearchCodeCorrect
    (hindex : SourceSearchCodeLabelIndexFromPrimrec) :
    SourceObligations :=
  sourceObligationsOfLabelIndexFromWithSearchCode hindex
    programData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the bounded-search accumulator step gives the
ordinary source obligations once the semantic folded proof is imported.
-/
def sourceObligationsOfSearchCodeDecoderStepCorrect
    (hstep : SourceSearchCodeDecoderStepPrimrec) :
    SourceObligations :=
  sourceObligationsOfSearchCodeDecoderStep hstep
    programData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the one-fuel bounded-search row decoder gives the
ordinary source obligations once the semantic folded proof is imported.
-/
def sourceObligationsOfSearchCodeOneRowsCorrect
    (hrows : SourceSearchCodeOneRowsPrimrec) :
    SourceObligations :=
  sourceObligationsOfSearchCodeOneRows hrows
    programData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the variable-branch one-fuel bounded-search row
decoder gives the ordinary source obligations once the semantic folded proof is
imported.
-/
def sourceObligationsOfSearchCodeOneVarRowsCorrect
    (hvarRows : SourceSearchCodeOneVarRowsPrimrec) :
    SourceObligations :=
  sourceObligationsOfSearchCodeOneVarRows hvarRows
    programData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the bounded interior bounded-search rows gives the
ordinary source obligations once the semantic folded proof is imported.
-/
def sourceObligationsOfSearchCodeBoundedInteriorRowsCorrect
    (hinterior : SourceSearchCodeBoundedInteriorRowsPrimrec) :
    SourceObligations :=
  sourceObligationsOfSearchCodeBoundedInteriorRows hinterior
    programData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the full interior bounded-search rows gives the
ordinary source obligations once the semantic folded proof is imported.
-/
def sourceObligationsOfSearchCodeInteriorRowsCorrect
    (hinterior : SourceSearchCodeInteriorRowsPrimrec) :
    SourceObligations :=
  sourceObligationsOfSearchCodeInteriorRows hinterior
    programData_haltsEmpty_iff_tm0_eval_dom

/--
Generated-position source obligations from only the source-level computability
proof, using the semantic correctness theorem for `positionProgramData`.
-/
def positionSourceObligationsOfProgramDataCorrect
    (hprogram : Computable (fun c : Code =>
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c))) :
    PositionSourceObligations :=
  positionSourceObligationsOfProgramData hprogram
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the generated position-code descriptor rows gives
the full generated-position source obligations once the semantic folded proof is
imported.
-/
def positionSourceObligationsOfLabelIndexFromWithPositionCodeCorrect
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    PositionSourceObligations :=
  positionSourceObligationsOfLabelIndexFromWithPositionCode hindex
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Primitive recursiveness of the source-specialized position-code label-index
decoder gives the full generated-position source obligations once the semantic
folded proof is imported.
-/
def positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfSourcePositionCodeLabelIndexFrom hindex
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Primitive recursiveness of the bounded-search label-index decoder, together
with duplicate-free source statement supports, gives the full generated-position
source obligations once the semantic folded proof is imported.
-/
def positionSourceObligationsOfSearchCodeLabelIndexFromWithStatementNodupCorrect
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    PositionSourceObligations :=
  positionSourceObligationsOfSearchCodeLabelIndexFromWithStatementNodup
    hsearch hnodup
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the generated position-code accumulator step gives
the full generated-position source obligations once the semantic folded proof
is imported.
-/
def positionSourceObligationsOfPositionCodeDecoderStepCorrect
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeDecoderStep hstep
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Primitive recursiveness of the generated one-row-at-index decoder gives the
full generated-position source obligations once the semantic folded proof is
imported.
-/
def positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeOneRowsAtIndex hrows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Primitive recursiveness of bounded-interior generated position-code rows at
concrete numeric label slots gives the full generated-position source
obligations once the semantic folded proof is imported.
-/
def positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndex hbounded
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Primitive recursiveness of the source-level position-coded start decoder gives
the full generated-position source obligations once the semantic folded proof
is imported.
-/
def positionSourceObligationsOfPositionCodeLabelIndexStartCorrect
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeLabelIndexStart hstart
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Primitive recursiveness of interior generated position-code rows at concrete
numeric label slots gives the full generated-position source obligations once
the semantic folded proof is imported.
-/
def positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeInteriorRowsAtIndex hinterior
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Primitive recursiveness of the global position-code label-index decoder gives
the full generated-position source obligations once the semantic folded proof
is imported.
-/
def positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfGlobalPositionCodeLabelIndexFrom hindex
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the generated one-row position-code decoder gives
the full generated-position source obligations once the semantic folded proof
is imported.
-/
def positionSourceObligationsOfPositionCodeOneRowsCorrect
    (hvarRows : SourcePositionCodeOneRowsPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeOneRows hvarRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the generated bounded-interior position-code rows
gives the full generated-position source obligations once the semantic folded
proof is imported.
-/
def positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeBoundedInteriorRows hbounded
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the generated interior position-code rows gives the
full generated-position source obligations once the semantic folded proof is
imported.
-/
def positionSourceObligationsOfPositionCodeInteriorRowsCorrect
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeInteriorRows hinterior
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end TM0FoldedReduction

end LeanWang
