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

/--
Primitive recursiveness of the generated position-code accumulator step gives
the full generated-position source obligations once the semantic folded proof
is imported.
-/
def positionSourceObligationsOfPositionCodeDecoderStepCorrect
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2)) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeDecoderStep hstep
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
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeOneRows hvarRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Packaged generated one-row position-code decoder and translated statement-list
uniqueness give the full generated-position source obligations once the
semantic folded proof is imported.
-/
def positionSourceObligationsOfPositionCodeOneRowsWithStatementNodupCorrect
    (hrows : SourcePositionCodeOneRowsWithStatementNodup) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeOneRowsWithStatementNodup hrows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the generated bounded-interior position-code rows
gives the full generated-position source obligations once the semantic folded
proof is imported.
-/
def positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect
    (hbounded : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeBoundedInteriorRows hbounded
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Packaged generated bounded-interior position-code decoder and translated
statement-list uniqueness give the full generated-position source obligations
once the semantic folded proof is imported.
-/
def positionSourceObligationsOfPositionCodeBoundedInteriorRowsWithStatementNodupCorrect
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithStatementNodup) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeBoundedInteriorRowsWithStatementNodup
    hbounded TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the generated interior position-code rows gives the
full generated-position source obligations once the semantic folded proof is
imported.
-/
def positionSourceObligationsOfPositionCodeInteriorRowsCorrect
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeInteriorRows hinterior
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Packaged generated interior position-code decoder and translated statement-list
uniqueness give the full generated-position source obligations once the
semantic folded proof is imported.
-/
def positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodupCorrect
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodup
    hinterior TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end TM0FoldedReduction

end LeanWang
