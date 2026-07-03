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
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
    (sourcePositionCodeLabelIndexFromPrimrec_of_decoderStep hstep)

set_option linter.style.longLine false in
/--
Primitive recursiveness of the global position-code label-index decoder gives
the full generated-position source obligations once the semantic folded proof
is imported.
-/
def positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    PositionSourceObligations :=
  positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
    (sourcePositionCodeLabelIndexFromPrimrec_of_globalPositionCodeLabelIndexFromPrimrec
      hindex)

/--
Primitive recursiveness of the generated one-row position-code decoder gives
the full generated-position source obligations once the semantic folded proof
is imported.
-/
def positionSourceObligationsOfPositionCodeOneRowsCorrect
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    PositionSourceObligations :=
  positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
    (sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeOneRows hvarRows)

set_option linter.style.longLine false in
/--
The packaged generated one-row position-code decoder also gives the full
generated-position source obligations once the semantic folded proof is
imported.  The package keeps translated statement-list uniqueness for the
older normalized-program route; this generated-position route only needs the
row decoder field.
-/
def positionSourceObligationsOfPositionCodeOneRowsWithStatementNodupCorrect
    (hrows : SourcePositionCodeOneRowsWithStatementNodup) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeOneRowsCorrect hrows.rows

/--
Primitive recursiveness of the generated bounded-interior position-code rows
gives the full generated-position source obligations once the semantic folded
proof is imported.
-/
def positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect
    (hbounded : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    PositionSourceObligations :=
  positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
    (sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeBoundedInteriorRows
      hbounded)

set_option linter.style.longLine false in
/--
The packaged generated bounded-interior position-code decoder also gives the
full generated-position source obligations once the semantic folded proof is
imported.  The translated statement-list uniqueness field is retained for the
older normalized-program route.
-/
def positionSourceObligationsOfPositionCodeBoundedInteriorRowsWithStatementNodupCorrect
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithStatementNodup) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded.rows

/--
Primitive recursiveness of the generated interior position-code rows gives the
full generated-position source obligations once the semantic folded proof is
imported.
-/
def positionSourceObligationsOfPositionCodeInteriorRowsCorrect
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    PositionSourceObligations :=
  positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
    (sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeInteriorRows
      hinterior)

set_option linter.style.longLine false in
/--
The packaged generated interior position-code decoder also gives the full
generated-position source obligations once the semantic folded proof is
imported.  The translated statement-list uniqueness field is retained for the
older normalized-program route.
-/
def positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodupCorrect
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeInteriorRowsCorrect hinterior.rows

end TM0FoldedReduction

end LeanWang
