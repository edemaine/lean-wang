/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.OffsetStart.SearchBridge

/-!
Computability consequences for folded source program data and generated position-program data.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

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

theorem sourcePositionProgramData_computable_of_source_positionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_interiorRows hinterior)

theorem sourcePositionProgramData_computable_of_source_positionCodeBoundedInteriorRows
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_positionCodeInteriorRows
    (sourcePositionCodeInteriorRowsIndexVar_primrec_of_oneRows
      (sourcePositionCodeOneRowsIndexVar_primrec_of_boundedInterior hbounded))

theorem sourcePositionProgramData_computable_of_source_positionCodeOneRows
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_positionCodeInteriorRows
    (sourcePositionCodeInteriorRowsIndexVar_primrec_of_oneRows hrows)

theorem sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_from hindex)

set_option linter.style.longLine false in
/--
Primitive recursiveness of the source-level position-coded start decoder is
enough for computability of the source-specialized generated position-coded
folded program.
-/
theorem sourcePositionProgramData_computable_of_source_positionCodeLabelIndexStart
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_start hstart)

set_option linter.style.longLine false in
/--
Primitive recursiveness of the generated one-row-at-index decoder is enough
for computability of the source-specialized generated position-coded folded
program.
-/
theorem sourcePositionProgramData_computable_of_source_positionCodeOneRowsAtIndex
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode
    (sourcePositionCodeLabelIndexFromPrimrec_of_oneRowsAtIndex hrows)

set_option linter.style.longLine false in
/--
Primitive recursiveness of bounded-interior generated position-code rows at
concrete numeric label slots is enough for computability of the
source-specialized generated position-coded folded program.
-/
theorem sourcePositionProgramData_computable_of_source_positionCodeBoundedInteriorRowsAtIndex
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_positionCodeOneRowsAtIndex
    (sourcePositionCodeOneRowsAtIndexPrimrec_of_boundedInteriorAtIndex hbounded)

set_option linter.style.longLine false in
/--
Primitive recursiveness of interior generated position-code rows at concrete
numeric label slots is enough for computability of the source-specialized
generated position-coded folded program.
-/
theorem sourcePositionProgramData_computable_of_source_positionCodeInteriorRowsAtIndex
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_positionCodeBoundedInteriorRowsAtIndex
    (sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_interiorAtIndex
      hinterior)

set_option linter.style.longLine false in
/--
The source-specialized position-code label-index decoder gives computability
of the source-specialized generated position-coded folded program.
-/
theorem sourcePositionProgramData_computable_of_sourcePositionCodeLabelIndexFrom
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode
    hindex

set_option linter.style.longLine false in
theorem sourcePositionProgramData_computable_of_sourcePositionCodeLabelIndexFrom'
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)) :=
  (sourcePositionProgramData_computable_of_sourcePositionCodeLabelIndexFrom hindex).of_eq
    fun _ => rfl

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


end TM0FoldedReduction

end LeanWang
