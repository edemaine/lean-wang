/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Obligations
import LeanWang.TM0FoldedCompiler.CorrectnessPosition

/-!
Source-code computability bridges for the folded TM0 program data.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

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

end TM0FoldedReduction

end LeanWang
