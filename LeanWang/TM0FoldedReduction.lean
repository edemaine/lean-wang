/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram
import LeanWang.Theorems

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
The folded finite-TM0 construction packaged as the `TM0FiniteCompiler`
interface used by the main theorem surface.
-/
def compiler (h : Obligations) : TM0FiniteCompiler where
  compile := TM0FoldedCompiler.program
  compile_computable := h.program_computable
  correct := h.correct

/--
Encoded domino undecidability from a scaffold and the folded finite-TM0 route,
assuming the isolated folded-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_scaffold
    (S : Scaffold) (hS : IsScaffold S) (h : Obligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_tm0Reduction_concrete
    S hS (compiler h)

/--
Unencoded domino undecidability from a scaffold and the folded finite-TM0 route,
assuming the isolated folded-route obligations.
-/
theorem domino_problem_undecidable_of_scaffold
    (S : Scaffold) (hS : IsScaffold S) (h : Obligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_tm0Reduction_concrete
    S hS (compiler h)

end TM0FoldedReduction

end LeanWang

end
