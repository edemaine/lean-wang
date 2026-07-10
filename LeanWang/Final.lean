/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalFoldedReduction

/-!
# Final Wang-tile undecidability theorem

The machine side uses one fixed universal TM0 machine.  A source code changes
only the finite initial tape written before the fixed simulation starts.  Thus
the final theorem needs no source-dependent machine compiler or decoder
obligation; its sole remaining input is a concrete scaffold certificate.
-/

noncomputable section

namespace LeanWang

/-- Encoded Wang domino undecidability from any certified scaffold. -/
theorem encoded_domino_problem_undecidable
    (S : Scaffold) (hS : IsScaffold S) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  UniversalFoldedReduction.encoded_domino_problem_undecidable S hS

/-- Wang domino undecidability from any certified scaffold. -/
theorem domino_problem_undecidable
    (S : Scaffold) (hS : IsScaffold S) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  UniversalFoldedReduction.domino_problem_undecidable S hS

/-- Encoded Wang domino undecidability from a channel-aware routed scaffold. -/
theorem encoded_domino_problem_undecidable_of_routed
    (S : RoutedScaffold) (hS : IsRoutedScaffold S) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  UniversalFoldedReduction.encoded_domino_problem_undecidable_of_routed S hS

/-- Wang domino undecidability from a channel-aware routed scaffold. -/
theorem domino_problem_undecidable_of_routed
    (S : RoutedScaffold) (hS : IsRoutedScaffold S) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  UniversalFoldedReduction.domino_problem_undecidable_of_routed S hS

end LeanWang

end
