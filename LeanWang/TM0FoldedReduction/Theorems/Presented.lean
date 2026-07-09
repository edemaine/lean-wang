/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Theorems.PositionScaffold

/-!
Presented Ollinger/Robinson scaffold wrappers for position-coded source obligations.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/--
Encoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated position-coded source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_presented_position_source
    (I : OllingerRobinson.PresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Unencoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated position-coded source-route obligations.
-/
theorem domino_problem_undecidable_of_presented_position_source
    (I : OllingerRobinson.PresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source
    (I : OllingerRobinson.PresentedFlexibleInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source
    (I : OllingerRobinson.PresentedFlexibleInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Encoded domino undecidability from a checked finite-data
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_checked_position_source
    (I : OllingerRobinson.CheckedPresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_position_source
    I.toPresentedInstance h

/--
Unencoded domino undecidability from a checked finite-data
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_checked_position_source
    (I : OllingerRobinson.CheckedPresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_position_source
    I.toPresentedInstance h

end TM0FoldedReduction

end LeanWang
