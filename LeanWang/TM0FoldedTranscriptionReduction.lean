/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Theorems
import LeanWang.OllingerRobinsonTranscription

/-!
Reduction wrappers for finite Ollinger/Robinson scaffold transcriptions.

`TM0FoldedReduction` is parameterized by abstract scaffold packages.  This file
connects those theorem surfaces to the checked finite-transcription package used
for the eventual Figure 13 data.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/--
Encoded domino undecidability from a checked flexible finite scaffold
transcription and generated position-coded source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source
    D.toPresentedFlexibleInstance h

/--
Unencoded domino undecidability from a checked flexible finite scaffold
transcription and generated position-coded source-route obligations.
-/
theorem domino_problem_undecidable_of_checked_flexible_transcription_position_source
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source
    D.toPresentedFlexibleInstance h

/--
Encoded domino undecidability from a checked flexible finite scaffold
transcription and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source_positionCodeInteriorRows
    D.toPresentedFlexibleInstance hinterior hcorrect

/--
Unencoded domino undecidability from a checked flexible finite scaffold
transcription and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source_positionCodeInteriorRows
    D.toPresentedFlexibleInstance hinterior hcorrect

end TM0FoldedReduction

end LeanWang
