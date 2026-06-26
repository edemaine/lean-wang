/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13Data
import LeanWang.TM0FoldedTranscriptionReduction

/-!
Reduction wrappers specialized to the concrete Figure 18 scaffold package.

This module is intentionally thin: it keeps the large folded reduction modules
unchanged while exposing theorem surfaces that take the eventual direct
`Figure18Instance`, layered Figure 18 instances, product-witness
`Figure18AdjacentProductWitnessInstance`, adjacent-compatible
`Figure18AdjacentCompatibleInstance`, indexed routed
`Figure18IndexedRoutedInstance`, routed `Figure18RoutedInstance`, or flexible
`Figure18FlexibleInstance` directly.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
an indexed free-square certificate and generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_position_source
    (I : OllingerRobinson.Figure18Instance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_position_source
    I.toPresentedInstance h

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with an indexed free-square certificate and generated position-coded
source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_position_source
    (I : OllingerRobinson.Figure18Instance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_position_source
    I.toPresentedInstance h

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
an indexed free-square certificate and the generated interior position-code
rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18_position_source_interiorRows
    (I : OllingerRobinson.Figure18Instance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    I.toPresentedInstance hinterior hcorrect

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with an indexed free-square certificate and the generated interior position-code
rows.
-/
theorem domino_problem_undecidable_of_figure18_position_source_interiorRows
    (I : OllingerRobinson.Figure18Instance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    I.toPresentedInstance hinterior hcorrect

/--
Encoded domino undecidability from a layered concrete Figure 18 scaffold
instance with an indexed free-square certificate and generated position-coded
source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_layered_figure18_position_source
    (I : OllingerRobinson.Figure13Layers.LayeredFigure18Instance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure18_position_source
    I.toFigure18Instance h

/--
Unencoded domino undecidability from a layered concrete Figure 18 scaffold
instance with an indexed free-square certificate and generated position-coded
source-route obligations.
-/
theorem domino_problem_undecidable_of_layered_figure18_position_source
    (I : OllingerRobinson.Figure13Layers.LayeredFigure18Instance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure18_position_source
    I.toFigure18Instance h

/--
Encoded domino undecidability from a layered concrete Figure 18 scaffold
instance with an indexed free-square certificate and the generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_layered_figure18_position_source_interiorRows
    (I : OllingerRobinson.Figure13Layers.LayeredFigure18Instance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure18_position_source_interiorRows
    I.toFigure18Instance hinterior hcorrect

/--
Unencoded domino undecidability from a layered concrete Figure 18 scaffold
instance with an indexed free-square certificate and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_layered_figure18_position_source_interiorRows
    (I : OllingerRobinson.Figure13Layers.LayeredFigure18Instance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure18_position_source_interiorRows
    I.toFigure18Instance hinterior hcorrect

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
an indexed routed free-coordinate certificate and generated position-coded
source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_indexed_routed_position_source
    (I : OllingerRobinson.Figure18IndexedRoutedInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with an indexed routed free-coordinate certificate and generated position-coded
source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_indexed_routed_position_source
    (I : OllingerRobinson.Figure18IndexedRoutedInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
an indexed routed free-coordinate certificate and the generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18_indexed_routed_position_source_interiorRows
    (I : OllingerRobinson.Figure18IndexedRoutedInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with an indexed routed free-coordinate certificate and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_figure18_indexed_routed_position_source_interiorRows
    (I : OllingerRobinson.Figure18IndexedRoutedInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Encoded domino undecidability from a layered concrete Figure 18 scaffold
instance with an indexed routed free-coordinate certificate and generated
position-coded source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_layered_figure18_indexed_routed_position_source
    (I : OllingerRobinson.Figure13Layers.LayeredFigure18IndexedRoutedInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure18_indexed_routed_position_source
    I.toFigure18IndexedRoutedInstance h

/--
Unencoded domino undecidability from a layered concrete Figure 18 scaffold
instance with an indexed routed free-coordinate certificate and generated
position-coded source-route obligations.
-/
theorem domino_problem_undecidable_of_layered_figure18_indexed_routed_position_source
    (I : OllingerRobinson.Figure13Layers.LayeredFigure18IndexedRoutedInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure18_indexed_routed_position_source
    I.toFigure18IndexedRoutedInstance h

/--
Encoded domino undecidability from a layered concrete Figure 18 scaffold
instance with an indexed routed free-coordinate certificate and the generated
interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_layered_figure18_indexed_routed_interiorRows
    (I : OllingerRobinson.Figure13Layers.LayeredFigure18IndexedRoutedInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure18_indexed_routed_position_source_interiorRows
    I.toFigure18IndexedRoutedInstance hinterior hcorrect

/--
Unencoded domino undecidability from a layered concrete Figure 18 scaffold
instance with an indexed routed free-coordinate certificate and the generated
interior position-code rows.
-/
theorem domino_problem_undecidable_of_layered_figure18_indexed_routed_position_source_interiorRows
    (I : OllingerRobinson.Figure13Layers.LayeredFigure18IndexedRoutedInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure18_indexed_routed_position_source_interiorRows
    I.toFigure18IndexedRoutedInstance hinterior hcorrect

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
an adjacent-compatible free-coordinate certificate and generated position-coded
source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_adjacent_compatible_position_source
    (I : OllingerRobinson.Figure18AdjacentCompatibleInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with an adjacent-compatible free-coordinate certificate and generated
position-coded source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_adjacent_compatible_position_source
    (I : OllingerRobinson.Figure18AdjacentCompatibleInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
an adjacent-compatible free-coordinate certificate and the generated interior
position-code rows.
-/
theorem
encoded_domino_problem_undecidable_of_figure18_adjacent_compatible_position_source_interiorRows
    (I : OllingerRobinson.Figure18AdjacentCompatibleInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with an adjacent-compatible free-coordinate certificate and the generated
interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure18_adjacent_compatible_position_source_interiorRows
    (I : OllingerRobinson.Figure18AdjacentCompatibleInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
an adjacent product-witness free-coordinate certificate and generated
position-coded source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_adjacent_product_witness_position_source
    (I : OllingerRobinson.Figure18AdjacentProductWitnessInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with an adjacent product-witness free-coordinate certificate and generated
position-coded source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_adjacent_product_witness_position_source
    (I : OllingerRobinson.Figure18AdjacentProductWitnessInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
an adjacent product-witness free-coordinate certificate and the generated
interior position-code rows.
-/
theorem
encoded_domino_problem_undecidable_of_figure18_adjacent_product_witness_position_source_interiorRows
    (I : OllingerRobinson.Figure18AdjacentProductWitnessInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with an adjacent product-witness free-coordinate certificate and the generated
interior position-code rows.
-/
theorem
domino_problem_undecidable_of_figure18_adjacent_product_witness_position_source_interiorRows
    (I : OllingerRobinson.Figure18AdjacentProductWitnessInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
a decoded-site free-coordinate certificate and generated position-coded
source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_decoded_site_position_source
    (I : OllingerRobinson.Figure18DecodedSiteInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with a decoded-site free-coordinate certificate and generated position-coded
source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_decoded_site_position_source
    (I : OllingerRobinson.Figure18DecodedSiteInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
a decoded-site free-coordinate certificate and the generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18_decoded_site_interiorRows
    (I : OllingerRobinson.Figure18DecodedSiteInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with a decoded-site free-coordinate certificate and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_figure18_decoded_site_interiorRows
    (I : OllingerRobinson.Figure18DecodedSiteInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Encoded domino undecidability from a concrete flat Figure 18 scaffold instance
with a decoded-site free-coordinate certificate and generated position-coded
source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_flat_decoded_site_position_source
    (I : OllingerRobinson.Figure18FlatDecodedSiteInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Unencoded domino undecidability from a concrete flat Figure 18 scaffold instance
with a decoded-site free-coordinate certificate and generated position-coded
source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_flat_decoded_site_position_source
    (I : OllingerRobinson.Figure18FlatDecodedSiteInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Encoded domino undecidability from a concrete flat Figure 18 scaffold instance
with a decoded-site free-coordinate certificate and the generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18_flat_decoded_site_interiorRows
    (I : OllingerRobinson.Figure18FlatDecodedSiteInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Unencoded domino undecidability from a concrete flat Figure 18 scaffold instance
with a decoded-site free-coordinate certificate and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_figure18_flat_decoded_site_interiorRows
    (I : OllingerRobinson.Figure18FlatDecodedSiteInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Encoded domino undecidability from a concrete listed active-site Figure 18
scaffold instance and generated position-coded source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_listed_active_site_position_source
    (I : OllingerRobinson.Figure18ListedActiveSiteInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Unencoded domino undecidability from a concrete listed active-site Figure 18
scaffold instance and generated position-coded source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_listed_active_site_position_source
    (I : OllingerRobinson.Figure18ListedActiveSiteInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Encoded domino undecidability from a concrete listed active-site Figure 18
scaffold instance and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18_listed_active_site_interiorRows
    (I : OllingerRobinson.Figure18ListedActiveSiteInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Unencoded domino undecidability from a concrete listed active-site Figure 18
scaffold instance and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure18_listed_active_site_interiorRows
    (I : OllingerRobinson.Figure18ListedActiveSiteInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Encoded domino undecidability from a concrete checked listed active-site Figure
18 scaffold instance and generated position-coded source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_checked_listed_active_site_position_source
    (I : OllingerRobinson.Figure18CheckedListedActiveSiteInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Unencoded domino undecidability from a concrete checked listed active-site Figure
18 scaffold instance and generated position-coded source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_checked_listed_active_site_position_source
    (I : OllingerRobinson.Figure18CheckedListedActiveSiteInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Encoded domino undecidability from a concrete checked listed active-site Figure
18 scaffold instance and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18_checked_listed_active_site_interiorRows
    (I : OllingerRobinson.Figure18CheckedListedActiveSiteInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Unencoded domino undecidability from a concrete checked listed active-site Figure
18 scaffold instance and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure18_checked_listed_active_site_interiorRows
    (I : OllingerRobinson.Figure18CheckedListedActiveSiteInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Encoded domino undecidability from concrete Figure 18 scaffold data, its two
geometric invariants, and generated position-coded source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_scaffold_data_position_source
    (D : OllingerRobinson.Figure18ScaffoldData) (certificate : D.Certificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure18_checked_listed_active_site_position_source
    (D.toCheckedListedActiveSiteInstance certificate) h

/--
Unencoded domino undecidability from concrete Figure 18 scaffold data, its two
geometric invariants, and generated position-coded source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_scaffold_data_position_source
    (D : OllingerRobinson.Figure18ScaffoldData) (certificate : D.Certificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure18_checked_listed_active_site_position_source
    (D.toCheckedListedActiveSiteInstance certificate) h

/--
Encoded domino undecidability from concrete Figure 18 scaffold data, its two
geometric invariants, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18_scaffold_data_interiorRows
    (D : OllingerRobinson.Figure18ScaffoldData) (certificate : D.Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure18_checked_listed_active_site_interiorRows
    (D.toCheckedListedActiveSiteInstance certificate) hinterior hcorrect

/--
Unencoded domino undecidability from concrete Figure 18 scaffold data, its two
geometric invariants, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure18_scaffold_data_interiorRows
    (D : OllingerRobinson.Figure18ScaffoldData) (certificate : D.Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure18_checked_listed_active_site_interiorRows
    (D.toCheckedListedActiveSiteInstance certificate) hinterior hcorrect

/--
Encoded domino undecidability from layered Figure 18 scaffold data, its direct
layered geometric certificate, and generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_layered_figure18_scaffold_data_position_source
    (D : OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData)
    (certificate : D.Certificate) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_layered_figure18_position_source
    certificate.toLayeredFigure18Instance h

/--
Unencoded domino undecidability from layered Figure 18 scaffold data, its direct
layered geometric certificate, and generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_layered_figure18_scaffold_data_position_source
    (D : OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData)
    (certificate : D.Certificate) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_layered_figure18_position_source
    certificate.toLayeredFigure18Instance h

/--
Encoded domino undecidability from layered Figure 18 scaffold data, its direct
layered geometric certificate, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_layered_figure18_scaffold_data_interiorRows
    (D : OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData)
    (certificate : D.Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_layered_figure18_position_source_interiorRows
    certificate.toLayeredFigure18Instance hinterior hcorrect

/--
Unencoded domino undecidability from layered Figure 18 scaffold data, its direct
layered geometric certificate, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_layered_figure18_scaffold_data_interiorRows
    (D : OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData)
    (certificate : D.Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_layered_figure18_position_source_interiorRows
    certificate.toLayeredFigure18Instance hinterior hcorrect

/--
Encoded domino undecidability from layered Figure 18 scaffold data, its
indexed-routed layered geometric certificate, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_position_source
    (D : OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData)
    (certificate : D.IndexedRoutedCertificate) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_layered_figure18_indexed_routed_position_source
    certificate.toLayeredFigure18IndexedRoutedInstance h

/--
Unencoded domino undecidability from layered Figure 18 scaffold data, its
indexed-routed layered geometric certificate, and generated position-coded
source-route obligations.
-/
theorem domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_position_source
    (D : OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData)
    (certificate : D.IndexedRoutedCertificate) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_layered_figure18_indexed_routed_position_source
    certificate.toLayeredFigure18IndexedRoutedInstance h

/--
Encoded domino undecidability from layered Figure 18 scaffold data, its
indexed-routed layered geometric certificate, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_interiorRows
    (D : OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData)
    (certificate : D.IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_layered_figure18_indexed_routed_interiorRows
    certificate.toLayeredFigure18IndexedRoutedInstance hinterior hcorrect

/--
Unencoded domino undecidability from layered Figure 18 scaffold data, its
indexed-routed layered geometric certificate, and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_interiorRows
    (D : OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData)
    (certificate : D.IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_layered_figure18_indexed_routed_position_source_interiorRows
    certificate.toLayeredFigure18IndexedRoutedInstance hinterior hcorrect

/--
Encoded domino undecidability from checked raw layered scaffold data, its direct
layered geometric certificate, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_checked_raw_layered_scaffold_position_source
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedRawData)
    (certificate : data.Certificate) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_layered_figure18_scaffold_data_position_source
    data.toLayeredFigure18ScaffoldData certificate h

/--
Unencoded domino undecidability from checked raw layered scaffold data, its
direct layered geometric certificate, and generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_checked_raw_layered_scaffold_position_source
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedRawData)
    (certificate : data.Certificate) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_layered_figure18_scaffold_data_position_source
    data.toLayeredFigure18ScaffoldData certificate h

/--
Encoded domino undecidability from checked raw layered scaffold data, its direct
layered geometric certificate, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_checked_raw_layered_scaffold_interiorRows
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedRawData)
    (certificate : data.Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_layered_figure18_scaffold_data_interiorRows
    data.toLayeredFigure18ScaffoldData certificate hinterior hcorrect

/--
Unencoded domino undecidability from checked raw layered scaffold data, its
direct layered geometric certificate, and the generated interior position-code
rows.
-/
theorem domino_problem_undecidable_of_checked_raw_layered_scaffold_interiorRows
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedRawData)
    (certificate : data.Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_layered_figure18_scaffold_data_interiorRows
    data.toLayeredFigure18ScaffoldData certificate hinterior hcorrect

/--
Encoded domino undecidability from checked raw layered scaffold data, its
indexed-routed layered geometric certificate, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_checked_raw_indexed_routed_position_source
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedRawData)
    (certificate : data.IndexedRoutedCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_position_source
    data.toLayeredFigure18ScaffoldData certificate h

/--
Unencoded domino undecidability from checked raw layered scaffold data, its
indexed-routed layered geometric certificate, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_checked_raw_indexed_routed_position_source
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedRawData)
    (certificate : data.IndexedRoutedCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_position_source
    data.toLayeredFigure18ScaffoldData certificate h

/--
Encoded domino undecidability from checked raw layered scaffold data, its
indexed-routed layered geometric certificate, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_checked_raw_indexed_routed_interiorRows
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedRawData)
    (certificate : data.IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_interiorRows
    data.toLayeredFigure18ScaffoldData certificate hinterior hcorrect

/--
Unencoded domino undecidability from checked raw layered scaffold data, its
indexed-routed layered geometric certificate, and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_checked_raw_indexed_routed_interiorRows
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedRawData)
    (certificate : data.IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_interiorRows
    data.toLayeredFigure18ScaffoldData certificate hinterior hcorrect

/--
Encoded domino undecidability from sparse checked raw layered scaffold data,
its direct layered geometric certificate, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_checked_sparse_raw_layered_scaffold_position_source
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseRawData)
    (certificate : data.Certificate) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_raw_layered_scaffold_position_source
    data.toCheckedRawData certificate h

/--
Unencoded domino undecidability from sparse checked raw layered scaffold data,
its direct layered geometric certificate, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_checked_sparse_raw_layered_scaffold_position_source
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseRawData)
    (certificate : data.Certificate) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_raw_layered_scaffold_position_source
    data.toCheckedRawData certificate h

/--
Encoded domino undecidability from sparse checked raw layered scaffold data,
its direct layered geometric certificate, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_checked_sparse_raw_layered_scaffold_interiorRows
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseRawData)
    (certificate : data.Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_raw_layered_scaffold_interiorRows
    data.toCheckedRawData certificate hinterior hcorrect

/--
Unencoded domino undecidability from sparse checked raw layered scaffold data,
its direct layered geometric certificate, and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_checked_sparse_raw_layered_scaffold_interiorRows
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseRawData)
    (certificate : data.Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_raw_layered_scaffold_interiorRows
    data.toCheckedRawData certificate hinterior hcorrect

/--
Encoded domino undecidability from sparse checked raw layered scaffold data,
its indexed-routed layered geometric certificate, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_position_source
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseRawData)
    (certificate : data.IndexedRoutedCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_raw_indexed_routed_position_source
    data.toCheckedRawData certificate h

/--
Unencoded domino undecidability from sparse checked raw layered scaffold data,
its indexed-routed layered geometric certificate, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_position_source
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseRawData)
    (certificate : data.IndexedRoutedCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_raw_indexed_routed_position_source
    data.toCheckedRawData certificate h

/--
Encoded domino undecidability from sparse checked raw layered scaffold data,
its indexed-routed layered geometric certificate, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_interiorRows
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseRawData)
    (certificate : data.IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_raw_indexed_routed_interiorRows
    data.toCheckedRawData certificate hinterior hcorrect

/--
Unencoded domino undecidability from sparse checked raw layered scaffold data,
its indexed-routed layered geometric certificate, and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_interiorRows
    (data :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseRawData)
    (certificate : data.IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_raw_indexed_routed_interiorRows
    data.toCheckedRawData certificate hinterior hcorrect

/--
Encoded domino undecidability from the preferred concrete sparse layered data
entry shape: sparse Figure 13 layer rows, checked active Figure 18 sites, a
typed corner site, an indexed-routed layered geometric certificate, and
generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_checked_sparse_sites_indexed_routed_position_source
    (layerRows :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseLayerRows)
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.checkedSparseScaffoldDataOfSites
        layerRows activeSiteData cornerSite).IndexedRoutedCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_position_source
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.checkedSparseScaffoldDataOfSites
        layerRows activeSiteData cornerSite)
      certificate h

/--
Unencoded domino undecidability from the preferred concrete sparse layered data
entry shape: sparse Figure 13 layer rows, checked active Figure 18 sites, a
typed corner site, an indexed-routed layered geometric certificate, and
generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_checked_sparse_sites_indexed_routed_position_source
    (layerRows :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseLayerRows)
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.checkedSparseScaffoldDataOfSites
        layerRows activeSiteData cornerSite).IndexedRoutedCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_position_source
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.checkedSparseScaffoldDataOfSites
        layerRows activeSiteData cornerSite)
      certificate h

/--
Encoded domino undecidability from the preferred concrete sparse layered data
entry shape and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_checked_sparse_sites_indexed_routed_interiorRows
    (layerRows :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseLayerRows)
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.checkedSparseScaffoldDataOfSites
        layerRows activeSiteData cornerSite).IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_interiorRows
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.checkedSparseScaffoldDataOfSites
        layerRows activeSiteData cornerSite)
      certificate hinterior hcorrect

/--
Unencoded domino undecidability from the preferred concrete sparse layered data
entry shape and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_checked_sparse_sites_indexed_routed_interiorRows
    (layerRows :
      OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.CheckedSparseLayerRows)
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.checkedSparseScaffoldDataOfSites
        layerRows activeSiteData cornerSite).IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_interiorRows
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.checkedSparseScaffoldDataOfSites
        layerRows activeSiteData cornerSite)
      certificate hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, an indexed-routed
layered geometric certificate, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData.sparseRawDataOfSites
        activeSiteData cornerSite).IndexedRoutedCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_position_source
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData.sparseRawDataOfSites
        activeSiteData cornerSite)
      certificate h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, an indexed-routed
layered geometric certificate, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData.sparseRawDataOfSites
        activeSiteData cornerSite).IndexedRoutedCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_position_source
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData.sparseRawDataOfSites
        activeSiteData cornerSite)
      certificate h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData.sparseRawDataOfSites
        activeSiteData cornerSite).IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_interiorRows
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData.sparseRawDataOfSites
        activeSiteData cornerSite)
      certificate hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData.sparseRawDataOfSites
        activeSiteData cornerSite).IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_interiorRows
      (OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData.sparseRawDataOfSites
        activeSiteData cornerSite)
      certificate hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, checked indexed
routed stack witnesses, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_checked_routed_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasIndexedRoutedFixedCornerSquareCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, checked indexed
routed stack witnesses, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_checked_routed_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasIndexedRoutedFixedCornerSquareCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, checked indexed
routed stack witnesses, realization, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_checked_routed_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasIndexedRoutedFixedCornerSquareCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_interiorRows
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, checked indexed
routed stack witnesses, realization, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_checked_routed_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasIndexedRoutedFixedCornerSquareCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_interiorRows
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, a plain Figure 18
scaffold certificate, and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_scaffold_data_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (figure18ScaffoldDataOfSites activeSiteData cornerSite).Certificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure18_scaffold_data_position_source
      (figure18ScaffoldDataOfSites activeSiteData cornerSite)
      certificate h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, a plain Figure 18
scaffold certificate, and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_concrete_figure13_sites_scaffold_data_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (figure18ScaffoldDataOfSites activeSiteData cornerSite).Certificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure18_scaffold_data_position_source
      (figure18ScaffoldDataOfSites activeSiteData cornerSite)
      certificate h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, a plain Figure 18
scaffold certificate, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_scaffold_data_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (figure18ScaffoldDataOfSites activeSiteData cornerSite).Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure18_scaffold_data_interiorRows
      (figure18ScaffoldDataOfSites activeSiteData cornerSite)
      certificate hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, a plain Figure 18
scaffold certificate, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_concrete_figure13_sites_scaffold_data_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (certificate :
      (figure18ScaffoldDataOfSites activeSiteData cornerSite).Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure18_scaffold_data_interiorRows
      (figure18ScaffoldDataOfSites activeSiteData cornerSite)
      certificate hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, indexed
active-corner windows, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_indexed_windows_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfSites activeSiteData cornerSite).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfSites activeSiteData cornerSite).HasRealizationInvariant)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_scaffold_data_position_source
      activeSiteData cornerSite
      (figure18ScaffoldDataOfSitesCertificateOfIndexedActiveWindows
        activeSiteData cornerSite indexedActiveWindows realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, indexed
active-corner windows, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_indexed_windows_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfSites activeSiteData cornerSite).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfSites activeSiteData cornerSite).HasRealizationInvariant)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_scaffold_data_position_source
      activeSiteData cornerSite
      (figure18ScaffoldDataOfSitesCertificateOfIndexedActiveWindows
        activeSiteData cornerSite indexedActiveWindows realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, indexed
active-corner windows, realization, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_indexed_windows_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfSites activeSiteData cornerSite).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfSites activeSiteData cornerSite).HasRealizationInvariant)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_scaffold_data_interiorRows
      activeSiteData cornerSite
      (figure18ScaffoldDataOfSitesCertificateOfIndexedActiveWindows
        activeSiteData cornerSite indexedActiveWindows realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, indexed
active-corner windows, realization, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_indexed_windows_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfSites activeSiteData cornerSite).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfSites activeSiteData cornerSite).HasRealizationInvariant)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_scaffold_data_interiorRows
      activeSiteData cornerSite
      (figure18ScaffoldDataOfSitesCertificateOfIndexedActiveWindows
        activeSiteData cornerSite indexedActiveWindows realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, an
indexed-routed layered geometric certificate, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (sparseRawDataOfNatSites
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid).IndexedRoutedCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_position_source
      (sparseRawDataOfNatSites
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid)
      certificate h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, an
indexed-routed layered geometric certificate, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (sparseRawDataOfNatSites
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid).IndexedRoutedCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_position_source
      (sparseRawDataOfNatSites
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid)
      certificate h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, and the
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (sparseRawDataOfNatSites
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid).IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_interiorRows
      (sparseRawDataOfNatSites
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid)
      certificate hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, and the
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (sparseRawDataOfNatSites
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid).IndexedRoutedCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_checked_sparse_raw_indexed_routed_interiorRows
      (sparseRawDataOfNatSites
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid)
      certificate hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, checked
indexed routed stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_checked_routed_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasIndexedRoutedFixedCornerSquareCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, checked
indexed routed stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_checked_routed_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasIndexedRoutedFixedCornerSquareCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, checked
indexed routed stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_checked_routed_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasIndexedRoutedFixedCornerSquareCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, checked
indexed routed stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_checked_routed_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasIndexedRoutedFixedCornerSquareCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_scaffold_data_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure18_scaffold_data_position_source
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
      certificate h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_concrete_figure13_nat_sites_scaffold_data_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure18_scaffold_data_position_source
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
      certificate h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_scaffold_data_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure18_scaffold_data_interiorRows
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
      certificate hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_concrete_figure13_nat_sites_scaffold_data_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure18_scaffold_data_interiorRows
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
      certificate hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, indexed
active-corner windows, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_scaffold_data_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (figure18ScaffoldDataOfNatSitesCertificateOfIndexedActiveWindows
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid indexedActiveWindows realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, indexed
active-corner windows, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_nat_sites_scaffold_data_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (figure18ScaffoldDataOfNatSitesCertificateOfIndexedActiveWindows
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid indexedActiveWindows realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, indexed
active-corner windows, realization, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_scaffold_data_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (figure18ScaffoldDataOfNatSitesCertificateOfIndexedActiveWindows
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid indexedActiveWindows realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, indexed
active-corner windows, realization, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_nat_sites_scaffold_data_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (figure18ScaffoldDataOfNatSitesCertificateOfIndexedActiveWindows
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid indexedActiveWindows realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from a concrete flat Figure 18 scaffold instance
with an active-site free-coordinate certificate and generated position-coded
source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_flat_active_site_position_source
    (I : OllingerRobinson.Figure18FlatActiveSiteInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Unencoded domino undecidability from a concrete flat Figure 18 scaffold instance
with an active-site free-coordinate certificate and generated position-coded
source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_flat_active_site_position_source
    (I : OllingerRobinson.Figure18FlatActiveSiteInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Encoded domino undecidability from a concrete flat Figure 18 scaffold instance
with an active-site free-coordinate certificate and the generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18_flat_active_site_interiorRows
    (I : OllingerRobinson.Figure18FlatActiveSiteInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Unencoded domino undecidability from a concrete flat Figure 18 scaffold instance
with an active-site free-coordinate certificate and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_figure18_flat_active_site_interiorRows
    (I : OllingerRobinson.Figure18FlatActiveSiteInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
a routed free-coordinate certificate and generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_routed_position_source
    (I : OllingerRobinson.Figure18RoutedInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with a routed free-coordinate certificate and generated position-coded
source-route obligations.
-/
theorem domino_problem_undecidable_of_figure18_routed_position_source
    (I : OllingerRobinson.Figure18RoutedInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.toFlexibleInstance.checkedFlexibleTranscription h

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
a routed free-coordinate certificate and the generated interior position-code
rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18_routed_position_source_interiorRows
    (I : OllingerRobinson.Figure18RoutedInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with a routed free-coordinate certificate and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_figure18_routed_position_source_interiorRows
    (I : OllingerRobinson.Figure18RoutedInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.toFlexibleInstance.checkedFlexibleTranscription hinterior hcorrect

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
a flexible certificate and generated position-coded source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure18_flexible_position_source
    (I : OllingerRobinson.Figure18FlexibleInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.checkedFlexibleTranscription h

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with a flexible certificate and generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_figure18_flexible_position_source
    (I : OllingerRobinson.Figure18FlexibleInstance)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_flexible_transcription_position_source
    I.checkedFlexibleTranscription h

/--
Encoded domino undecidability from a concrete Figure 18 scaffold instance with
a flexible certificate and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18_flexible_position_source_interiorRows
    (I : OllingerRobinson.Figure18FlexibleInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.checkedFlexibleTranscription hinterior hcorrect

/--
Unencoded domino undecidability from a concrete Figure 18 scaffold instance
with a flexible certificate and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure18_flexible_position_source_interiorRows
    (I : OllingerRobinson.Figure18FlexibleInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
    I.checkedFlexibleTranscription hinterior hcorrect

/-
The fully discharged `positionProgramData`-correct variants are available by
first applying `I.checkedFlexibleTranscription` to the checked-transcription
theorems in `TM0FoldedPositionReduction`. They are kept out of this module so
this Figure 18 integration layer does not force the large semantic proof file to
rebuild whenever the finite scaffold package changes.
-/

end TM0FoldedReduction

end LeanWang
