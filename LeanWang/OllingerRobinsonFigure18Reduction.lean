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
table, checked active Figure 18 sites, a typed corner site, adjacent
product-witness stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_product_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasAdjacentProductWitnessCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, adjacent
product-witness stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_product_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasAdjacentProductWitnessCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, adjacent
product-witness stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_product_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasAdjacentProductWitnessCheckedStacks
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, adjacent
product-witness stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_product_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasAdjacentProductWitnessCheckedStacks
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, decoded-site stack
witnesses, realization, and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_decoded_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasDecodedSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfDecodedSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, decoded-site stack
witnesses, realization, and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_decoded_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasDecodedSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfDecodedSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, decoded-site stack
witnesses, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_decoded_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasDecodedSiteCheckedStacks
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfDecodedSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, decoded-site stack
witnesses, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_decoded_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasDecodedSiteCheckedStacks
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfDecodedSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, flat decoded-site
stack witnesses, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_flat_decoded_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasFlatDecodedSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).flatTable)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, flat decoded-site
stack witnesses, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_flat_decoded_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasFlatDecodedSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).flatTable)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, flat decoded-site
stack witnesses, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_flat_decoded_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasFlatDecodedSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).flatTable)
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, flat decoded-site
stack witnesses, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_flat_decoded_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasFlatDecodedSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).flatTable)
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, flat active-site
stack witnesses, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_flat_active_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasFlatActiveSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).flatTable)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfFlatActiveSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, flat active-site
stack witnesses, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_flat_active_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasFlatActiveSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).flatTable)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfFlatActiveSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, flat active-site
stack witnesses, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_flat_active_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasFlatActiveSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).flatTable)
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfFlatActiveSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, flat active-site
stack witnesses, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_flat_active_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasFlatActiveSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).flatTable)
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfFlatActiveSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
stack witnesses, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_listed_active_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasListedActiveSiteCheckedStacks
          activeSiteData.sites cornerSite)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
stack witnesses, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_listed_active_stacks_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasListedActiveSiteCheckedStacks
          activeSiteData.sites cornerSite)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
stack witnesses, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_listed_active_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasListedActiveSiteCheckedStacks
          activeSiteData.sites cornerSite)
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
stack witnesses, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_listed_active_stacks_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hchecked :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasListedActiveSiteCheckedStacks
          activeSiteData.sites cornerSite)
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
        activeSiteData cornerSite hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
windows, finite stack certificates for those windows, realization, and
generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_listed_active_windows_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hstacks :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasCheckedStacksForListedActiveSiteWindows
          activeSiteData.sites cornerSite)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteWindows
        activeSiteData cornerSite hwindows hstacks realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
windows, finite stack certificates for those windows, realization, and
generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_listed_active_windows_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hstacks :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasCheckedStacksForListedActiveSiteWindows
          activeSiteData.sites cornerSite)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteWindows
        activeSiteData cornerSite hwindows hstacks realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
windows, finite stack certificates for those windows, realization, and the
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_listed_active_windows_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hstacks :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasCheckedStacksForListedActiveSiteWindows
          activeSiteData.sites cornerSite)
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteWindows
        activeSiteData cornerSite hwindows hstacks realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
windows, finite stack certificates for those windows, realization, and the
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_listed_active_windows_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hstacks :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasCheckedStacksForListedActiveSiteWindows
          activeSiteData.sites cornerSite)
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteWindows
        activeSiteData cornerSite hwindows hstacks realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
windows, finite rectangle stack checks, realization, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_listed_rectangles_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hrectangles :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasCheckedStacksForListedActiveSiteRectangles
          activeSiteData.sites cornerSite)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
        activeSiteData cornerSite hwindows hrectangles realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
windows, finite rectangle stack checks, realization, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_listed_rectangles_position_source
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hrectangles :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasCheckedStacksForListedActiveSiteRectangles
          activeSiteData.sites cornerSite)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_sites_indexed_routed_position_source
      activeSiteData cornerSite
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
        activeSiteData cornerSite hwindows hrectangles realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
windows, finite rectangle stack checks, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_sites_listed_rectangles_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hrectangles :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasCheckedStacksForListedActiveSiteRectangles
          activeSiteData.sites cornerSite)
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
        activeSiteData cornerSite hwindows hrectangles realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, checked active Figure 18 sites, a typed corner site, listed active-site
windows, finite rectangle stack checks, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_sites_listed_rectangles_interiorRows
    (activeSiteData : OllingerRobinson.Figure18Site.CheckedNatSpecs)
    (cornerSite : OllingerRobinson.Figure18Site)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hrectangles :
      (sparseRawDataOfSites activeSiteData
        cornerSite).HasCheckedStacksForListedActiveSiteRectangles
          activeSiteData.sites cornerSite)
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
      (scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
        activeSiteData cornerSite hwindows hrectangles realizes)
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
table, raw checked active Figure 18 site specs, a raw checked corner, a routed
free-coordinate certificate, and generated position-coded source-route
obligations.

This is the direct Figure 18 scaffold surface for the paper's selected
free-coordinate argument; it does not require adjacent selected coordinates.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      OllingerRobinson.Figure18RoutedCertificate
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  let I : OllingerRobinson.Figure18RoutedInstance := {
    table := (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).table
    certificate := certificate
  }
  exact
    encoded_domino_problem_undecidable_of_checked_flexible_transcription_position_source
      I.toFlexibleInstance.checkedFlexibleTranscription
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a routed
free-coordinate certificate, and generated position-coded source-route
obligations.

This is the direct Figure 18 scaffold surface for the paper's selected
free-coordinate argument; it does not require adjacent selected coordinates.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      OllingerRobinson.Figure18RoutedCertificate
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  let I : OllingerRobinson.Figure18RoutedInstance := {
    table := (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).table
    certificate := certificate
  }
  exact
    domino_problem_undecidable_of_checked_flexible_transcription_position_source
      I.toFlexibleInstance.checkedFlexibleTranscription
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a routed
free-coordinate certificate, and the generated interior position-code rows.

This is the direct Figure 18 scaffold surface for the paper's selected
free-coordinate argument; it does not require adjacent selected coordinates.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      OllingerRobinson.Figure18RoutedCertificate
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  let I : OllingerRobinson.Figure18RoutedInstance := {
    table := (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).table
    certificate := certificate
  }
  exact
    encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
      I.toFlexibleInstance.checkedFlexibleTranscription
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a routed
free-coordinate certificate, and the generated interior position-code rows.

This is the direct Figure 18 scaffold surface for the paper's selected
free-coordinate argument; it does not require adjacent selected coordinates.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_routed_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      OllingerRobinson.Figure18RoutedCertificate
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  let I : OllingerRobinson.Figure18RoutedInstance := {
    table := (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).table
    certificate := certificate
  }
  exact
    domino_problem_undecidable_of_checked_transcription_position_source_interiorRows
      I.toFlexibleInstance.checkedFlexibleTranscription
      hinterior hcorrect

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
table, raw checked active Figure 18 site specs, a raw checked corner, routed
fixed-corner squares with allowed compatible site rectangles, finite generated
stack pair compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_allowed_routed_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hallowed :
      HasAllowedIndexedRoutedFixedCornerSquares
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfAllowedRouted
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hpair hallowed realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, routed
fixed-corner squares with allowed compatible site rectangles, finite generated
stack pair compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_allowed_routed_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hallowed :
      HasAllowedIndexedRoutedFixedCornerSquares
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfAllowedRouted
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hpair hallowed realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, routed
fixed-corner squares with allowed compatible site rectangles, finite generated
stack pair compatibility, realization, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_allowed_routed_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hallowed :
      HasAllowedIndexedRoutedFixedCornerSquares
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfAllowedRouted
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hpair hallowed realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, routed
fixed-corner squares with allowed compatible site rectangles, finite generated
stack pair compatibility, realization, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_allowed_routed_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hallowed :
      HasAllowedIndexedRoutedFixedCornerSquares
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfAllowedRouted
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hpair hallowed realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site fixed-corner squares, finite generated stack pair compatibility,
realization, and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_listed_active_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hlisted :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquares
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSite
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hpair hlisted realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site fixed-corner squares, finite generated stack pair compatibility,
realization, and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_listed_active_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hlisted :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquares
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSite
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hpair hlisted realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site fixed-corner squares, finite generated stack pair compatibility,
realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_listed_active_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hlisted :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquares
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSite
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hpair hlisted realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site fixed-corner squares, finite generated stack pair compatibility,
realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_listed_active_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hlisted :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquares
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSite
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hpair hlisted realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, adjacent
product-witness stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_product_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasAdjacentProductWitnessCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, adjacent
product-witness stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_product_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasAdjacentProductWitnessCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, adjacent
product-witness stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_product_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasAdjacentProductWitnessCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, adjacent
product-witness stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_product_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasAdjacentProductWitnessCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner,
decoded-site stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_decoded_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasDecodedSiteCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfDecodedSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner,
decoded-site stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_decoded_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasDecodedSiteCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfDecodedSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner,
decoded-site stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_decoded_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasDecodedSiteCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfDecodedSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner,
decoded-site stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_decoded_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasDecodedSiteCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfDecodedSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, flat
decoded-site stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_flat_decoded_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasFlatDecodedSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).flatTable)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, flat
decoded-site stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_flat_decoded_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasFlatDecodedSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).flatTable)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, flat
decoded-site stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_flat_decoded_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasFlatDecodedSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).flatTable)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, flat
decoded-site stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_flat_decoded_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasFlatDecodedSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).flatTable)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, flat
active-site stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_flat_active_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasFlatActiveSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).flatTable)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatActiveSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, flat
active-site stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_flat_active_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasFlatActiveSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).flatTable)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatActiveSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, flat
active-site stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_flat_active_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasFlatActiveSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).flatTable)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatActiveSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, flat
active-site stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_flat_active_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasFlatActiveSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).flatTable)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatActiveSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_listed_active_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasListedActiveSiteCheckedStacks
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site stack witnesses, realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_listed_active_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasListedActiveSiteCheckedStacks
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_listed_active_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasListedActiveSiteCheckedStacks
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site stack witnesses, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_listed_active_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasListedActiveSiteCheckedStacks
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite stack certificates for those windows, realization,
and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_listed_active_windows_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForListedActiveSiteWindows
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteWindows
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hstacks realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite stack certificates for those windows, realization,
and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_listed_active_windows_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForListedActiveSiteWindows
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteWindows
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hstacks realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite stack certificates for those windows, realization,
and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_listed_active_windows_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForListedActiveSiteWindows
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteWindows
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hstacks realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite stack certificates for those windows, realization,
and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_listed_active_windows_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForListedActiveSiteWindows
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteWindows
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hstacks realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite rectangle stack checks, realization, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_listed_rectangles_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hrectangles :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForListedActiveSiteRectangles
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hrectangles realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite rectangle stack checks, realization, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_listed_rectangles_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hrectangles :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForListedActiveSiteRectangles
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hrectangles realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite rectangle stack checks, realization, and the
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_listed_rectangles_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hrectangles :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForListedActiveSiteRectangles
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hrectangles realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite rectangle stack checks, realization, and the
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_listed_rectangles_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hrectangles :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForListedActiveSiteRectangles
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hrectangles realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite generated-stack pair compatibility, realization,
and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_listed_pair_compat_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) = true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSitePairCompatibility
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hpair realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite generated-stack pair compatibility, realization,
and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_listed_pair_compat_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) = true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSitePairCompatibility
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hpair realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite generated-stack pair compatibility, realization,
and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_listed_pair_compat_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) = true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSitePairCompatibility
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hpair realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, listed
active-site windows, finite generated-stack pair compatibility, realization,
and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_listed_pair_compat_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) = true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSitePairCompatibility
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hwindows hpair realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, listed active-site windows, finite
generated-stack pair compatibility, realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_flat_table_pair_compat_position_source
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        table.activeSiteData.sites table.cornerSite)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfFlatRoleTable table).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_position_source
      (scaffoldDataOfFlatRoleTable table)
      (scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfListedPairCompatibility
        table hwindows hpair realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, listed active-site windows, finite
generated-stack pair compatibility, realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_flat_table_pair_compat_position_source
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        table.activeSiteData.sites table.cornerSite)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfFlatRoleTable table).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_position_source
      (scaffoldDataOfFlatRoleTable table)
      (scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfListedPairCompatibility
        table hwindows hpair realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, listed active-site windows, finite
generated-stack pair compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_flat_table_pair_compat_interiorRows
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        table.activeSiteData.sites table.cornerSite)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfFlatRoleTable table).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_interiorRows
      (scaffoldDataOfFlatRoleTable table)
      (scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfListedPairCompatibility
        table hwindows hpair realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, listed active-site windows, finite
generated-stack pair compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_flat_table_pair_compat_interiorRows
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (hwindows :
      OllingerRobinson.HasFigure18ListedActiveSiteFixedCornerSquareWindows
        table.activeSiteData.sites table.cornerSite)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfFlatRoleTable table).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_interiorRows
      (scaffoldDataOfFlatRoleTable table)
      (scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfListedPairCompatibility
        table hwindows hpair realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, bundled flat-table scaffold obligations,
and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_flat_table_obligations_position_source
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (obligations : FlatRoleTableObligations table)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_position_source
      (scaffoldDataOfFlatRoleTable table)
      (scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfObligations
        table obligations)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, bundled flat-table scaffold obligations,
and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_flat_table_obligations_position_source
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (obligations : FlatRoleTableObligations table)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_position_source
      (scaffoldDataOfFlatRoleTable table)
      (scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfObligations
        table obligations)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, bundled flat-table scaffold obligations,
and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_flat_table_obligations_interiorRows
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (obligations : FlatRoleTableObligations table)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_interiorRows
      (scaffoldDataOfFlatRoleTable table)
      (scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfObligations
        table obligations)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, bundled flat-table scaffold obligations,
and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_flat_table_obligations_interiorRows
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (obligations : FlatRoleTableObligations table)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_layered_scaffold_data_indexed_routed_interiorRows
      (scaffoldDataOfFlatRoleTable table)
      (scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfObligations
        table obligations)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, a plain scaffold certificate, finite
generated-stack pair compatibility, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_flat_table_cert_pair_position_source
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_flat_table_obligations_position_source
      table
      (FlatRoleTableObligations.ofCertificate table certificate hpair)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, a plain scaffold certificate, finite
generated-stack pair compatibility, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_flat_table_cert_pair_position_source
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_flat_table_obligations_position_source
      table
      (FlatRoleTableObligations.ofCertificate table certificate hpair)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, a plain scaffold certificate, finite
generated-stack pair compatibility, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_flat_table_cert_pair_interiorRows
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_flat_table_obligations_interiorRows
      table
      (FlatRoleTableObligations.ofCertificate table certificate hpair)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, a plain scaffold certificate, finite
generated-stack pair compatibility, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_flat_table_cert_pair_interiorRows
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_flat_table_obligations_interiorRows
      table
      (FlatRoleTableObligations.ofCertificate table certificate hpair)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, a plain scaffold certificate, no finite
generated-stack pair failures, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_flat_table_cert_failures_position_source
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        table.activeSiteData table.cornerSite = [])
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_flat_table_obligations_position_source
      table
      (FlatRoleTableObligations.ofCertificateFailures
        table certificate hfailures)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, a plain scaffold certificate, no finite
generated-stack pair failures, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_flat_table_cert_failures_position_source
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        table.activeSiteData table.cornerSite = [])
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_flat_table_obligations_position_source
      table
      (FlatRoleTableObligations.ofCertificateFailures
        table certificate hfailures)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, a plain scaffold certificate, no finite
generated-stack pair failures, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_flat_table_cert_failures_interiorRows
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        table.activeSiteData table.cornerSite = [])
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_flat_table_obligations_interiorRows
      table
      (FlatRoleTableObligations.ofCertificateFailures
        table certificate hfailures)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, a flat Figure 18 role table, a plain scaffold certificate, no finite
generated-stack pair failures, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_flat_table_cert_failures_interiorRows
    (table : OllingerRobinson.Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        table.activeSiteData table.cornerSite = [])
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_flat_table_obligations_interiorRows
      table
      (FlatRoleTableObligations.ofCertificateFailures
        table certificate hfailures)
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
table, raw checked active Figure 18 site specs, a raw checked corner, bundled
Nat-site scaffold obligations, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_obligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, bundled
Nat-site scaffold obligations, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_obligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      h

/--
Encoded domino undecidability from bundled Nat-site scaffold obligations,
using the generated flat-table active-site route.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_flat_table_obligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      h

/--
Unencoded domino undecidability from bundled Nat-site scaffold obligations,
using the generated flat-table active-site route.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_flat_table_obligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, bundled
Nat-site scaffold obligations, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_obligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, bundled
Nat-site scaffold obligations, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_obligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      hinterior hcorrect

/--
Encoded domino undecidability from bundled Nat-site scaffold obligations,
using the generated flat-table active-site route and generated interior rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_flat_table_obligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      hinterior hcorrect

/--
Unencoded domino undecidability from bundled Nat-site scaffold obligations,
using the generated flat-table active-site route and generated interior rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_flat_table_obligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, finite generated-stack pair compatibility, and
generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_cert_pair_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfCertificatePairCompatibility
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid certificate hpair)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, finite generated-stack pair compatibility, and
generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_cert_pair_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfCertificatePairCompatibility
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid certificate hpair)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, finite generated-stack pair compatibility, and
the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_cert_pair_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfCertificatePairCompatibility
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid certificate hpair)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, finite generated-stack pair compatibility, and
the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_cert_pair_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfCertificatePairCompatibility
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid certificate hpair)
      hinterior hcorrect

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, no finite generated-stack pair failures, and
generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_cert_failures_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          [])
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_flat_table_obligations_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteObligations.ofCertificateFailures
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid certificate hfailures)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, no finite generated-stack pair failures, and
generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_cert_failures_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          [])
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_flat_table_obligations_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteObligations.ofCertificateFailures
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid certificate hfailures)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, no finite generated-stack pair failures, and
the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_cert_failures_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          [])
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_flat_table_obligations_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteObligations.ofCertificateFailures
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid certificate hfailures)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a plain
Figure 18 scaffold certificate, no finite generated-stack pair failures, and
the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_cert_failures_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          [])
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_flat_table_obligations_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteObligations.ofCertificateFailures
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid certificate hfailures)
      hinterior hcorrect

/--
Encoded domino undecidability from a bundled concrete Figure 13/Figure 18
Nat-site scaffold certificate and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_site_scaffold_certificate_position_source
    (C : NatSiteScaffoldCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
      C.activeSiteSpecs C.activeSiteSpecs_valid
      C.cornerIndex C.cornerQuadrant C.cornerIndex_valid
      C.indexedRoutedCertificate
      h

/--
Unencoded domino undecidability from a bundled concrete Figure 13/Figure 18
Nat-site scaffold certificate and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_site_scaffold_certificate_position_source
    (C : NatSiteScaffoldCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_concrete_figure13_nat_sites_indexed_routed_position_source
      C.activeSiteSpecs C.activeSiteSpecs_valid
      C.cornerIndex C.cornerQuadrant C.cornerIndex_valid
      C.indexedRoutedCertificate
      h

/--
Encoded domino undecidability from a bundled concrete Figure 13/Figure 18
Nat-site scaffold certificate and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_site_scaffold_certificate_interiorRows
    (C : NatSiteScaffoldCertificate)
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
      C.activeSiteSpecs C.activeSiteSpecs_valid
      C.cornerIndex C.cornerQuadrant C.cornerIndex_valid
      C.indexedRoutedCertificate
      hinterior hcorrect

/--
Unencoded domino undecidability from a bundled concrete Figure 13/Figure 18
Nat-site scaffold certificate and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_site_scaffold_certificate_interiorRows
    (C : NatSiteScaffoldCertificate)
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
      C.activeSiteSpecs C.activeSiteSpecs_valid
      C.cornerIndex C.cornerQuadrant C.cornerIndex_valid
      C.indexedRoutedCertificate
      hinterior hcorrect

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
