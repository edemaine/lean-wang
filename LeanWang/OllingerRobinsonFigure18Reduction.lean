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
open OllingerRobinson
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
free-coordinate certificate, and the generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_decoderStep
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      OllingerRobinson.Figure18RoutedCertificate
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid certificate
      (positionSourceObligationsOfPositionCodeDecoderStep hstep hcorrect)

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, a routed
free-coordinate certificate, and the generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_routed_decoderStep
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      OllingerRobinson.Figure18RoutedCertificate
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid certificate
      (positionSourceObligationsOfPositionCodeDecoderStep hstep hcorrect)

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
table, raw checked active Figure 18 site specs, a raw checked corner, Robinson
board routed free-grid witnesses carrying checked stacks, realization, and
generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_robinson_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasRobinsonBoardRoutedFreeGridCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, Robinson
board routed free-grid witnesses carrying checked stacks, realization, and
generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_robinson_board_routed_stacks_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasRobinsonBoardRoutedFreeGridCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      h

/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, Robinson
board routed free-grid witnesses carrying checked stacks, realization, and the
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_nat_sites_robinson_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasRobinsonBoardRoutedFreeGridCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hchecked realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, a raw checked corner, Robinson
board routed free-grid witnesses carrying checked stacks, realization, and the
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_nat_sites_robinson_board_routed_stacks_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasRobinsonBoardRoutedFreeGridCheckedStacks
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
      (scaffoldDataOfNatSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
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
Encoded domino undecidability from a bundled concrete Figure 13/Figure 18
Nat-site Robinson routed scaffold certificate and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
    (C : NatSiteRobinsonScaffoldCertificate)
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
Nat-site Robinson routed scaffold certificate and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
    (C : NatSiteRobinsonScaffoldCertificate)
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
Nat-site Robinson routed scaffold certificate and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
    (C : NatSiteRobinsonScaffoldCertificate)
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
Nat-site Robinson routed scaffold certificate and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
    (C : NatSiteRobinsonScaffoldCertificate)
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
Encoded domino undecidability from the bundled Robinson certificate whose
backward scaffold construction is stated as active-indexed finite boxes.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_indexed_box_certificate_position_source
    (C : NatSiteRobinsonIndexedBoxScaffoldCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
    C.toScaffoldCertificate h

/--
Unencoded domino undecidability from the bundled Robinson certificate whose
backward scaffold construction is stated as active-indexed finite boxes.
-/
theorem
    domino_problem_undecidable_of_figure13_indexed_box_certificate_position_source
    (C : NatSiteRobinsonIndexedBoxScaffoldCertificate)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13_robinson_certificate_position_source
    C.toScaffoldCertificate h

/--
Encoded domino undecidability from an active-indexed-box Robinson certificate
and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_indexed_box_certificate_interiorRows
    (C : NatSiteRobinsonIndexedBoxScaffoldCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
    C.toScaffoldCertificate hinterior hcorrect

/--
Unencoded domino undecidability from an active-indexed-box Robinson certificate
and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_indexed_box_certificate_interiorRows
    (C : NatSiteRobinsonIndexedBoxScaffoldCertificate)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
    C.toScaffoldCertificate hinterior hcorrect

/--
Encoded domino undecidability from separated Robinson routed board/free-grid
geometry, finite checked layer-stack attachment, realization, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_robinson_free_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForRobinsonBoardRoutedFreeGrids
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hstacks realizes)
      h

/--
Unencoded domino undecidability from separated Robinson routed board/free-grid
geometry, finite checked layer-stack attachment, realization, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_robinson_free_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForRobinsonBoardRoutedFreeGrids
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hstacks realizes)
      h

/--
Encoded domino undecidability from separated Robinson routed board/free-grid
geometry, finite checked layer-stack attachment, realization, and the generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_robinson_free_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForRobinsonBoardRoutedFreeGrids
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hstacks realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from separated Robinson routed board/free-grid
geometry, finite checked layer-stack attachment, realization, and the generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_robinson_free_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForRobinsonBoardRoutedFreeGrids
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hstacks realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from Robinson routed board/free-grid geometry,
allowed local site rectangles, finite generated stack compatibility,
realization, and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_allowed_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofAllowedFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hallowed realizes)
      h

/--
Unencoded domino undecidability from Robinson routed board/free-grid geometry,
allowed local site rectangles, finite generated stack compatibility,
realization, and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_allowed_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofAllowedFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hallowed realizes)
      h

/--
Encoded domino undecidability from Robinson routed board/free-grid geometry,
allowed local site rectangles, finite generated stack compatibility,
realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_allowed_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofAllowedFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hallowed realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from Robinson routed board/free-grid geometry,
allowed local site rectangles, finite generated stack compatibility,
realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_allowed_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofAllowedFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hallowed realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from level-indexed Robinson routed board/free-grid
geometry, allowed local site rectangles on those level grids, finite generated
stack compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_allowed_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelAllowedFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hallowed realizes)
      h

/--
Unencoded domino undecidability from level-indexed Robinson routed board/free-grid
geometry, allowed local site rectangles on those level grids, finite generated
stack compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_level_allowed_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelAllowedFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hallowed realizes)
      h

/--
Encoded domino undecidability from level-indexed Robinson routed board/free-grid
geometry, allowed local site rectangles on those level grids, finite generated
stack compatibility, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_allowed_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelAllowedFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hallowed realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from level-indexed Robinson routed board/free-grid
geometry, allowed local site rectangles on those level grids, finite generated
stack compatibility, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_level_allowed_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelAllowedFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hallowed realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from level-indexed Robinson routed board/free-grid
geometry, local compatibility on those level grids, finite generated stack
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_local_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hcompatible realizes)
      h

/--
Unencoded domino undecidability from level-indexed Robinson routed board/free-grid
geometry, local compatibility on those level grids, finite generated stack
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_level_local_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hcompatible realizes)
      h

/--
Encoded domino undecidability from level-indexed Robinson routed board/free-grid
geometry, local compatibility on those level grids, finite generated stack
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_local_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from level-indexed Robinson routed board/free-grid
geometry, local compatibility on those level grids, finite generated stack
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_level_local_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from Robinson Section 7 obstruction-signal
certificates, local compatibility on the resulting level grids, finite
generated stack compatibility, realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_signal_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsignal hcheck hcompatible realizes)
      h

/--
Unencoded domino undecidability from Robinson Section 7 obstruction-signal
certificates, local compatibility on the resulting level grids, finite
generated stack compatibility, realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_level_signal_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsignal hcheck hcompatible realizes)
      h

/--
Encoded domino undecidability from Robinson Section 7 obstruction-signal
certificates, local compatibility on the resulting level grids, finite
generated stack compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_signal_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsignal hcheck hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from Robinson Section 7 obstruction-signal
certificates, local compatibility on the resulting level grids, finite
generated stack compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_level_signal_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsignal hcheck hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from Robinson Section 7 obstruction-signal
certificates with coordinate recurrence, local compatibility on the resulting
level grids, finite generated stack compatibility, realization, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_signal_step_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalCoordinateStepLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsteps hcheck hcompatible realizes)
      h

/--
Unencoded domino undecidability from Robinson Section 7 obstruction-signal
certificates with coordinate recurrence, local compatibility on the resulting
level grids, finite generated stack compatibility, realization, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_level_signal_step_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalCoordinateStepLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsteps hcheck hcompatible realizes)
      h

/--
Encoded domino undecidability from Robinson Section 7 obstruction-signal
certificates with coordinate recurrence, local compatibility on the resulting
level grids, finite generated stack compatibility, realization, and the
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_signal_step_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalCoordinateStepLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsteps hcheck hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from Robinson Section 7 obstruction-signal
certificates with coordinate recurrence, local compatibility on the resulting
level grids, finite generated stack compatibility, realization, and the
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_level_signal_step_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalCoordinateStepLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsteps hcheck hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from Robinson Section 7 obstruction-signal
certificates with local site compatibility and coordinate recurrence, finite
generated stack compatibility, realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_signal_local_step_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalCoordinateStepFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsteps hcheck realizes)
      h

/--
Unencoded domino undecidability from Robinson Section 7 obstruction-signal
certificates with local site compatibility and coordinate recurrence, finite
generated stack compatibility, realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_level_signal_local_step_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalCoordinateStepFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsteps hcheck realizes)
      h

/--
Encoded domino undecidability from Robinson Section 7 obstruction-signal
certificates with local site compatibility and coordinate recurrence, finite
generated stack compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_signal_local_step_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalCoordinateStepFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsteps hcheck realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from Robinson Section 7 obstruction-signal
certificates with local site compatibility and coordinate recurrence, finite
generated stack compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_level_signal_local_step_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalCoordinateStepFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hsteps hcheck realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from a coherent Robinson Section 7 local
obstruction-signal tower, finite generated stack compatibility, realization,
and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_signal_local_tower_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalTowerFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid htower hcheck realizes)
      h

/--
Unencoded domino undecidability from a coherent Robinson Section 7 local
obstruction-signal tower, finite generated stack compatibility, realization,
and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_level_signal_local_tower_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalTowerFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid htower hcheck realizes)
      h

/--
Encoded domino undecidability from a coherent Robinson Section 7 local
obstruction-signal tower, finite scaffold/payload layer patches, finite
generated stack compatibility, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_signal_local_tower_layer_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalTowerFreeGridsLayerPatches
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid htower hcheck patches)
      h

/--
Unencoded domino undecidability from a coherent Robinson Section 7 local
obstruction-signal tower, finite scaffold/payload layer patches, finite
generated stack compatibility, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_level_signal_local_tower_layer_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalTowerFreeGridsLayerPatches
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid htower hcheck patches)
      h

/--
Encoded domino undecidability from a coherent Robinson Section 7 local
obstruction-signal tower, finite active-corner indexed boxes, finite generated
stack compatibility, and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_tower_indexedBoxes_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalTowerFreeGridsIndexedBoxes
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid htower hcheck hboxes)
      h

/--
Unencoded domino undecidability from a coherent Robinson Section 7 local
obstruction-signal tower, finite active-corner indexed boxes, finite generated
stack compatibility, and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_level_tower_indexedBoxes_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalTowerFreeGridsIndexedBoxes
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid htower hcheck hboxes)
      h

/--
Encoded domino undecidability from a coherent Robinson Section 7 local
obstruction-signal tower, finite active-corner indexed boxes, finite generated
stack compatibility, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_tower_indexedBoxes_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalTowerFreeGridsIndexedBoxes
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid htower hcheck hboxes)
      hinterior hcorrect

/--
Unencoded domino undecidability from a coherent Robinson Section 7 local
obstruction-signal tower, finite active-corner indexed boxes, finite generated
stack compatibility, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_level_tower_indexedBoxes_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalTowerFreeGridsIndexedBoxes
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid htower hcheck hboxes)
      hinterior hcorrect

/--
Encoded domino undecidability from the bundled Robinson Section 7 scaffold
target: a coherent local obstruction-signal tower, finite active-corner indexed
boxes, and the generated finite compatibility check.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_towerBoxObligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      O.toScaffoldCertificate h

/--
Unencoded domino undecidability from the bundled Robinson Section 7 scaffold
target: a coherent local obstruction-signal tower, finite active-corner indexed
boxes, and the generated finite compatibility check.
-/
theorem
    domino_problem_undecidable_of_figure13_towerBoxObligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      O.toScaffoldCertificate h

/--
Encoded domino undecidability from the bundled Robinson Section 7 scaffold
target and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_towerBoxObligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      O.toScaffoldCertificate hinterior hcorrect

/--
Unencoded domino undecidability from the bundled Robinson Section 7 scaffold
target and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_towerBoxObligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      O.toScaffoldCertificate hinterior hcorrect

/--
Encoded domino undecidability from the bundled Robinson Section 7 scaffold
target, with the indexed-box part stated only for positive radii.  The
radius-zero box is supplied by the scaffold corner tile.
-/
theorem encoded_domino_problem_undecidable_of_figure13_tower_pos_boxes_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_towerBoxObligations_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofPositiveBoxes
        htower hcheck hboxes_pos)
      h

/--
Unencoded domino undecidability from the bundled Robinson Section 7 scaffold
target, with the indexed-box part stated only for positive radii.
-/
theorem domino_problem_undecidable_of_figure13_tower_pos_boxes_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_towerBoxObligations_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofPositiveBoxes
        htower hcheck hboxes_pos)
      h

/--
Encoded domino undecidability from the bundled Robinson Section 7 scaffold
target, positive-radius indexed boxes, and generated interior position-code
rows.
-/
theorem encoded_domino_problem_undecidable_of_figure13_tower_pos_boxes_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_towerBoxObligations_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofPositiveBoxes
        htower hcheck hboxes_pos)
      hinterior hcorrect

/--
Unencoded domino undecidability from the bundled Robinson Section 7 scaffold
target, positive-radius indexed boxes, and generated interior position-code
rows.
-/
theorem domino_problem_undecidable_of_figure13_tower_pos_boxes_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_towerBoxObligations_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofPositiveBoxes
        htower hcheck hboxes_pos)
      hinterior hcorrect

/--
Encoded domino undecidability from canonical Robinson-board routing, finite
generated stack compatibility, and positive-radius indexed boxes.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_canonical_routing_pos_boxes_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_towerBoxObligations_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofCanonicalRoutingPositiveBoxes
        hrouting hcheck hboxes_pos)
      h

/--
Unencoded domino undecidability from canonical Robinson-board routing, finite
generated stack compatibility, and positive-radius indexed boxes.
-/
theorem
    domino_problem_undecidable_of_figure13_canonical_routing_pos_boxes_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_towerBoxObligations_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofCanonicalRoutingPositiveBoxes
        hrouting hcheck hboxes_pos)
      h

/--
Encoded domino undecidability from canonical Robinson-board routing,
positive-radius indexed boxes, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_canonical_routing_pos_boxes_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_towerBoxObligations_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofCanonicalRoutingPositiveBoxes
        hrouting hcheck hboxes_pos)
      hinterior hcorrect

/--
Unencoded domino undecidability from canonical Robinson-board routing,
positive-radius indexed boxes, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_canonical_routing_pos_boxes_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_towerBoxObligations_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofCanonicalRoutingPositiveBoxes
        hrouting hcheck hboxes_pos)
      hinterior hcorrect

/--
Encoded domino undecidability from the field-based Robinson Section 7 local
signal tower, finite generated stack compatibility, and positive-radius
indexed boxes.
-/
theorem encoded_domino_problem_undecidable_of_figure13_signal_tower_pos_boxes_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_towerBoxObligations_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofSignalLocalTowerPositiveBoxes
        htower hcheck hboxes_pos)
      h

/--
Unencoded domino undecidability from the field-based Robinson Section 7 local
signal tower, finite generated stack compatibility, and positive-radius
indexed boxes.
-/
theorem domino_problem_undecidable_of_figure13_signal_tower_pos_boxes_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_towerBoxObligations_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofSignalLocalTowerPositiveBoxes
        htower hcheck hboxes_pos)
      h

/--
Encoded domino undecidability from the field-based Robinson Section 7 local
signal tower, positive-radius indexed boxes, and generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure13_signal_tower_pos_boxes_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_towerBoxObligations_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofSignalLocalTowerPositiveBoxes
        htower hcheck hboxes_pos)
      hinterior hcorrect

/--
Unencoded domino undecidability from the field-based Robinson Section 7 local
signal tower, positive-radius indexed boxes, and generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_figure13_signal_tower_pos_boxes_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_towerBoxObligations_interiorRows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid
      (NatSiteRobinsonTowerIndexedBoxObligations.ofSignalLocalTowerPositiveBoxes
        htower hcheck hboxes_pos)
      hinterior hcorrect

/--
Encoded domino undecidability from a coherent Robinson Section 7 local
obstruction-signal tower, finite generated stack compatibility, realization,
and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_signal_local_tower_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalTowerFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid htower hcheck realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from a coherent Robinson Section 7 local
obstruction-signal tower, finite generated stack compatibility, realization,
and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_level_signal_local_tower_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelSignalLocalTowerFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid htower hcheck realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from Robinson level board/free-grid geometry with
local Figure 18 site compatibility bundled into the generated level grids,
finite generated stack compatibility, realization, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_compatible_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck realizes)
      h

/--
Unencoded domino undecidability from Robinson level board/free-grid geometry
with local Figure 18 site compatibility bundled into the generated level grids,
finite generated stack compatibility, realization, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_level_compatible_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck realizes)
      h

/--
Encoded domino undecidability from Robinson level board/free-grid geometry with
local Figure 18 site compatibility bundled into the generated level grids,
finite generated stack compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_level_compatible_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from Robinson level board/free-grid geometry
with local Figure 18 site compatibility bundled into the generated level grids,
finite generated stack compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_level_compatible_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the bundled compatible level-grid scaffold
obligation and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
        activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofCompatibleLevelObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      h

/--
Unencoded domino undecidability from the bundled compatible level-grid scaffold
obligation and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
        activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofCompatibleLevelObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      h

/--
Encoded domino undecidability from the bundled compatible level-grid scaffold
obligation and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
        activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofCompatibleLevelObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      hinterior hcorrect

/--
Unencoded domino undecidability from the bundled compatible level-grid scaffold
obligation and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_compatible_level_obligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
        activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofCompatibleLevelObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      hinterior hcorrect

/--
Encoded domino undecidability from Robinson routed board/free-grid geometry,
local compatibility of the selected Figure 18 sites, finite generated stack
compatibility, realization, and generated position-coded source-route
obligations.

For generated flat role tables, active-site membership of each selected crossing
is already part of `Figure18RobinsonBoardRoutedFreeGrid.active`; the Robinson
Section 7 obstruction-signal argument only has to prove the local horizontal and
vertical compatibility recorded by `HasLocallyCompatibleRobinsonBoardRoutedFreeGrids`.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_locally_compatible_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hcompatible realizes)
      h

/--
Unencoded domino undecidability from Robinson routed board/free-grid geometry,
local compatibility of the selected Figure 18 sites, finite generated stack
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_locally_compatible_robinson_grids_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hcompatible realizes)
      h

/--
Encoded domino undecidability from Robinson routed board/free-grid geometry,
local compatibility of the selected Figure 18 sites, finite generated stack
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_locally_compatible_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from Robinson routed board/free-grid geometry,
local compatibility of the selected Figure 18 sites, finite generated stack
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_locally_compatible_robinson_grids_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLocallyCompatibleFreeGrids
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hgrids hcheck hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from bundled Robinson Section 7 obligations and
generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_robinson_obligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      h

/--
Unencoded domino undecidability from bundled Robinson Section 7 obligations and
generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_robinson_obligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      h

/--
Encoded domino undecidability from bundled Robinson Section 7 obligations and
the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_robinson_obligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonObligations activeSiteSpecs activeSiteSpecs_valid
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      hinterior hcorrect

/--
Unencoded domino undecidability from bundled Robinson Section 7 obligations and
the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_robinson_obligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonObligations activeSiteSpecs activeSiteSpecs_valid
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      hinterior hcorrect

/--
Encoded domino undecidability from bundled level-indexed Robinson Section 7
obligations and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_robinson_level_obligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonLevelObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      h

/--
Unencoded domino undecidability from bundled level-indexed Robinson Section 7
obligations and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_robinson_level_obligations_position_source
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonLevelObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofLevelObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      h

/--
Encoded domino undecidability from bundled level-indexed Robinson Section 7
obligations and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_robinson_level_obligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonLevelObligations activeSiteSpecs activeSiteSpecs_valid
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
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      hinterior hcorrect

/--
Unencoded domino undecidability from bundled level-indexed Robinson Section 7
obligations and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_robinson_level_obligations_interiorRows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonLevelObligations activeSiteSpecs activeSiteSpecs_valid
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
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofLevelObligations
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid obligations)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson routed-grid/local-compatibility geometry, realization, and
generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component1_blank_robinson_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidate
        hgrids hcompatible realizes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson routed-grid/local-compatibility geometry, realization, and
generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component1_blank_robinson_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidate
        hgrids hcompatible realizes)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson routed-grid/local-compatibility geometry, realization, and
the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component1_blank_robinson_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidate
        hgrids hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson routed-grid/local-compatibility geometry, realization, and
the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component1_blank_robinson_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidate
        hgrids hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson routed-grid/local-compatibility geometry, realization, and
generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component2_blank_robinson_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidate
        hgrids hcompatible realizes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson routed-grid/local-compatibility geometry, realization, and
generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component2_blank_robinson_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidate
        hgrids hcompatible realizes)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson routed-grid/local-compatibility geometry, realization, and
the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component2_blank_robinson_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidate
        hgrids hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson routed-grid/local-compatibility geometry, realization, and
the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component2_blank_robinson_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidate
        hgrids hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local allowed
site rectangles, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component1_blank_level_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component1BlankCandidateActiveSiteData
        l2Component1BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevel
        hgrids hallowed realizes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local allowed
site rectangles, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component1_blank_level_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component1BlankCandidateActiveSiteData
        l2Component1BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevel
        hgrids hallowed realizes)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local allowed
site rectangles, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component1_blank_level_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component1BlankCandidateActiveSiteData
        l2Component1BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevel
        hgrids hallowed realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local allowed
site rectangles, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component1_blank_level_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component1BlankCandidateActiveSiteData
        l2Component1BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevel
        hgrids hallowed realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local allowed
site rectangles, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component2_blank_level_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component2BlankCandidateActiveSiteData
        l2Component2BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevel
        hgrids hallowed realizes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local allowed
site rectangles, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component2_blank_level_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component2BlankCandidateActiveSiteData
        l2Component2BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevel
        hgrids hallowed realizes)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local allowed
site rectangles, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component2_blank_level_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component2BlankCandidateActiveSiteData
        l2Component2BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevel
        hgrids hallowed realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local allowed
site rectangles, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component2_blank_level_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component2BlankCandidateActiveSiteData
        l2Component2BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevel
        hgrids hallowed realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component1_blank_level_local_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelLocal
        hgrids hcompatible realizes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component1_blank_level_local_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelLocal
        hgrids hcompatible realizes)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component1_blank_level_local_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelLocal
        hgrids hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component1_blank_level_local_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelLocal
        hgrids hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component2_blank_level_local_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelLocal
        hgrids hcompatible realizes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component2_blank_level_local_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelLocal
        hgrids hcompatible realizes)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component2_blank_level_local_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelLocal
        hgrids hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, level-indexed Robinson routed-grid geometry, level-local
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component2_blank_level_local_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelLocal
        hgrids hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates, level-local
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component1_blank_level_signal_position_source
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelSignalLocal
        hsignal hcompatible realizes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates, level-local
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component1_blank_level_signal_position_source
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelSignalLocal
        hsignal hcompatible realizes)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates, level-local
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component2_blank_level_signal_position_source
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelSignalLocal
        hsignal hcompatible realizes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates, level-local
compatibility, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component2_blank_level_signal_position_source
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelSignalLocal
        hsignal hcompatible realizes)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates, level-local
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component1_blank_level_signal_interiorRows
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelSignalLocal
        hsignal hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates, level-local
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component1_blank_level_signal_interiorRows
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelSignalLocal
        hsignal hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates, level-local
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2_component2_blank_level_signal_interiorRows
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelSignalLocal
        hsignal hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates, level-local
compatibility, realization, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2_component2_blank_level_signal_interiorRows
    (hsignal :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCertificatesForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelSignalLocal
        hsignal hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates with coordinate
recurrence, level-local compatibility, realization, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_level_signal_step_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelSignalCoordinateStepLocal
        hsteps hcompatible realizes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates with coordinate
recurrence, level-local compatibility, realization, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_level_signal_step_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelSignalCoordinateStepLocal
        hsteps hcompatible realizes)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates with coordinate
recurrence, level-local compatibility, realization, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_level_signal_step_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelSignalCoordinateStepLocal
        hsteps hcompatible realizes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates with coordinate
recurrence, level-local compatibility, realization, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_level_signal_step_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelSignalCoordinateStepLocal
        hsteps hcompatible realizes)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates with coordinate
recurrence, level-local compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_level_signal_step_interiorRows
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelSignalCoordinateStepLocal
        hsteps hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates with coordinate
recurrence, level-local compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_level_signal_step_interiorRows
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component1BlankCandidateLevelSignalCoordinateStepLocal
        hsteps hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates with coordinate
recurrence, level-local compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_level_signal_step_interiorRows
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelSignalCoordinateStepLocal
        hsteps hcompatible realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 obstruction-signal certificates with coordinate
recurrence, level-local compatibility, realization, and the generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_level_signal_step_interiorRows
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2Component2BlankCandidateLevelSignalCoordinateStepLocal
        hsteps hcompatible realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_signal_local_step_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalStepFreeGrids
        hsteps realizes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_signal_local_step_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalStepFreeGrids
        hsteps realizes)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, realization, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_signal_local_step_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalStepFreeGrids
        hsteps realizes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, realization, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_signal_local_step_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalStepFreeGrids
        hsteps realizes)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
realization, and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_signal_local_tower_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalTowerFreeGrids
        htower realizes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
realization, and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_signal_local_tower_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalTowerFreeGrids
        htower realizes)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
realization, and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_signal_local_tower_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalTowerFreeGrids
        htower realizes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
realization, and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_signal_local_tower_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalTowerFreeGrids
        htower realizes)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_signal_local_tower_layer_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalTowerFreeGridsLayerPatches
        htower patches)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_signal_local_tower_layer_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalTowerFreeGridsLayerPatches
        htower patches)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_signal_local_tower_layer_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalTowerFreeGridsLayerPatches
        htower patches)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_signal_local_tower_layer_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalTowerFreeGridsLayerPatches
        htower patches)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, a fixed Robinson Section 7 obstruction-geometry tower with routing,
finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_fixed_geometry_routing_layer_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1FixedGeometryTowerRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, a fixed Robinson Section 7 obstruction-geometry tower with routing,
finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_fixed_geometry_routing_layer_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1FixedGeometryTowerRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, a fixed Robinson Section 7 obstruction-geometry tower with routing,
finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_fixed_geometry_routing_layer_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2FixedGeometryTowerRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, a fixed Robinson Section 7 obstruction-geometry tower with routing,
finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_fixed_geometry_routing_layer_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2FixedGeometryTowerRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_fixed_geometry_product_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1FixedGeometryProductRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_fixed_geometry_product_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1FixedGeometryProductRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_fixed_geometry_product_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2FixedGeometryProductRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, finite scaffold/payload layer patches, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_fixed_geometry_product_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2FixedGeometryProductRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, finite scaffold/payload layer patches, and
generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_product_layer_patches_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1CanonicalProductRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, finite scaffold/payload layer patches, and
generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_product_layer_patches_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1CanonicalProductRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, finite scaffold/payload layer patches, and
generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_product_layer_patches_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2CanonicalProductRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, finite scaffold/payload layer patches, and
generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_product_layer_patches_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2CanonicalProductRoutingFreeGridsLayerPatches
        hrouting patches)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, finite scaffold/payload layer patches, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_product_layer_patches_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_product_layer_patches_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, finite scaffold/payload layer patches, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_product_layer_patches_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_product_layer_patches_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, finite scaffold/payload layer patches, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_product_layer_patches_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_product_layer_patches_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, finite scaffold/payload layer patches, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_product_layer_patches_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_product_layer_patches_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, positive-radius indexed boxes, and generated
position-coded source-route obligations.  The radius-zero box is supplied by
the scaffold corner tile.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_product_pos_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1CanonicalProductRoutingFreeGridsPositiveBoxes
        hrouting hboxes_pos)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, positive-radius indexed boxes, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_product_pos_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1CanonicalProductRoutingFreeGridsPositiveBoxes
        hrouting hboxes_pos)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, positive-radius indexed boxes, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_product_pos_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2CanonicalProductRoutingFreeGridsPositiveBoxes
        hrouting hboxes_pos)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, positive-radius indexed boxes, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_product_pos_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2CanonicalProductRoutingFreeGridsPositiveBoxes
        hrouting hboxes_pos)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, positive-radius indexed boxes, and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_product_pos_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_product_pos_boxes_position_source
      hrouting hboxes_pos
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, positive-radius indexed boxes, and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_product_pos_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_product_pos_boxes_position_source
      hrouting hboxes_pos
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, positive-radius indexed boxes, and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_product_pos_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_product_pos_boxes_position_source
      hrouting hboxes_pos
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, positive-radius indexed boxes, and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_product_pos_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_product_pos_boxes_position_source
      hrouting hboxes_pos
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, routing over the canonical Robinson Section 7 obstruction-geometry
tower, positive-radius indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_routing_pos_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1CanonicalRoutingFreeGridsPositiveBoxes
        hrouting hboxes_pos)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, routing over the canonical Robinson Section 7 obstruction-geometry
tower, positive-radius indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_routing_pos_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1CanonicalRoutingFreeGridsPositiveBoxes
        hrouting hboxes_pos)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, routing over the canonical Robinson Section 7 obstruction-geometry
tower, positive-radius indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_routing_pos_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2CanonicalRoutingFreeGridsPositiveBoxes
        hrouting hboxes_pos)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, routing over the canonical Robinson Section 7 obstruction-geometry
tower, positive-radius indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_routing_pos_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2CanonicalRoutingFreeGridsPositiveBoxes
        hrouting hboxes_pos)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, routing over the canonical Robinson Section 7 obstruction-geometry
tower, positive-radius indexed boxes, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_routing_pos_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_routing_pos_boxes_position_source
      hrouting hboxes_pos
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, routing over the canonical Robinson Section 7 obstruction-geometry
tower, positive-radius indexed boxes, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_routing_pos_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_routing_pos_boxes_position_source
      hrouting hboxes_pos
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, routing over the canonical Robinson Section 7 obstruction-geometry
tower, positive-radius indexed boxes, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_routing_pos_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_routing_pos_boxes_position_source
      hrouting hboxes_pos
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, routing over the canonical Robinson Section 7 obstruction-geometry
tower, positive-radius indexed boxes, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_routing_pos_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_routing_pos_boxes_position_source
      hrouting hboxes_pos
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, active-corner indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_product_indexedBoxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1FixedGeometryProductRoutingFreeGridsIndexedBoxes
        hrouting hboxes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, active-corner indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_product_indexedBoxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1FixedGeometryProductRoutingFreeGridsIndexedBoxes
        hrouting hboxes)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, active-corner indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_product_indexedBoxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2FixedGeometryProductRoutingFreeGridsIndexedBoxes
        hrouting hboxes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, active-corner indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_product_indexedBoxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2FixedGeometryProductRoutingFreeGridsIndexedBoxes
        hrouting hboxes)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, active-corner indexed boxes, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_product_indexedBoxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C1FixedGeometryProductRoutingFreeGridsIndexedBoxes
        hrouting hboxes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, active-corner indexed boxes, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_product_indexedBoxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C1FixedGeometryProductRoutingFreeGridsIndexedBoxes
        hrouting hboxes)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, active-corner indexed boxes, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_product_indexedBoxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C2FixedGeometryProductRoutingFreeGridsIndexedBoxes
        hrouting hboxes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness fixed Robinson Section 7 obstruction-geometry
routing, active-corner indexed boxes, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_product_indexedBoxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C2FixedGeometryProductRoutingFreeGridsIndexedBoxes
        hrouting hboxes)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, active-corner indexed boxes, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_product_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13_l2c1_product_indexedBoxes_position_source
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      hrouting)
    hboxes h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, active-corner indexed boxes, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_product_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13_l2c1_product_indexedBoxes_position_source
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      hrouting)
    hboxes h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, active-corner indexed boxes, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_product_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13_l2c2_product_indexedBoxes_position_source
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      hrouting)
    hboxes h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, active-corner indexed boxes, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_product_boxes_position_source
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13_l2c2_product_indexedBoxes_position_source
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      hrouting)
    hboxes h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, active-corner indexed boxes, and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_product_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13_l2c1_product_indexedBoxes_interiorRows
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      hrouting)
    hboxes hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, active-corner indexed boxes, and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_product_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13_l2c1_product_indexedBoxes_interiorRows
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      hrouting)
    hboxes hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, active-corner indexed boxes, and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_product_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13_l2c2_product_indexedBoxes_interiorRows
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      hrouting)
    hboxes hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, product-witness routing over the canonical Robinson Section 7
obstruction-geometry tower, active-corner indexed boxes, and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_product_boxes_interiorRows
    (hrouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13_l2c2_product_indexedBoxes_interiorRows
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      hrouting)
    hboxes hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite active-corner indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_tower_indexedBoxes_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalTowerFreeGridsIndexedBoxes
        htower hboxes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite active-corner indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_tower_indexedBoxes_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalTowerFreeGridsIndexedBoxes
        htower hboxes)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite active-corner indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_tower_indexedBoxes_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalTowerFreeGridsIndexedBoxes
        htower hboxes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite active-corner indexed boxes, and generated position-coded source-route
obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_tower_indexedBoxes_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalTowerFreeGridsIndexedBoxes
        htower hboxes)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite active-corner indexed boxes, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_tower_indexedBoxes_interiorRows
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalTowerFreeGridsIndexedBoxes
        htower hboxes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite active-corner indexed boxes, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_tower_indexedBoxes_interiorRows
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalTowerFreeGridsIndexedBoxes
        htower hboxes)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite active-corner indexed boxes, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_tower_indexedBoxes_interiorRows
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalTowerFreeGridsIndexedBoxes
        htower hboxes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, a coherent Robinson Section 7 local obstruction-signal tower,
finite active-corner indexed boxes, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_tower_indexedBoxes_interiorRows
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalTowerFreeGridsIndexedBoxes
        htower hboxes)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via the
bundled Robinson Section 7 tower/indexed-box obligation.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      O.toScaffoldCertificate h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the bundled Robinson Section 7 tower/indexed-box obligation.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      O.toScaffoldCertificate h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the bundled Robinson Section 7 tower/indexed-box obligation.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      O.toScaffoldCertificate h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the bundled Robinson Section 7 tower/indexed-box obligation.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_position_source
      O.toScaffoldCertificate h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
the bundled Robinson Section 7 tower/indexed-box obligation and the generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      O.toScaffoldCertificate hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the bundled Robinson Section 7 tower/indexed-box obligation and the generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      O.toScaffoldCertificate hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the bundled Robinson Section 7 tower/indexed-box obligation and the generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      O.toScaffoldCertificate hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the bundled Robinson Section 7 tower/indexed-box obligation and the generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      O.toScaffoldCertificate hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via the
bundled canonical-routing positive-box scaffold obligation.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_obligations_position_source
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
      O.toL2C1TowerIndexedBoxObligations h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the bundled canonical-routing positive-box scaffold obligation.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_obligations_position_source
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
      O.toL2C1TowerIndexedBoxObligations h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the bundled canonical-routing positive-box scaffold obligation.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_obligations_position_source
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
      O.toL2C2TowerIndexedBoxObligations h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the bundled canonical-routing positive-box scaffold obligation.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_obligations_position_source
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
      O.toL2C2TowerIndexedBoxObligations h

/--
Encoded domino undecidability from the first audited L2-blank candidate via the
bundled canonical-routing positive-box scaffold obligation and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_obligations_interiorRows
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
      O.toL2C1TowerIndexedBoxObligations hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the bundled canonical-routing positive-box scaffold obligation and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_obligations_interiorRows
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
      O.toL2C1TowerIndexedBoxObligations hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the bundled canonical-routing positive-box scaffold obligation and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_obligations_interiorRows
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
      O.toL2C2TowerIndexedBoxObligations hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the bundled canonical-routing positive-box scaffold obligation and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_obligations_interiorRows
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
      O.toL2C2TowerIndexedBoxObligations hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via the
bundled canonical scaffold obligation and generated one-row position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_obligations_oneRows
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hrows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_obligations_position_source
      O (positionSourceObligationsOfPositionCodeOneRows hrows hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the bundled canonical scaffold obligation and generated one-row position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_obligations_oneRows
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hrows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_obligations_position_source
      O (positionSourceObligationsOfPositionCodeOneRows hrows hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the bundled canonical scaffold obligation and generated one-row position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_obligations_oneRows
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hrows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_obligations_position_source
      O (positionSourceObligationsOfPositionCodeOneRows hrows hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the bundled canonical scaffold obligation and generated one-row position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_obligations_oneRows
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hrows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_obligations_position_source
      O (positionSourceObligationsOfPositionCodeOneRows hrows hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via the
bundled canonical scaffold obligation and generated position-code accumulator
step.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_obligations_position_source
      O (positionSourceObligationsOfPositionCodeDecoderStep hstep hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the bundled canonical scaffold obligation and generated position-code
accumulator step.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_obligations_position_source
      O (positionSourceObligationsOfPositionCodeDecoderStep hstep hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via the
bundled canonical scaffold obligation and generated position-code accumulator
step.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_obligations_position_source
      O (positionSourceObligationsOfPositionCodeDecoderStep hstep hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the bundled canonical scaffold obligation and generated position-code
accumulator step.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_obligations_position_source
      O (positionSourceObligationsOfPositionCodeDecoderStep hstep hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical routing and translated positive-radius indexed boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
        O.canonicalRouting O.positiveTranslatedIndexedBoxes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical routing and translated positive-radius indexed boxes.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
        O.canonicalRouting O.positiveTranslatedIndexedBoxes)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical routing and translated positive-radius indexed boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
        O.canonicalRouting O.positiveTranslatedIndexedBoxes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical routing and translated positive-radius indexed boxes.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
        O.canonicalRouting O.positiveTranslatedIndexedBoxes)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical decoded combined-site corridor routing and translated
positive-radius indexed boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_combined_site_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_translated_obligations_position_source
      O.toCanonicalTranslatedPositiveBoxObligations h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical decoded combined-site corridor routing and translated
positive-radius indexed boxes.
-/
theorem
    domino_problem_undecidable_l2c1_combined_site_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_translated_obligations_position_source
      O.toCanonicalTranslatedPositiveBoxObligations h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical decoded combined-site corridor routing and translated
positive-radius indexed boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_combined_site_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_translated_obligations_position_source
      O.toCanonicalTranslatedPositiveBoxObligations h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical decoded combined-site corridor routing and translated
positive-radius indexed boxes.
-/
theorem
    domino_problem_undecidable_l2c2_combined_site_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_translated_obligations_position_source
      O.toCanonicalTranslatedPositiveBoxObligations h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical named-site-rectangle routing and translated positive-radius indexed
boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_site_rect_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_combined_site_translated_obligations_position_source
      O.toCanonicalCombinedSiteTranslatedPositiveBoxObligations h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical named-site-rectangle routing and translated positive-radius indexed
boxes.
-/
theorem
    domino_problem_undecidable_l2c1_site_rect_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_combined_site_translated_obligations_position_source
      O.toCanonicalCombinedSiteTranslatedPositiveBoxObligations h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical named-site-rectangle routing and translated positive-radius indexed
boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_site_rect_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_combined_site_translated_obligations_position_source
      O.toCanonicalCombinedSiteTranslatedPositiveBoxObligations h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical named-site-rectangle routing and translated positive-radius indexed
boxes.
-/
theorem
    domino_problem_undecidable_l2c2_site_rect_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_combined_site_translated_obligations_position_source
      O.toCanonicalCombinedSiteTranslatedPositiveBoxObligations h

open NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson-board routing and a raw Figure 13 plane tiling.
-/
theorem encoded_domino_problem_undecidable_l2c1_canonical_fig13_tiles_plane_position_source
    (canonicalRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_translated_obligations_position_source
      (ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
        canonicalRouting hplane)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson-board routing and a raw Figure 13 plane tiling.
-/
theorem domino_problem_undecidable_l2c1_canonical_fig13_tiles_plane_position_source
    (canonicalRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_translated_obligations_position_source
      (ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
        canonicalRouting hplane)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson-board routing and a raw Figure 13 plane tiling.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_fig13_tiles_plane_position_source
    (canonicalRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_translated_obligations_position_source
      (ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
        canonicalRouting hplane)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson-board routing and a raw Figure 13 plane tiling.
-/
theorem domino_problem_undecidable_l2c2_canonical_fig13_tiles_plane_position_source
    (canonicalRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_translated_obligations_position_source
      (ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
        canonicalRouting hplane)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
product-witness canonical Robinson-board routing and a raw Figure 13 plane
tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_product_fig13_tiles_plane_position_source
    (canonicalProductRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfCanonicalProductRoutingPositiveFig13TilesPlane
        canonicalProductRouting hplane)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
product-witness canonical Robinson-board routing and a raw Figure 13 plane
tiling.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_product_fig13_tiles_plane_position_source
    (canonicalProductRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfCanonicalProductRoutingPositiveFig13TilesPlane
        canonicalProductRouting hplane)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
product-witness canonical Robinson-board routing and a raw Figure 13 plane
tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_product_fig13_tiles_plane_position_source
    (canonicalProductRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfCanonicalProductRoutingPositiveFig13TilesPlane
        canonicalProductRouting hplane)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
product-witness canonical Robinson-board routing and a raw Figure 13 plane
tiling.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_product_fig13_tiles_plane_position_source
    (canonicalProductRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfCanonicalProductRoutingPositiveFig13TilesPlane
        canonicalProductRouting hplane)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson-board corridor transmission and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_corridor_fig13_tiles_plane_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfCanonicalCorridorRoutingPositiveFig13TilesPlane
        canonicalCorridorRouting hplane)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson-board corridor transmission and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_corridor_fig13_tiles_plane_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfCanonicalCorridorRoutingPositiveFig13TilesPlane
        canonicalCorridorRouting hplane)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson-board corridor transmission and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_corridor_fig13_tiles_plane_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfCanonicalCorridorRoutingPositiveFig13TilesPlane
        canonicalCorridorRouting hplane)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson-board corridor transmission and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_corridor_fig13_tiles_plane_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfCanonicalCorridorRoutingPositiveFig13TilesPlane
        canonicalCorridorRouting hplane)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical decoded combined-site corridor routing and a raw Figure 13 plane
tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_combined_site_fig13_tiles_plane_position_source
    (canonicalCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfCanonicalCombinedSiteRoutingPositiveFig13TilesPlane
        canonicalCombinedSiteRouting hplane)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical decoded combined-site corridor routing and a raw Figure 13 plane
tiling.
-/
theorem
    domino_problem_undecidable_l2c1_combined_site_fig13_tiles_plane_position_source
    (canonicalCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfCanonicalCombinedSiteRoutingPositiveFig13TilesPlane
        canonicalCombinedSiteRouting hplane)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical decoded combined-site corridor routing and a raw Figure 13 plane
tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_combined_site_fig13_tiles_plane_position_source
    (canonicalCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfCanonicalCombinedSiteRoutingPositiveFig13TilesPlane
        canonicalCombinedSiteRouting hplane)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical decoded combined-site corridor routing and a raw Figure 13 plane
tiling.
-/
theorem
    domino_problem_undecidable_l2c2_combined_site_fig13_tiles_plane_position_source
    (canonicalCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfCanonicalCombinedSiteRoutingPositiveFig13TilesPlane
        canonicalCombinedSiteRouting hplane)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
tiling-dependent Robinson board geometry, decoded combined-site corridor
routing, and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_geom_combined_fig13_position_source
    (geometryCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfGeomCombinedPositiveFig13TilesPlane
        geometryCombinedSiteRouting hplane)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
tiling-dependent Robinson board geometry, decoded combined-site corridor
routing, and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c1_geom_combined_fig13_position_source
    (geometryCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfGeomCombinedPositiveFig13TilesPlane
        geometryCombinedSiteRouting hplane)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
tiling-dependent Robinson board geometry, decoded combined-site corridor
routing, and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_geom_combined_fig13_position_source
    (geometryCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfGeomCombinedPositiveFig13TilesPlane
        geometryCombinedSiteRouting hplane)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
tiling-dependent Robinson board geometry, decoded combined-site corridor
routing, and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c2_geom_combined_fig13_position_source
    (geometryCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfGeomCombinedPositiveFig13TilesPlane
        geometryCombinedSiteRouting hplane)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
the bundled tiling-dependent Robinson geometry and translated active-box
scaffold obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_geom_combined_obligations_position_source
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the bundled tiling-dependent Robinson geometry and translated active-box
scaffold obligations.
-/
theorem
    domino_problem_undecidable_l2c1_geom_combined_obligations_position_source
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the bundled tiling-dependent Robinson geometry and translated active-box
scaffold obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_geom_combined_obligations_position_source
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the bundled tiling-dependent Robinson geometry and translated active-box
scaffold obligations.
-/
theorem
    domino_problem_undecidable_l2c2_geom_combined_obligations_position_source
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate
      h

open NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations in
def l2c1GeomCombinedFig13Obligations
    (geomCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    geomCombinedSiteRouting hplane

open NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations in
def l2c2GeomCombinedFig13Obligations
    (geomCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    geomCombinedSiteRouting hplane

/--
Encoded domino undecidability from the first audited L2-blank candidate via
tiling-dependent Robinson board geometry, decoded combined-site corridor
routing, a raw Figure 13 plane tiling, and the generated position-code
accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_geom_combined_fig13_decoderStep
    (geometryCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_decoderStep
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfGeomCombinedPositiveFig13TilesPlane
        geometryCombinedSiteRouting hplane)
      hstep hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
tiling-dependent Robinson board geometry, decoded combined-site corridor
routing, a raw Figure 13 plane tiling, and the generated position-code
accumulator step.
-/
theorem
    domino_problem_undecidable_l2c1_geom_combined_fig13_decoderStep
    (geometryCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_decoderStep
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfGeomCombinedPositiveFig13TilesPlane
        geometryCombinedSiteRouting hplane)
      hstep hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
tiling-dependent Robinson board geometry, decoded combined-site corridor
routing, a raw Figure 13 plane tiling, and the generated position-code
accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_geom_combined_fig13_decoderStep
    (geometryCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_decoderStep
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfGeomCombinedPositiveFig13TilesPlane
        geometryCombinedSiteRouting hplane)
      hstep hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
tiling-dependent Robinson board geometry, decoded combined-site corridor
routing, a raw Figure 13 plane tiling, and the generated position-code
accumulator step.
-/
theorem
    domino_problem_undecidable_l2c2_geom_combined_fig13_decoderStep
    (geometryCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_decoderStep
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfGeomCombinedPositiveFig13TilesPlane
        geometryCombinedSiteRouting hplane)
      hstep hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
the bundled tiling-dependent Robinson geometry and translated active-box
scaffold obligations, plus the generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_geom_combined_obligations_decoderStep
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_decoderStep
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate
      hstep hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the bundled tiling-dependent Robinson geometry and translated active-box
scaffold obligations, plus the generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c1_geom_combined_obligations_decoderStep
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_decoderStep
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate
      hstep hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the bundled tiling-dependent Robinson geometry and translated active-box
scaffold obligations, plus the generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_geom_combined_obligations_decoderStep
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_decoderStep
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate
      hstep hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the bundled tiling-dependent Robinson geometry and translated active-box
scaffold obligations, plus the generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c2_geom_combined_obligations_decoderStep
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_decoderStep
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate
      hstep hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical routing, translated positive-radius indexed boxes, and the generated
position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_obligations_decoderStep
      O.toCanonicalPositiveBoxObligations hstep hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical routing, translated positive-radius indexed boxes, and the generated
position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_obligations_decoderStep
      O.toCanonicalPositiveBoxObligations hstep hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical routing, translated positive-radius indexed boxes, and the generated
position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_obligations_decoderStep
      O.toCanonicalPositiveBoxObligations hstep hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical routing, translated positive-radius indexed boxes, and the generated
position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_obligations_decoderStep
      O.toCanonicalPositiveBoxObligations hstep hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical decoded combined-site corridor routing, translated positive-radius
indexed boxes, and the generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_combined_site_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_translated_obligations_decoderStep
      O.toCanonicalTranslatedPositiveBoxObligations hstep hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical decoded combined-site corridor routing, translated positive-radius
indexed boxes, and the generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c1_combined_site_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_translated_obligations_decoderStep
      O.toCanonicalTranslatedPositiveBoxObligations hstep hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical decoded combined-site corridor routing, translated positive-radius
indexed boxes, and the generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_combined_site_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_translated_obligations_decoderStep
      O.toCanonicalTranslatedPositiveBoxObligations hstep hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical decoded combined-site corridor routing, translated positive-radius
indexed boxes, and the generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c2_combined_site_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_translated_obligations_decoderStep
      O.toCanonicalTranslatedPositiveBoxObligations hstep hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical named-site-rectangle routing, translated positive-radius indexed
boxes, and the generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_site_rect_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_combined_site_translated_obligations_decoderStep
      O.toCanonicalCombinedSiteTranslatedPositiveBoxObligations hstep hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical named-site-rectangle routing, translated positive-radius indexed
boxes, and the generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c1_site_rect_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_combined_site_translated_obligations_decoderStep
      O.toCanonicalCombinedSiteTranslatedPositiveBoxObligations hstep hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical named-site-rectangle routing, translated positive-radius indexed
boxes, and the generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_site_rect_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_combined_site_translated_obligations_decoderStep
      O.toCanonicalCombinedSiteTranslatedPositiveBoxObligations hstep hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical named-site-rectangle routing, translated positive-radius indexed
boxes, and the generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c2_site_rect_translated_obligations_decoderStep
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_combined_site_translated_obligations_decoderStep
      O.toCanonicalCombinedSiteTranslatedPositiveBoxObligations hstep hcorrect

open NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations in
def l2c1Fig13Obligations
    (canonicalCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    canonicalCombinedSiteRouting hplane

open NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations in
def l2c2Fig13Obligations
    (canonicalCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    canonicalCombinedSiteRouting hplane

open NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations in
def l2c1SiteRectFig13Obligations
    (canonicalSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane canonicalSiteRectRouting
    hplane

open NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations in
def l2c2SiteRectFig13Obligations
    (canonicalSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane canonicalSiteRectRouting
    hplane

open NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations in
def l2c1FreeSiteRectFig13Obligations
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlaneFreeSiteRect
    canonicalFreeSiteRectRouting hplane

open NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations in
def l2c2FreeSiteRectFig13Obligations
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlaneFreeSiteRect
    canonicalFreeSiteRectRouting hplane

open NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations in
def l2c1FreeSiteRectFig13BundledObligations
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    canonicalFreeSiteRectRouting hplane

open NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations in
def l2c2FreeSiteRectFig13BundledObligations
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    canonicalFreeSiteRectRouting hplane

open NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations in
def l2c1OriginZeroFig13BundledObligations
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    originZeroWindows hplane

open NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations in
def l2c2OriginZeroFig13BundledObligations
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    originZeroWindows hplane

/--
The Figure 18 role table whose indexed-active windows are needed for the first
audited L2-blank candidate.
-/
def l2Component1IndexedActiveRoleTable : OllingerRobinson.Figure18RoleTable :=
  (OllingerRobinson.Figure18RoleTable.FlatRoleTable.ofActiveSites
    (activeSiteDataOfSpecs l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid).sites
    (cornerSiteOfNat 0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)).toRoleTable

/--
The Figure 18 role table whose indexed-active windows are needed for the second
audited L2-blank candidate.
-/
def l2Component2IndexedActiveRoleTable : OllingerRobinson.Figure18RoleTable :=
  (OllingerRobinson.Figure18RoleTable.FlatRoleTable.ofActiveSites
    (activeSiteDataOfSpecs l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid).sites
    (cornerSiteOfNat 0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)).toRoleTable

open NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations in
def l2c1IndexedActiveFig13BundledObligations
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        l2Component1IndexedActiveRoleTable)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    indexedActiveWindows hplane

open NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations in
def l2c2IndexedActiveFig13BundledObligations
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        l2Component2IndexedActiveRoleTable)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    indexedActiveWindows hplane

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical named-site-rectangle routing and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_site_rect_fig13_tiles_plane_position_source
    (canonicalSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_site_rect_translated_obligations_position_source
      (l2c1SiteRectFig13Obligations canonicalSiteRectRouting hplane) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical named-site-rectangle routing and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c1_site_rect_fig13_tiles_plane_position_source
    (canonicalSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_site_rect_translated_obligations_position_source
      (l2c1SiteRectFig13Obligations canonicalSiteRectRouting hplane) h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical named-site-rectangle routing and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_site_rect_fig13_tiles_plane_position_source
    (canonicalSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_site_rect_translated_obligations_position_source
      (l2c2SiteRectFig13Obligations canonicalSiteRectRouting hplane) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical named-site-rectangle routing and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c2_site_rect_fig13_tiles_plane_position_source
    (canonicalSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_site_rect_translated_obligations_position_source
      (l2c2SiteRectFig13Obligations canonicalSiteRectRouting hplane) h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
bundled canonical free-site-rectangle routing and translated active-box
obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
bundled canonical free-site-rectangle routing and translated active-box
obligations.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
bundled canonical free-site-rectangle routing and translated active-box
obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
bundled canonical free-site-rectangle routing and translated active-box
obligations.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_translated_obligations_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows, generated Figure 13/Figure 16 compatibility,
and translated active-box obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_translated_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows, generated Figure 13/Figure 16 compatibility,
and translated active-box obligations.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_translated_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows, generated Figure 13/Figure 16 compatibility,
and translated active-box obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_translated_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows, generated Figure 13/Figure 16 compatibility,
and translated active-box obligations.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_translated_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing, translated active-box obligations, and
the Robinson Section 7 tower/indexed-box certificate route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_tower_obligations_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
      O.toL2C1TowerIndexedBoxObligations h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing, translated active-box obligations, and
the Robinson Section 7 tower/indexed-box certificate route.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_tower_obligations_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
      O.toL2C1TowerIndexedBoxObligations h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing, translated active-box obligations, and
the Robinson Section 7 tower/indexed-box certificate route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_tower_obligations_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
      O.toL2C2TowerIndexedBoxObligations h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing, translated active-box obligations, and
the Robinson Section 7 tower/indexed-box certificate route.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_tower_obligations_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
      O.toL2C2TowerIndexedBoxObligations h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows, translated active-box obligations, and the
Robinson Section 7 tower/indexed-box certificate route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_tower_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
      O.toL2C1TowerIndexedBoxObligations h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows, translated active-box obligations, and the
Robinson Section 7 tower/indexed-box certificate route.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_tower_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
      O.toL2C1TowerIndexedBoxObligations h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows, translated active-box obligations, and the
Robinson Section 7 tower/indexed-box certificate route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_tower_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
      O.toL2C2TowerIndexedBoxObligations h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows, translated active-box obligations, and the
Robinson Section 7 tower/indexed-box certificate route.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_tower_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
      O.toL2C2TowerIndexedBoxObligations h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_tower_obligations_interiorRows
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
      O.toL2C1TowerIndexedBoxObligations
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_tower_obligations_interiorRows
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
      O.toL2C1TowerIndexedBoxObligations
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_tower_obligations_interiorRows
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
      O.toL2C2TowerIndexedBoxObligations
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_tower_obligations_interiorRows
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
      O.toL2C2TowerIndexedBoxObligations
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_tower_obligations_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
      O.toL2C1TowerIndexedBoxObligations
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_tower_obligations_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
      O.toL2C1TowerIndexedBoxObligations
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_tower_obligations_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
      O.toL2C2TowerIndexedBoxObligations
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_tower_obligations_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
      O.toL2C2TowerIndexedBoxObligations
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
translation-invariant indexed active/corner windows, generated Figure 13/Figure
16 compatibility, and translated active-box obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_indexed_active_translated_obligations_position_source
    (O : NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
translation-invariant indexed active/corner windows, generated Figure 13/Figure
16 compatibility, and translated active-box obligations.
-/
theorem
    domino_problem_undecidable_l2c1_indexed_active_translated_obligations_position_source
    (O : NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
translation-invariant indexed active/corner windows, generated Figure 13/Figure
16 compatibility, and translated active-box obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_indexed_active_translated_obligations_position_source
    (O : NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
translation-invariant indexed active/corner windows, generated Figure 13/Figure
16 compatibility, and translated active-box obligations.
-/
theorem
    domino_problem_undecidable_l2c2_indexed_active_translated_obligations_position_source
    (O : NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_tiles_plane_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfOriginZeroFig13TilesPlane
        originZeroWindows hplane)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_fig13_tiles_plane_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2Component1Figure18RoutedCertificateOfOriginZeroFig13TilesPlane
        originZeroWindows hplane)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_tiles_plane_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfOriginZeroFig13TilesPlane
        originZeroWindows hplane)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_fig13_tiles_plane_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2Component2Figure18RoutedCertificateOfOriginZeroFig13TilesPlane
        originZeroWindows hplane)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
translation-invariant indexed active/corner windows and a raw Figure 13 plane
tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_indexed_active_fig13_tiles_plane_position_source
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        l2Component1IndexedActiveRoleTable)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_indexed_active_translated_obligations_position_source
      (l2c1IndexedActiveFig13BundledObligations indexedActiveWindows hplane) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
translation-invariant indexed active/corner windows and a raw Figure 13 plane
tiling.
-/
theorem
    domino_problem_undecidable_l2c1_indexed_active_fig13_tiles_plane_position_source
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        l2Component1IndexedActiveRoleTable)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_indexed_active_translated_obligations_position_source
      (l2c1IndexedActiveFig13BundledObligations indexedActiveWindows hplane) h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
translation-invariant indexed active/corner windows and a raw Figure 13 plane
tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_indexed_active_fig13_tiles_plane_position_source
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        l2Component2IndexedActiveRoleTable)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_indexed_active_translated_obligations_position_source
      (l2c2IndexedActiveFig13BundledObligations indexedActiveWindows hplane) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
translation-invariant indexed active/corner windows and a raw Figure 13 plane
tiling.
-/
theorem
    domino_problem_undecidable_l2c2_indexed_active_fig13_tiles_plane_position_source
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        l2Component2IndexedActiveRoleTable)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_indexed_active_translated_obligations_position_source
      (l2c2IndexedActiveFig13BundledObligations indexedActiveWindows hplane) h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows, a raw Figure 13 plane tiling, and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_tiles_plane_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_tiles_plane_position_source
      originZeroWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows, a raw Figure 13 plane tiling, and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_fig13_tiles_plane_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_fig13_tiles_plane_position_source
      originZeroWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows, a raw Figure 13 plane tiling, and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_tiles_plane_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_tiles_plane_position_source
      originZeroWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows, a raw Figure 13 plane tiling, and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_fig13_tiles_plane_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_fig13_tiles_plane_position_source
      originZeroWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
translation-invariant indexed active/corner windows, a raw Figure 13 plane
tiling, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_indexed_active_fig13_tiles_plane_interiorRows
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        l2Component1IndexedActiveRoleTable)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_indexed_active_fig13_tiles_plane_position_source
      indexedActiveWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
translation-invariant indexed active/corner windows, a raw Figure 13 plane
tiling, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_indexed_active_fig13_tiles_plane_interiorRows
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        l2Component1IndexedActiveRoleTable)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_indexed_active_fig13_tiles_plane_position_source
      indexedActiveWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
translation-invariant indexed active/corner windows, a raw Figure 13 plane
tiling, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_indexed_active_fig13_tiles_plane_interiorRows
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        l2Component2IndexedActiveRoleTable)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_indexed_active_fig13_tiles_plane_position_source
      indexedActiveWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
translation-invariant indexed active/corner windows, a raw Figure 13 plane
tiling, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_indexed_active_fig13_tiles_plane_interiorRows
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        l2Component2IndexedActiveRoleTable)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_indexed_active_fig13_tiles_plane_position_source
      indexedActiveWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_fig13_tiles_plane_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_site_rect_translated_obligations_position_source
      (l2c1FreeSiteRectFig13Obligations canonicalFreeSiteRectRouting hplane) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_fig13_tiles_plane_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_site_rect_translated_obligations_position_source
      (l2c1FreeSiteRectFig13Obligations canonicalFreeSiteRectRouting hplane) h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_fig13_tiles_plane_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_site_rect_translated_obligations_position_source
      (l2c2FreeSiteRectFig13Obligations canonicalFreeSiteRectRouting hplane) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_fig13_tiles_plane_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_site_rect_translated_obligations_position_source
      (l2c2FreeSiteRectFig13Obligations canonicalFreeSiteRectRouting hplane) h

/-- Short local name for the layered Robinson Section 7 obstruction route. -/
abbrev LayeredSection7ObstructionRoutingInvariant
    (D : OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData) :
    Prop :=
  D.HasRobinsonSection7ObstructionRoutingInvariant

/-- Finite-box form of the raw Figure 13 scaffold hypothesis. -/
abbrev Figure13TileableBoxes : Prop :=
  ∀ r : Nat, TileableBox fig13Tiles r

/-- Cofinal-square form of the raw Figure 13 scaffold hypothesis. -/
abbrev Figure13CofinalTileableSquares : Prop :=
  ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ TileableSquare fig13Tiles m

/-- Finite checked Figure 16-recognized Robinson board macro-square hypothesis. -/
abbrev Figure13CheckedRecognizedMacroSquares : Prop :=
  HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares

/--
Canonical finite checked Figure 16-recognized Robinson board macro-square
hypothesis.
-/
abbrev Figure13CanonicalCheckedRecognizedMacroSquares : Prop :=
  HasCanonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares

/--
Finite checked Figure 16-recognized Robinson board macro-square hypothesis for
the corrected Figure 18 site-compatible target.
-/
abbrev Figure18CheckedRecognizedCompatibleMacroSquares : Prop :=
  HasCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares

/--
Canonical finite checked Figure 16-recognized Robinson board macro-square
hypothesis for the corrected Figure 18 site-compatible target.
-/
abbrev Figure18CanonicalCheckedRecognizedCompatibleMacroSquares : Prop :=
  HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares

/--
Canonical Figure 16 macro-square hypothesis using only checked source layer
stacks and raw Figure 13 boundary compatibility.
-/
abbrev Figure18CanonicalRawBoundaryMacroSquares : Prop :=
  HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares

/-- Finite-check form of `Figure18CanonicalRawBoundaryMacroSquares`. -/
abbrev Figure18CanonicalRawBoundaryMacroSquaresBool : Prop :=
  HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool

theorem canonicalRawBoundaryMacroSquares_of_bool
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool) :
    Figure18CanonicalRawBoundaryMacroSquares :=
  canonicalCheckedFigure16SourceRawBoundary_of_bool hlevel

theorem canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares) :
    Figure18CanonicalCheckedRecognizedCompatibleMacroSquares :=
  canonicalCheckedFigure16RecognizedCompatible_of_sourceRawBoundary hlevel

theorem canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundaryBool
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool) :
    Figure18CanonicalCheckedRecognizedCompatibleMacroSquares :=
  canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary
    (canonicalRawBoundaryMacroSquares_of_bool hlevel)

theorem tilesPlane_fig13Tiles_of_checkedRecognizedMacroSquares
    (hlevel : Figure13CheckedRecognizedMacroSquares) :
    TilesPlane fig13Tiles :=
  tilesPlane_fig13Tiles_of_checkedFigure16RecognizedRobinsonBoardLevelMacroSquares
    hlevel

theorem tilesPlane_fig13Tiles_of_canonicalCheckedRecognizedMacroSquares
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares) :
    TilesPlane fig13Tiles :=
  tilesPlane_fig13Tiles_of_canonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares
    hlevel

theorem tilesPlane_fig13Tiles_of_canonicalRawBoundaryMacroSquares
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares) :
    TilesPlane fig13Tiles :=
  tilesPlane_fig13Tiles_of_canonicalCheckedFigure16SourceRawBoundary hlevel

theorem tilesPlane_fig13Tiles_of_canonicalRawBoundaryMacroSquaresBool
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool) :
    TilesPlane fig13Tiles :=
  tilesPlane_fig13Tiles_of_canonicalRawBoundaryMacroSquares
    (canonicalRawBoundaryMacroSquares_of_bool hlevel)

theorem tilesPlane_figure18ScaffoldTiles_of_checkedRecognizedCompatibleMacroSquares
    (hlevel : Figure18CheckedRecognizedCompatibleMacroSquares) :
    TilesPlane figure18ScaffoldTiles :=
  tilesPlane_figure18ScaffoldTiles_of_checkedFigure16RecognizedCompatible
    hlevel

theorem
    tilesPlane_figure18ScaffoldTiles_of_canonicalCheckedRecognizedCompatibleMacroSquares
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares) :
    TilesPlane figure18ScaffoldTiles :=
  tilesPlane_figure18ScaffoldTiles_of_canonicalCheckedFigure16RecognizedCompatible
    hlevel

open NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations in
def l2c1FreeSiteRectCanonicalCheckedFig16BundledObligations
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveCanonicalCheckedFigure16MacroSquares
    canonicalFreeSiteRectRouting hlevel

open NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations in
def l2c2FreeSiteRectCanonicalCheckedFig16BundledObligations
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveCanonicalCheckedFigure16MacroSquares
    canonicalFreeSiteRectRouting hlevel

open NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations in
def l2c1FreeSiteRectCanonicalCheckedCompatibleFig16BundledObligations
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveCanonicalCheckedCompatibleFigure16MacroSquares
    canonicalFreeSiteRectRouting hlevel

open NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations in
def l2c2FreeSiteRectCanonicalCheckedCompatibleFig16BundledObligations
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveCanonicalCheckedCompatibleFigure16MacroSquares
    canonicalFreeSiteRectRouting hlevel

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing and canonical checked Figure 16
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_canonical_checked_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_free_site_rect_translated_obligations_position_source
      (l2c1FreeSiteRectCanonicalCheckedFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing and canonical checked Figure 16
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_canonical_checked_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_free_site_rect_translated_obligations_position_source
      (l2c1FreeSiteRectCanonicalCheckedFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing and canonical checked Figure 16
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_canonical_checked_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_free_site_rect_translated_obligations_position_source
      (l2c2FreeSiteRectCanonicalCheckedFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing and canonical checked Figure 16
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_canonical_checked_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_free_site_rect_translated_obligations_position_source
      (l2c2FreeSiteRectCanonicalCheckedFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing and the corrected compatible Figure 16
macro-square target.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_compatible_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_free_site_rect_translated_obligations_position_source
      (l2c1FreeSiteRectCanonicalCheckedCompatibleFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing and the corrected compatible Figure 16
macro-square target.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_compatible_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_free_site_rect_translated_obligations_position_source
      (l2c1FreeSiteRectCanonicalCheckedCompatibleFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing and the corrected compatible Figure 16
macro-square target.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_compatible_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_free_site_rect_translated_obligations_position_source
      (l2c2FreeSiteRectCanonicalCheckedCompatibleFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing and the corrected compatible Figure 16
macro-square target.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_compatible_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_free_site_rect_translated_obligations_position_source
      (l2c2FreeSiteRectCanonicalCheckedCompatibleFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing and canonical raw-boundary Figure 16
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_raw_boundary_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_free_site_rect_compatible_fig16_position_source
      canonicalFreeSiteRectRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing and canonical raw-boundary Figure 16
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_raw_boundary_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_free_site_rect_compatible_fig16_position_source
      canonicalFreeSiteRectRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing and canonical raw-boundary Figure 16
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_raw_boundary_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_free_site_rect_compatible_fig16_position_source
      canonicalFreeSiteRectRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing and canonical raw-boundary Figure 16
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_raw_boundary_fig16_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_free_site_rect_compatible_fig16_position_source
      canonicalFreeSiteRectRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_raw_boundary_fig16_bool_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_free_site_rect_raw_boundary_fig16_position_source
      canonicalFreeSiteRectRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_raw_boundary_fig16_bool_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_free_site_rect_raw_boundary_fig16_position_source
      canonicalFreeSiteRectRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_raw_boundary_fig16_bool_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_free_site_rect_raw_boundary_fig16_position_source
      canonicalFreeSiteRectRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_raw_boundary_fig16_bool_position_source
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_free_site_rect_raw_boundary_fig16_position_source
      canonicalFreeSiteRectRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and canonical checked Figure 16
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_canonical_checked_fig16_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_free_site_rect_canonical_checked_fig16_position_source
      section7Routing hlevel h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and canonical checked Figure 16
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_section7_canonical_checked_fig16_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_free_site_rect_canonical_checked_fig16_position_source
      section7Routing hlevel h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and canonical checked Figure 16
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_canonical_checked_fig16_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_free_site_rect_canonical_checked_fig16_position_source
      section7Routing hlevel h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and canonical checked Figure 16
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_section7_canonical_checked_fig16_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_free_site_rect_canonical_checked_fig16_position_source
      section7Routing hlevel h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and canonical raw-boundary Figure 16
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_free_site_rect_raw_boundary_fig16_position_source
      section7Routing hlevel h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and canonical raw-boundary Figure 16
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_free_site_rect_raw_boundary_fig16_position_source
      section7Routing hlevel h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and canonical raw-boundary Figure 16
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_free_site_rect_raw_boundary_fig16_position_source
      section7Routing hlevel h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and canonical raw-boundary Figure 16
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_free_site_rect_raw_boundary_fig16_position_source
      section7Routing hlevel h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_bool_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
      section7Routing (canonicalRawBoundaryMacroSquares_of_bool hlevel) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_bool_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
      section7Routing (canonicalRawBoundaryMacroSquares_of_bool hlevel) h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_bool_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
      section7Routing (canonicalRawBoundaryMacroSquares_of_bool hlevel) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_bool_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
      section7Routing (canonicalRawBoundaryMacroSquares_of_bool hlevel) h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical checked Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_canonical_checked_fig16_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_canonical_checked_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical checked Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_section7_canonical_checked_fig16_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_canonical_checked_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical checked Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_canonical_checked_fig16_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_canonical_checked_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical checked Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_section7_canonical_checked_fig16_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure13CanonicalCheckedRecognizedMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_canonical_checked_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical raw-boundary Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical raw-boundary Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical raw-boundary Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical raw-boundary Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, finite-checked canonical raw-boundary
Figure 16 macro-squares, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_bool_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
      section7Routing (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, finite-checked canonical raw-boundary
Figure 16 macro-squares, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_bool_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
      section7Routing (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, finite-checked canonical raw-boundary
Figure 16 macro-squares, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_bool_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
      section7Routing (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, finite-checked canonical raw-boundary
Figure 16 macro-squares, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_bool_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
      section7Routing (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_free_site_rect_fig13_tiles_plane_position_source
      section7Routing hplane h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_free_site_rect_fig13_tiles_plane_position_source
      section7Routing hplane h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_free_site_rect_fig13_tiles_plane_position_source
      section7Routing hplane h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_free_site_rect_fig13_tiles_plane_position_source
      section7Routing hplane h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and finite raw Figure 13 boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_fig13_tileable_boxes_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_position_source
      section7Routing
      (OllingerRobinson.Figure13Layers.tilesPlane_fig13Tiles_of_tileableBoxes hboxes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and finite raw Figure 13 boxes.
-/
theorem
    domino_problem_undecidable_l2c1_section7_fig13_tileable_boxes_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_position_source
      section7Routing
      (OllingerRobinson.Figure13Layers.tilesPlane_fig13Tiles_of_tileableBoxes hboxes)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and finite raw Figure 13 boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_fig13_tileable_boxes_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_position_source
      section7Routing
      (OllingerRobinson.Figure13Layers.tilesPlane_fig13Tiles_of_tileableBoxes hboxes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and finite raw Figure 13 boxes.
-/
theorem
    domino_problem_undecidable_l2c2_section7_fig13_tileable_boxes_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_position_source
      section7Routing
      (OllingerRobinson.Figure13Layers.tilesPlane_fig13Tiles_of_tileableBoxes hboxes)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and cofinal raw Figure 13 squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_fig13_cofinal_squares_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hsquares : Figure13CofinalTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_position_source
      section7Routing
      (OllingerRobinson.Figure13Layers.tilesPlane_fig13Tiles_of_cofinal_tileableSquares
        hsquares)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and cofinal raw Figure 13 squares.
-/
theorem
    domino_problem_undecidable_l2c1_section7_fig13_cofinal_squares_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hsquares : Figure13CofinalTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_position_source
      section7Routing
      (OllingerRobinson.Figure13Layers.tilesPlane_fig13Tiles_of_cofinal_tileableSquares
        hsquares)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and cofinal raw Figure 13 squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_fig13_cofinal_squares_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hsquares : Figure13CofinalTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_position_source
      section7Routing
      (OllingerRobinson.Figure13Layers.tilesPlane_fig13Tiles_of_cofinal_tileableSquares
        hsquares)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and cofinal raw Figure 13 squares.
-/
theorem
    domino_problem_undecidable_l2c2_section7_fig13_cofinal_squares_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hsquares : Figure13CofinalTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_position_source
      section7Routing
      (OllingerRobinson.Figure13Layers.tilesPlane_fig13Tiles_of_cofinal_tileableSquares
        hsquares)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, a raw Figure 13 plane tiling, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_position_source
      section7Routing hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, a raw Figure 13 plane tiling, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_position_source
      section7Routing hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, a raw Figure 13 plane tiling, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_position_source
      section7Routing hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, a raw Figure 13 plane tiling, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_position_source
      section7Routing hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, finite raw Figure 13 boxes, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_fig13_tileable_boxes_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_fig13_tileable_boxes_position_source
      section7Routing hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, finite raw Figure 13 boxes, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_section7_fig13_tileable_boxes_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_fig13_tileable_boxes_position_source
      section7Routing hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, finite raw Figure 13 boxes, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_fig13_tileable_boxes_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_fig13_tileable_boxes_position_source
      section7Routing hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, finite raw Figure 13 boxes, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_section7_fig13_tileable_boxes_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_fig13_tileable_boxes_position_source
      section7Routing hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, cofinal raw Figure 13 squares, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_fig13_cofinal_squares_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hsquares : Figure13CofinalTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_fig13_cofinal_squares_position_source
      section7Routing hsquares
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, cofinal raw Figure 13 squares, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_section7_fig13_cofinal_squares_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hsquares : Figure13CofinalTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_fig13_cofinal_squares_position_source
      section7Routing hsquares
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, cofinal raw Figure 13 squares, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_fig13_cofinal_squares_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hsquares : Figure13CofinalTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_fig13_cofinal_squares_position_source
      section7Routing hsquares
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, cofinal raw Figure 13 squares, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_section7_fig13_cofinal_squares_interiorRows
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hsquares : Figure13CofinalTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_fig13_cofinal_squares_position_source
      section7Routing hsquares
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing, a raw Figure 13 plane tiling, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_fig13_tiles_plane_interiorRows
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_free_site_rect_fig13_tiles_plane_position_source
      canonicalFreeSiteRectRouting hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing, a raw Figure 13 plane tiling, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_fig13_tiles_plane_interiorRows
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_free_site_rect_fig13_tiles_plane_position_source
      canonicalFreeSiteRectRouting hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing, a raw Figure 13 plane tiling, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_fig13_tiles_plane_interiorRows
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_free_site_rect_fig13_tiles_plane_position_source
      canonicalFreeSiteRectRouting hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing, a raw Figure 13 plane tiling, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_fig13_tiles_plane_interiorRows
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_free_site_rect_fig13_tiles_plane_position_source
      canonicalFreeSiteRectRouting hplane
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical decoded combined-site corridor routing, a raw Figure 13 plane tiling,
and the generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_combined_site_fig13_tiles_plane_decoderStep
    (canonicalCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_combined_site_translated_obligations_decoderStep
      (l2c1Fig13Obligations canonicalCombinedSiteRouting hplane)
      hstep hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical decoded combined-site corridor routing, a raw Figure 13 plane tiling,
and the generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c1_combined_site_fig13_tiles_plane_decoderStep
    (canonicalCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_combined_site_translated_obligations_decoderStep
      (l2c1Fig13Obligations canonicalCombinedSiteRouting hplane)
      hstep hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical decoded combined-site corridor routing, a raw Figure 13 plane tiling,
and the generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_combined_site_fig13_tiles_plane_decoderStep
    (canonicalCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_combined_site_translated_obligations_decoderStep
      (l2c2Fig13Obligations canonicalCombinedSiteRouting hplane)
      hstep hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical decoded combined-site corridor routing, a raw Figure 13 plane tiling,
and the generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c2_combined_site_fig13_tiles_plane_decoderStep
    (canonicalCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_combined_site_translated_obligations_decoderStep
      (l2c2Fig13Obligations canonicalCombinedSiteRouting hplane)
      hstep hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical named-site-rectangle routing, a raw Figure 13 plane tiling, and the
generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_site_rect_fig13_tiles_plane_decoderStep
    (canonicalSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_site_rect_translated_obligations_decoderStep
      (l2c1SiteRectFig13Obligations canonicalSiteRectRouting hplane)
      hstep hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical named-site-rectangle routing, a raw Figure 13 plane tiling, and the
generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c1_site_rect_fig13_tiles_plane_decoderStep
    (canonicalSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_site_rect_translated_obligations_decoderStep
      (l2c1SiteRectFig13Obligations canonicalSiteRectRouting hplane)
      hstep hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical named-site-rectangle routing, a raw Figure 13 plane tiling, and the
generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_site_rect_fig13_tiles_plane_decoderStep
    (canonicalSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_site_rect_translated_obligations_decoderStep
      (l2c2SiteRectFig13Obligations canonicalSiteRectRouting hplane)
      hstep hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical named-site-rectangle routing, a raw Figure 13 plane tiling, and the
generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c2_site_rect_fig13_tiles_plane_decoderStep
    (canonicalSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_site_rect_translated_obligations_decoderStep
      (l2c2SiteRectFig13Obligations canonicalSiteRectRouting hplane)
      hstep hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing, a raw Figure 13 plane tiling, and the
generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_fig13_tiles_plane_decoderStep
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_site_rect_translated_obligations_decoderStep
      (l2c1FreeSiteRectFig13Obligations canonicalFreeSiteRectRouting hplane)
      hstep hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical free-site-rectangle routing, a raw Figure 13 plane tiling, and the
generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_fig13_tiles_plane_decoderStep
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_site_rect_translated_obligations_decoderStep
      (l2c1FreeSiteRectFig13Obligations canonicalFreeSiteRectRouting hplane)
      hstep hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing, a raw Figure 13 plane tiling, and the
generated position-code accumulator step.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_fig13_tiles_plane_decoderStep
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_site_rect_translated_obligations_decoderStep
      (l2c2FreeSiteRectFig13Obligations canonicalFreeSiteRectRouting hplane)
      hstep hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical free-site-rectangle routing, a raw Figure 13 plane tiling, and the
generated position-code accumulator step.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_fig13_tiles_plane_decoderStep
    (canonicalFreeSiteRectRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_site_rect_translated_obligations_decoderStep
      (l2c2FreeSiteRectFig13Obligations canonicalFreeSiteRectRouting hplane)
      hstep hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, with
the indexed-box part stated only for positive radii.  The radius-zero box is
supplied by the scaffold corner tile.
-/
theorem encoded_domino_problem_undecidable_l2c1_tower_pos_boxes_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C1PositiveBoxes
        htower hboxes_pos)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate, with
the indexed-box part stated only for positive radii.
-/
theorem domino_problem_undecidable_l2c1_tower_pos_boxes_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C1PositiveBoxes
        htower hboxes_pos)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate, with
the indexed-box part stated only for positive radii.
-/
theorem encoded_domino_problem_undecidable_l2c2_tower_pos_boxes_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C2PositiveBoxes
        htower hboxes_pos)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate, with
the indexed-box part stated only for positive radii.
-/
theorem domino_problem_undecidable_l2c2_tower_pos_boxes_position_source
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C2PositiveBoxes
        htower hboxes_pos)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate, with
positive-radius indexed boxes and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_tower_pos_boxes_interiorRows
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C1PositiveBoxes
        htower hboxes_pos)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate, with
positive-radius indexed boxes and generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c1_tower_pos_boxes_interiorRows
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C1PositiveBoxes
        htower hboxes_pos)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, with
positive-radius indexed boxes and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_tower_pos_boxes_interiorRows
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C2PositiveBoxes
        htower hboxes_pos)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate, with
positive-radius indexed boxes and generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_tower_pos_boxes_interiorRows
    (htower :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C2PositiveBoxes
        htower hboxes_pos)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
the field-based Robinson Section 7 local signal tower and positive-radius
indexed boxes.
-/
theorem encoded_domino_problem_undecidable_l2c1_signal_tower_pos_boxes_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C1SignalLocalTowerPositiveBoxes
        htower hboxes_pos)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using the field-based Robinson Section 7 local signal tower and
positive-radius indexed boxes.
-/
theorem domino_problem_undecidable_l2c1_signal_tower_pos_boxes_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_position_source
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C1SignalLocalTowerPositiveBoxes
        htower hboxes_pos)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
the field-based Robinson Section 7 local signal tower and positive-radius
indexed boxes.
-/
theorem encoded_domino_problem_undecidable_l2c2_signal_tower_pos_boxes_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C2SignalLocalTowerPositiveBoxes
        htower hboxes_pos)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using the field-based Robinson Section 7 local signal tower and
positive-radius indexed boxes.
-/
theorem domino_problem_undecidable_l2c2_signal_tower_pos_boxes_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_position_source
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C2SignalLocalTowerPositiveBoxes
        htower hboxes_pos)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
the field-based Robinson Section 7 local signal tower, positive-radius indexed
boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_signal_tower_pos_boxes_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C1SignalLocalTowerPositiveBoxes
        htower hboxes_pos)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using the field-based Robinson Section 7 local signal tower, positive-radius
indexed boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c1_signal_tower_pos_boxes_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_towerBoxObligations_interiorRows
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C1SignalLocalTowerPositiveBoxes
        htower hboxes_pos)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
the field-based Robinson Section 7 local signal tower, positive-radius indexed
boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_signal_tower_pos_boxes_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C2SignalLocalTowerPositiveBoxes
        htower hboxes_pos)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using the field-based Robinson Section 7 local signal tower, positive-radius
indexed boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_signal_tower_pos_boxes_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r))
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_towerBoxObligations_interiorRows
      (NatSiteRobinsonTowerIndexedBoxObligations.ofL2C2SignalLocalTowerPositiveBoxes
        htower hboxes_pos)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite-box realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_signal_local_step_boxes_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_signal_local_step_position_source
      hsteps (realizesActiveCornerSquares_of_realizesActiveCornerBoxes realizes) h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite-box realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_signal_local_step_boxes_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_signal_local_step_position_source
      hsteps (realizesActiveCornerSquares_of_realizesActiveCornerBoxes realizes) h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite-box realization, and generated position-coded
source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_signal_local_step_boxes_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_signal_local_step_position_source
      hsteps (realizesActiveCornerSquares_of_realizesActiveCornerBoxes realizes) h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite-box realization, and generated position-coded
source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_signal_local_step_boxes_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_signal_local_step_position_source
      hsteps (realizesActiveCornerSquares_of_realizesActiveCornerBoxes realizes) h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite combined-box patches, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_signal_local_step_patches_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_signal_local_step_boxes_position_source
      hsteps (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches) h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite combined-box patches, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_signal_local_step_patches_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_signal_local_step_boxes_position_source
      hsteps (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches) h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite combined-box patches, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_signal_local_step_patches_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_signal_local_step_boxes_position_source
      hsteps (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches) h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite combined-box patches, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_signal_local_step_patches_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_signal_local_step_boxes_position_source
      hsteps (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches) h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite scaffold/payload layer patches, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_signal_local_step_layer_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_signal_local_step_patches_position_source
      hsteps (activeCornerBoxPatches_of_layerBoxPatches patches) h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite scaffold/payload layer patches, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_signal_local_step_layer_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_signal_local_step_patches_position_source
      hsteps (activeCornerBoxPatches_of_layerBoxPatches patches) h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite scaffold/payload layer patches, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_signal_local_step_layer_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_signal_local_step_patches_position_source
      hsteps (activeCornerBoxPatches_of_layerBoxPatches patches) h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, finite scaffold/payload layer patches, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_signal_local_step_layer_position_source
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_signal_local_step_patches_position_source
      hsteps (activeCornerBoxPatches_of_layerBoxPatches patches) h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, realization, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_signal_local_step_interiorRows
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalStepFreeGrids
        hsteps realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, realization, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_signal_local_step_interiorRows
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C1SignalLocalStepFreeGrids
        hsteps realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, realization, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_signal_local_step_interiorRows
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalStepFreeGrids
        hsteps realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, Robinson Section 7 local obstruction-signal certificates with
coordinate recurrence, realization, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_signal_local_step_interiorRows
    (hsteps :
      OllingerRobinson.HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_robinson_certificate_interiorRows
      (NatSiteRobinsonScaffoldCertificate.ofL2C2SignalLocalStepFreeGrids
        hsteps realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, compatible Robinson level grids, realization, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_compatible_level_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component1BlankCandidate
        hgrids realizes)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, compatible Robinson level grids, realization, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_compatible_level_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component1BlankCandidate
        hgrids realizes)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, compatible Robinson level grids, realization, and generated
position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_compatible_level_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component2BlankCandidate
        hgrids realizes)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, compatible Robinson level grids, realization, and generated
position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_compatible_level_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component2BlankCandidate
        hgrids realizes)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, compatible Robinson level grids, finite scaffold/payload layer
patches, and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_compatible_layer_patches_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component1BlankCandidateLayerPatches
        hgrids patches)
      h

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, compatible Robinson level grids, finite scaffold/payload layer
patches, and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_compatible_level_layer_patches_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component1BlankCandidateLayerPatches
        hgrids patches)
      h

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, compatible Robinson level grids, finite scaffold/payload layer
patches, and generated position-coded source-route obligations.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_compatible_layer_patches_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component2BlankCandidateLayerPatches
        hgrids patches)
      h

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, compatible Robinson level grids, finite scaffold/payload layer
patches, and generated position-coded source-route obligations.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_compatible_level_layer_patches_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component2BlankCandidateLayerPatches
        hgrids patches)
      h

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, compatible Robinson level grids, realization, and the generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_compatible_level_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component1BlankCandidate
        hgrids realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, compatible Robinson level grids, realization, and the generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_compatible_level_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component1BlankCandidate
        hgrids realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, compatible Robinson level grids, realization, and the generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_compatible_level_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component2BlankCandidate
        hgrids realizes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, compatible Robinson level grids, realization, and the generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_compatible_level_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component2BlankCandidate
        hgrids realizes)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, compatible Robinson level grids, finite scaffold/payload layer
patches, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_compatible_level_layer_patches_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component1BlankCandidateLayerPatches
        hgrids patches)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, compatible Robinson level grids, finite scaffold/payload layer
patches, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_compatible_level_layer_patches_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component1BlankCandidateLayerPatches
        hgrids patches)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, compatible Robinson level grids, finite scaffold/payload layer
patches, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_compatible_level_layer_patches_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component2BlankCandidateLayerPatches
        hgrids patches)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, compatible Robinson level grids, finite scaffold/payload layer
patches, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_compatible_level_layer_patches_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonCompatibleLevelObligations.ofL2Component2BlankCandidateLayerPatches
        hgrids patches)
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
