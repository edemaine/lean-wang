/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure18Reduction.Section7.Prelude

/-!
Section 7 final theorem wrappers.

The reusable Section 7 scaffold packages live in
`LeanWang.OllingerRobinsonFigure18Reduction.Section7.Prelude`; this suffix
keeps the theorem-facing aliases separate so edits there rebuild less of the
Section 7 scaffold layer.
-/

namespace LeanWang

namespace TM0FoldedReduction

set_option linter.style.longLine false

open Nat.Partrec (Code)
open OllingerRobinson
open OllingerRobinson.Figure18ScaffoldData
open OllingerRobinson.Figure13Layers
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData

/--
Encoded domino undecidability from the first audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
macro-squares.
-/
theorem encoded_domino_problem_undecidable_l2c1_level_compatible_fig16_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1CompatibleLevelCanonicalCheckedCompatibleFig16Obligations
        hgrids hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
macro-squares.
-/
theorem domino_problem_undecidable_l2c1_level_compatible_fig16_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1CompatibleLevelCanonicalCheckedCompatibleFig16Obligations
        hgrids hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
macro-squares.
-/
theorem encoded_domino_problem_undecidable_l2c2_level_compatible_fig16_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2CompatibleLevelCanonicalCheckedCompatibleFig16Obligations
        hgrids hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
macro-squares.
-/
theorem domino_problem_undecidable_l2c2_level_compatible_fig16_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2CompatibleLevelCanonicalCheckedCompatibleFig16Obligations
        hgrids hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
level data.
-/
theorem encoded_domino_problem_undecidable_l2c1_level_compatible_fig16_level_data_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_level_compatible_fig16_position_source
      hgrids
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
level data.
-/
theorem domino_problem_undecidable_l2c1_level_compatible_fig16_level_data_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_level_compatible_fig16_position_source
      hgrids
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
level data.
-/
theorem encoded_domino_problem_undecidable_l2c2_level_compatible_fig16_level_data_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_level_compatible_fig16_position_source
      hgrids
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
level data.
-/
theorem domino_problem_undecidable_l2c2_level_compatible_fig16_level_data_position_source
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_level_compatible_fig16_position_source
      hgrids
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
checked compatible Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_l2c1_canonical_corridor_compatible_fig16_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_level_compatible_fig16_position_source
      (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCorridorRouting
        canonicalCorridorRouting)
      hlevel h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
checked compatible Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_l2c1_canonical_corridor_compatible_fig16_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_level_compatible_fig16_position_source
      (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCorridorRouting
        canonicalCorridorRouting)
      hlevel h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
checked compatible Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_corridor_compatible_fig16_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_level_compatible_fig16_position_source
      (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCorridorRouting
        canonicalCorridorRouting)
      hlevel h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
checked compatible Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_l2c2_canonical_corridor_compatible_fig16_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_level_compatible_fig16_position_source
      (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCorridorRouting
        canonicalCorridorRouting)
      hlevel h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
checked compatible Figure 16 level data.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_corridor_fig16_level_data_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_corridor_compatible_fig16_position_source
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
checked compatible Figure 16 level data.
-/
theorem
    domino_problem_undecidable_l2c1_corridor_fig16_level_data_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_corridor_compatible_fig16_position_source
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
checked compatible Figure 16 level data.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_corridor_fig16_level_data_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_corridor_compatible_fig16_position_source
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
checked compatible Figure 16 level data.
-/
theorem
    domino_problem_undecidable_l2c2_corridor_fig16_level_data_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_corridor_compatible_fig16_position_source
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_corridor_raw_boundary_fig16_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_corridor_compatible_fig16_position_source
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_corridor_raw_boundary_fig16_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_corridor_compatible_fig16_position_source
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_corridor_raw_boundary_fig16_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_corridor_compatible_fig16_position_source
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_corridor_raw_boundary_fig16_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_corridor_compatible_fig16_position_source
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and finite-checked
canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_corridor_fig16_bool_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_corridor_raw_boundary_fig16_position_source
      canonicalCorridorRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and finite-checked
canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_corridor_fig16_bool_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_corridor_raw_boundary_fig16_position_source
      canonicalCorridorRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and finite-checked
canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_corridor_fig16_bool_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_corridor_raw_boundary_fig16_position_source
      canonicalCorridorRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing and finite-checked
canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_corridor_fig16_bool_position_source
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_corridor_raw_boundary_fig16_position_source
      canonicalCorridorRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
compatible Robinson level grids, canonical checked compatible Figure 16
macro-squares, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_level_compatible_fig16_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_level_compatible_fig16_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
compatible Robinson level grids, canonical checked compatible Figure 16
macro-squares, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c1_level_compatible_fig16_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_level_compatible_fig16_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
compatible Robinson level grids, canonical checked compatible Figure 16
macro-squares, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_level_compatible_fig16_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_level_compatible_fig16_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
compatible Robinson level grids, canonical checked compatible Figure 16
macro-squares, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_level_compatible_fig16_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_level_compatible_fig16_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
compatible Robinson level grids, canonical checked compatible Figure 16 level
data, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_level_compatible_fig16_level_data_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_level_compatible_fig16_level_data_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
compatible Robinson level grids, canonical checked compatible Figure 16 level
data, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c1_level_compatible_fig16_level_data_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_level_compatible_fig16_level_data_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
compatible Robinson level grids, canonical checked compatible Figure 16 level
data, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_level_compatible_fig16_level_data_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_level_compatible_fig16_level_data_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
compatible Robinson level grids, canonical checked compatible Figure 16 level
data, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_level_compatible_fig16_level_data_interiorRows
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_level_compatible_fig16_level_data_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical checked
compatible Figure 16 macro-squares, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_corridor_compatible_fig16_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_level_compatible_fig16_interiorRows
      (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCorridorRouting
        canonicalCorridorRouting)
      hlevel hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical checked
compatible Figure 16 macro-squares, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_corridor_compatible_fig16_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_level_compatible_fig16_interiorRows
      (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCorridorRouting
        canonicalCorridorRouting)
      hlevel hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical checked
compatible Figure 16 macro-squares, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_corridor_compatible_fig16_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_level_compatible_fig16_interiorRows
      (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCorridorRouting
        canonicalCorridorRouting)
      hlevel hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical checked
compatible Figure 16 macro-squares, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_corridor_compatible_fig16_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_level_compatible_fig16_interiorRows
      (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCorridorRouting
        canonicalCorridorRouting)
      hlevel hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical checked
compatible Figure 16 level data, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_corridor_fig16_level_data_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_corridor_fig16_level_data_position_source
      canonicalCorridorRouting hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical checked
compatible Figure 16 level data, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_corridor_fig16_level_data_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_corridor_fig16_level_data_position_source
      canonicalCorridorRouting hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical checked
compatible Figure 16 level data, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_corridor_fig16_level_data_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_corridor_fig16_level_data_position_source
      canonicalCorridorRouting hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical checked
compatible Figure 16 level data, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_corridor_fig16_level_data_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_corridor_fig16_level_data_position_source
      canonicalCorridorRouting hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical
raw-boundary Figure 16 macro-squares, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_corridor_raw_boundary_fig16_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_corridor_compatible_fig16_interiorRows
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical
raw-boundary Figure 16 macro-squares, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_corridor_raw_boundary_fig16_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_corridor_compatible_fig16_interiorRows
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical
raw-boundary Figure 16 macro-squares, and the generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_corridor_raw_boundary_fig16_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_corridor_compatible_fig16_interiorRows
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, canonical
raw-boundary Figure 16 macro-squares, and the generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_corridor_raw_boundary_fig16_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_corridor_compatible_fig16_interiorRows
      canonicalCorridorRouting
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundary hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, finite-checked
canonical raw-boundary Figure 16 macro-squares, and the generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_canonical_corridor_fig16_bool_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_canonical_corridor_raw_boundary_fig16_interiorRows
      canonicalCorridorRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, finite-checked
canonical raw-boundary Figure 16 macro-squares, and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_l2c1_canonical_corridor_fig16_bool_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_canonical_corridor_raw_boundary_fig16_interiorRows
      canonicalCorridorRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, finite-checked
canonical raw-boundary Figure 16 macro-squares, and the generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_corridor_fig16_bool_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_canonical_corridor_raw_boundary_fig16_interiorRows
      canonicalCorridorRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
canonical Robinson Section 7 corridor-transmission routing, finite-checked
canonical raw-boundary Figure 16 macro-squares, and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_l2c2_canonical_corridor_fig16_bool_interiorRows
    (canonicalCorridorRouting :
      OllingerRobinson.HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_canonical_corridor_raw_boundary_fig16_interiorRows
      canonicalCorridorRouting
      (canonicalRawBoundaryMacroSquares_of_bool hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked
compatible Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_l2c1_signal_tower_fig16_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1SignalTowerCanonicalCheckedCompatibleFig16Obligations
        htower hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked
compatible Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_l2c1_signal_tower_fig16_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1SignalTowerCanonicalCheckedCompatibleFig16Obligations
        htower hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked
compatible Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_l2c2_signal_tower_fig16_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2SignalTowerCanonicalCheckedCompatibleFig16Obligations
        htower hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked
compatible Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_l2c2_signal_tower_fig16_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2SignalTowerCanonicalCheckedCompatibleFig16Obligations
        htower hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked
compatible Figure 16 level data.
-/
theorem encoded_domino_problem_undecidable_l2c1_signal_tower_fig16_level_data_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_fig16_position_source
      htower
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked
compatible Figure 16 level data.
-/
theorem domino_problem_undecidable_l2c1_signal_tower_fig16_level_data_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_fig16_position_source
      htower
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked
compatible Figure 16 level data.
-/
theorem encoded_domino_problem_undecidable_l2c2_signal_tower_fig16_level_data_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_fig16_position_source
      htower
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked
compatible Figure 16 level data.
-/
theorem domino_problem_undecidable_l2c2_signal_tower_fig16_level_data_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_fig16_position_source
      htower
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
the field-based Robinson Section 7 signal tower, canonical checked compatible
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_signal_tower_fig16_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_fig16_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the field-based Robinson Section 7 signal tower, canonical checked compatible
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c1_signal_tower_fig16_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_fig16_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the field-based Robinson Section 7 signal tower, canonical checked compatible
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_signal_tower_fig16_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_fig16_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the field-based Robinson Section 7 signal tower, canonical checked compatible
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_signal_tower_fig16_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_fig16_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
the field-based Robinson Section 7 signal tower, canonical checked compatible
Figure 16 level data, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_signal_tower_fig16_level_data_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_fig16_level_data_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the field-based Robinson Section 7 signal tower, canonical checked compatible
Figure 16 level data, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c1_signal_tower_fig16_level_data_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_fig16_level_data_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the field-based Robinson Section 7 signal tower, canonical checked compatible
Figure 16 level data, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_signal_tower_fig16_level_data_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_fig16_level_data_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the field-based Robinson Section 7 signal tower, canonical checked compatible
Figure 16 level data, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_signal_tower_fig16_level_data_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_fig16_level_data_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
tiling-dependent Robinson geometry, decoded combined-site corridor routing,
and canonical checked compatible Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_l2c1_geom_combined_fig16_position_source
    (geomCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1GeomCombinedCanonicalCheckedCompatibleFig16Obligations
        geomCombinedSiteRouting hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
tiling-dependent Robinson geometry, decoded combined-site corridor routing,
and canonical checked compatible Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_l2c1_geom_combined_fig16_position_source
    (geomCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1GeomCombinedCanonicalCheckedCompatibleFig16Obligations
        geomCombinedSiteRouting hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
tiling-dependent Robinson geometry, decoded combined-site corridor routing,
and canonical checked compatible Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_l2c2_geom_combined_fig16_position_source
    (geomCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2GeomCombinedCanonicalCheckedCompatibleFig16Obligations
        geomCombinedSiteRouting hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
tiling-dependent Robinson geometry, decoded combined-site corridor routing,
and canonical checked compatible Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_l2c2_geom_combined_fig16_position_source
    (geomCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2GeomCombinedCanonicalCheckedCompatibleFig16Obligations
        geomCombinedSiteRouting hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
tiling-dependent Robinson geometry, decoded combined-site corridor routing,
canonical checked compatible Figure 16 macro-squares, and the generated
interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_geom_combined_fig16_interiorRows
    (geomCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_geom_combined_fig16_position_source
      geomCombinedSiteRouting hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
tiling-dependent Robinson geometry, decoded combined-site corridor routing,
canonical checked compatible Figure 16 macro-squares, and the generated
interior position-code rows.
-/
theorem domino_problem_undecidable_l2c1_geom_combined_fig16_interiorRows
    (geomCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_geom_combined_fig16_position_source
      geomCombinedSiteRouting hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
tiling-dependent Robinson geometry, decoded combined-site corridor routing,
canonical checked compatible Figure 16 macro-squares, and the generated
interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_geom_combined_fig16_interiorRows
    (geomCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_geom_combined_fig16_position_source
      geomCombinedSiteRouting hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
tiling-dependent Robinson geometry, decoded combined-site corridor routing,
canonical checked compatible Figure 16 macro-squares, and the generated
interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_geom_combined_fig16_interiorRows
    (geomCombinedSiteRouting :
      OllingerRobinson.HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_geom_combined_fig16_position_source
      geomCombinedSiteRouting hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and canonical checked compatible
Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig16_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_fig16_position_source
      (l2c1SignalTowerOfOriginZeroCheckedStacks hchecked) hlevel h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and canonical checked compatible
Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_l2c1_checked_signal_tower_fig16_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_fig16_position_source
      (l2c1SignalTowerOfOriginZeroCheckedStacks hchecked) hlevel h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and canonical checked compatible
Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig16_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_fig16_position_source
      (l2c2SignalTowerOfOriginZeroCheckedStacks hchecked) hlevel h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and canonical checked compatible
Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_l2c2_checked_signal_tower_fig16_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_fig16_position_source
      (l2c2SignalTowerOfOriginZeroCheckedStacks hchecked) hlevel h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks, canonical checked compatible
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig16_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig16_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks, canonical checked compatible
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c1_checked_signal_tower_fig16_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig16_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks, canonical checked compatible
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig16_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig16_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks, canonical checked compatible
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_checked_signal_tower_fig16_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig16_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_raw_boundary_bool_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig16_position_source
      hchecked
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundaryBool hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_checked_raw_boundary_bool_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig16_position_source
      hchecked
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundaryBool hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_raw_boundary_bool_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig16_position_source
      hchecked
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundaryBool hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and finite-checked canonical
raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_checked_raw_boundary_bool_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig16_position_source
      hchecked
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_rawBoundaryBool hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks, finite-checked canonical raw-boundary
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_raw_boundary_bool_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_raw_boundary_bool_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks, finite-checked canonical raw-boundary
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_checked_raw_boundary_bool_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_raw_boundary_bool_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks, finite-checked canonical raw-boundary
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_raw_boundary_bool_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_raw_boundary_bool_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks, finite-checked canonical raw-boundary
Figure 16 macro-squares, and the generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_checked_raw_boundary_bool_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_raw_boundary_bool_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and row-major checked raw-boundary
Figure 16 level data.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_level_data_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_raw_boundary_bool_position_source
      hchecked
      (canonicalRawBoundaryMacroSquaresBool_of_checkedLevelData hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and row-major checked raw-boundary
Figure 16 level data.
-/
theorem domino_problem_undecidable_l2c1_checked_level_data_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_raw_boundary_bool_position_source
      hchecked
      (canonicalRawBoundaryMacroSquaresBool_of_checkedLevelData hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and row-major checked raw-boundary
Figure 16 level data.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_level_data_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_raw_boundary_bool_position_source
      hchecked
      (canonicalRawBoundaryMacroSquaresBool_of_checkedLevelData hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and row-major checked raw-boundary
Figure 16 level data.
-/
theorem domino_problem_undecidable_l2c2_checked_level_data_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_raw_boundary_bool_position_source
      hchecked
      (canonicalRawBoundaryMacroSquaresBool_of_checkedLevelData hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks, row-major checked raw-boundary
Figure 16 level data, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_level_data_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_level_data_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks, row-major checked raw-boundary
Figure 16 level data, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c1_checked_level_data_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_level_data_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks, row-major checked raw-boundary
Figure 16 level data, and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_level_data_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_level_data_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks, row-major checked raw-boundary
Figure 16 level data, and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_checked_level_data_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_level_data_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRows hinterior hcorrect)

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
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1FreeSiteRectCanonicalCheckedCompatibleFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel).toL2C1CompatibleLevelObligations
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
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1FreeSiteRectCanonicalCheckedCompatibleFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel).toL2C1CompatibleLevelObligations
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
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2FreeSiteRectCanonicalCheckedCompatibleFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel).toL2C2CompatibleLevelObligations
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
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2FreeSiteRectCanonicalCheckedCompatibleFig16BundledObligations
        canonicalFreeSiteRectRouting hlevel).toL2C2CompatibleLevelObligations
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
Robinson Section 7 obstruction routing and source/free-grid level
certificates for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_level_certs_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryLevelCertificates)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
      section7Routing
      (canonicalRawBoundaryMacroSquares_of_levelCertificates hlevel) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and source/free-grid level
certificates for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_level_certs_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryLevelCertificates)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
      section7Routing
      (canonicalRawBoundaryMacroSquares_of_levelCertificates hlevel) h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and source/free-grid level
certificates for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_level_certs_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryLevelCertificates)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
      section7Routing
      (canonicalRawBoundaryMacroSquares_of_levelCertificates hlevel) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and source/free-grid level
certificates for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_level_certs_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryLevelCertificates)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
      section7Routing
      (canonicalRawBoundaryMacroSquares_of_levelCertificates hlevel) h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and explicit source/free-grid level
checks for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_level_checks_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_level_certs_position_source
      section7Routing
      (canonicalRawBoundaryLevelCertificates_of_levelChecks hlevel) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and explicit source/free-grid level
checks for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_level_checks_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_level_certs_position_source
      section7Routing
      (canonicalRawBoundaryLevelCertificates_of_levelChecks hlevel) h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and explicit source/free-grid level
checks for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_level_checks_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_level_certs_position_source
      section7Routing
      (canonicalRawBoundaryLevelCertificates_of_levelChecks hlevel) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and explicit source/free-grid level
checks for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_level_checks_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_level_certs_position_source
      section7Routing
      (canonicalRawBoundaryLevelCertificates_of_levelChecks hlevel) h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and row-major checked source/free-grid
level data for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_checked_rows_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_level_checks_position_source
      section7Routing
      (canonicalRawBoundaryLevelChecks_of_checkedLevelData hlevel) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and row-major checked source/free-grid
level data for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_checked_rows_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_level_checks_position_source
      section7Routing
      (canonicalRawBoundaryLevelChecks_of_checkedLevelData hlevel) h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and row-major checked source/free-grid
level data for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_checked_rows_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_level_checks_position_source
      section7Routing
      (canonicalRawBoundaryLevelChecks_of_checkedLevelData hlevel) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and row-major checked source/free-grid
level data for canonical raw-boundary Figure 16 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_checked_rows_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_level_checks_position_source
      section7Routing
      (canonicalRawBoundaryLevelChecks_of_checkedLevelData hlevel) h

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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1CompatibleLevelObligationsOfRobinsonSection7ObstructionData
        (l2c1RobinsonSection7ObstructionDataOfPositiveBoardLevelTileableSquares
          section7Routing
          (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)))
      h

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
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1CompatibleLevelObligationsOfRobinsonSection7ObstructionData
        (l2c1RobinsonSection7ObstructionDataOfPositiveBoardLevelTileableSquares
          section7Routing
          (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)))
      h

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
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2CompatibleLevelObligationsOfRobinsonSection7ObstructionData
        (l2c2RobinsonSection7ObstructionDataOfPositiveBoardLevelTileableSquares
          section7Routing
          (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)))
      h

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
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2CompatibleLevelObligationsOfRobinsonSection7ObstructionData
        (l2c2RobinsonSection7ObstructionDataOfPositiveBoardLevelTileableSquares
          section7Routing
          (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)))
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and shifted row-major checked
source/free-grid board levels.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_board_rows_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_position_source
      section7Routing
      (tilesPlane_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing and shifted row-major checked
source/free-grid board levels.
-/
theorem
    domino_problem_undecidable_l2c1_section7_raw_boundary_board_rows_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_fig13_tiles_plane_position_source
      section7Routing
      (tilesPlane_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and shifted row-major checked
source/free-grid board levels.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_board_rows_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_position_source
      section7Routing
      (tilesPlane_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing and shifted row-major checked
source/free-grid board levels.
-/
theorem
    domino_problem_undecidable_l2c2_section7_raw_boundary_board_rows_position_source
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_fig13_tiles_plane_position_source
      section7Routing
      (tilesPlane_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels hlevel)
      h

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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
Robinson's field-based Section 7 local signal tower and the raw Figure 13 plane
tiling to supply the translated board boxes.
-/
theorem encoded_domino_problem_undecidable_l2c1_signal_tower_fig13_plane_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations.ofL2C1Fig13TilesPlane
        htower hplane).toFigure18RoutedCertificate h

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using Robinson's field-based Section 7 local signal tower and the raw Figure 13
plane tiling to supply the translated board boxes.
-/
theorem domino_problem_undecidable_l2c1_signal_tower_fig13_plane_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations.ofL2C1Fig13TilesPlane
        htower hplane).toFigure18RoutedCertificate h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
Robinson's field-based Section 7 local signal tower and the raw Figure 13 plane
tiling to supply the translated board boxes.
-/
theorem encoded_domino_problem_undecidable_l2c2_signal_tower_fig13_plane_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations.ofL2C2Fig13TilesPlane
        htower hplane).toFigure18RoutedCertificate h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using Robinson's field-based Section 7 local signal tower and the raw Figure 13
plane tiling to supply the translated board boxes.
-/
theorem domino_problem_undecidable_l2c2_signal_tower_fig13_plane_position_source
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations.ofL2C2Fig13TilesPlane
        htower hplane).toFigure18RoutedCertificate h

/--
Encoded domino undecidability from the first audited L2-blank candidate via the
pair-free Robinson Section 7 signal-tower/translated-board-box obligation.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_direct_obligations_position_source
    (O : NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
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
the pair-free Robinson Section 7 signal-tower/translated-board-box obligation.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_direct_obligations_position_source
    (O : NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
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
the pair-free Robinson Section 7 signal-tower/translated-board-box obligation.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_direct_obligations_position_source
    (O : NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
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
the pair-free Robinson Section 7 signal-tower/translated-board-box obligation.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_direct_obligations_position_source
    (O : NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
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
Encoded domino undecidability from the first preferred field-based Section 7
package: a local signal tower and positive translated active-corner boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
    (data : L2C1SignalTowerTranslatedBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_direct_obligations_position_source
      (l2c1SignalTowerDirectObligationsOfTranslatedBoxData data) h

/--
Unencoded domino undecidability from the first preferred field-based Section 7
package: a local signal tower and positive translated active-corner boxes.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
    (data : L2C1SignalTowerTranslatedBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_direct_obligations_position_source
      (l2c1SignalTowerDirectObligationsOfTranslatedBoxData data) h

/--
Encoded domino undecidability from the second preferred field-based Section 7
package: a local signal tower and positive translated active-corner boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
    (data : L2C2SignalTowerTranslatedBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_direct_obligations_position_source
      (l2c2SignalTowerDirectObligationsOfTranslatedBoxData data) h

/--
Unencoded domino undecidability from the second preferred field-based Section 7
package: a local signal tower and positive translated active-corner boxes.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
    (data : L2C2SignalTowerTranslatedBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_direct_obligations_position_source
      (l2c2SignalTowerDirectObligationsOfTranslatedBoxData data) h

/--
Encoded domino undecidability from the first Section 7 board/free-line package
with translated active-corner boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
          data))
      h

/--
Unencoded domino undecidability from the first Section 7 board/free-line package
with translated active-corner boxes.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
          data))
      h

/--
Encoded domino undecidability from the second Section 7 board/free-line package
with translated active-corner boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
          data))
      h

/--
Unencoded domino undecidability from the second Section 7 board/free-line package
with translated active-corner boxes.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
          data))
      h

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and source-position obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_free_site_figure18_scaffold_tiles_plane_position_source
    (canonicalActiveCorner : L2C1CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      h

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and source-position obligations.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_free_site_figure18_scaffold_tiles_plane_position_source
    (canonicalActiveCorner : L2C1CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      h

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and source-position obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_position_source
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      h

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and source-position obligations.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_position_source
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      h

set_option linter.style.longLine false in
/--
Encoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and source-position
obligations for the first audited L2 candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stacks_figure18_scaffold_tiles_plane_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      h

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and source-position
obligations for the first audited L2 candidate.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stacks_figure18_scaffold_tiles_plane_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      h

set_option linter.style.longLine false in
/--
Encoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and source-position
obligations for the second audited L2 candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stacks_figure18_scaffold_tiles_plane_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      h

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and source-position
obligations for the second audited L2 candidate.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stacks_figure18_scaffold_tiles_plane_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      h

/--
Encoded domino undecidability from the first Section 7 board/free-line package
with centered positive active-corner boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
          data))
      h

/--
Unencoded domino undecidability from the first Section 7 board/free-line package
with centered positive active-corner boxes.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
          data))
      h

/--
Encoded domino undecidability from the second Section 7 board/free-line package
with centered positive active-corner boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
          data))
      h

/--
Unencoded domino undecidability from the second Section 7 board/free-line package
with centered positive active-corner boxes.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
          data))
      h

/- The translated-box and positive-box wrappers above intentionally build the
layer-patch data package before calling the generic Section 7 theorem. Keeping
the finite-check-facing obligation as the single proof path avoids maintaining
parallel Section 7 theorem surfaces.
-/

/--
Encoded domino undecidability from the first Section 7 board/free-line package
with finite active-corner layer patches.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        data)
      h

/--
Unencoded domino undecidability from the first Section 7 board/free-line package
with finite active-corner layer patches.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        data)
      h

/--
Encoded domino undecidability from the second Section 7 board/free-line package
with finite active-corner layer patches.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        data)
      h

/--
Unencoded domino undecidability from the second Section 7 board/free-line package
with finite active-corner layer patches.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        data)
      h

/--
Encoded domino undecidability from origin-zero active/corner windows plus finite
active-corner layer patches for the first audited L2-blank candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_layer_patches_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfOriginZeroWindowsLayerPatches
        originZeroWindows patches)
      h

/--
Unencoded domino undecidability from origin-zero active/corner windows plus
finite active-corner layer patches for the first audited L2-blank candidate.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_layer_patches_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfOriginZeroWindowsLayerPatches
        originZeroWindows patches)
      h

/--
Encoded domino undecidability from origin-zero active/corner windows plus finite
active-corner layer patches for the second audited L2-blank candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfOriginZeroWindowsLayerPatches
        originZeroWindows patches)
      h

/--
Unencoded domino undecidability from origin-zero active/corner windows plus
finite active-corner layer patches for the second audited L2-blank candidate.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfOriginZeroWindowsLayerPatches
        originZeroWindows patches)
      h

/--
Encoded domino undecidability from the first checked-stack/layer-patch finite
scaffold package and the direct source-level position obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    (data : L2C1CheckedStackLayerPatchData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
        data)
      h

/--
Unencoded domino undecidability from the first checked-stack/layer-patch finite
scaffold package and the direct source-level position obligations.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    (data : L2C1CheckedStackLayerPatchData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
        data)
      h

/--
Encoded domino undecidability from the second checked-stack/layer-patch finite
scaffold package and the direct source-level position obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    (data : L2C2CheckedStackLayerPatchData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
        data)
      h

/--
Unencoded domino undecidability from the second checked-stack/layer-patch finite
scaffold package and the direct source-level position obligations.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    (data : L2C2CheckedStackLayerPatchData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
        data)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows and canonical checked compatible Figure 16
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
      (l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows and canonical checked compatible Figure 16
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
      (l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows and canonical checked compatible Figure 16
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
      (l2c2CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows and canonical checked compatible Figure 16
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
      (l2c2CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows and row-major checked compatible Figure 16
level data.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_level_data_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_position_source
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows and row-major checked compatible Figure 16
level data.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_level_data_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_position_source
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows and row-major checked compatible Figure 16
level data.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_level_data_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_position_source
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows and row-major checked compatible Figure 16
level data.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_level_data_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_position_source
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      h

/--
Encoded domino undecidability from the first preferred field-based Section 7
package specialized to cofinal raw Figure 13 square tilings.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_fig13_cofinal_squares_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hsquares : Figure13CofinalTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfFig13CofinalSquares
        signalLocalTower hsquares)
      h

/--
Unencoded domino undecidability from the first preferred field-based Section 7
package specialized to cofinal raw Figure 13 square tilings.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_fig13_cofinal_squares_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hsquares : Figure13CofinalTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfFig13CofinalSquares
        signalLocalTower hsquares)
      h

/--
Encoded domino undecidability from the second preferred field-based Section 7
package specialized to cofinal raw Figure 13 square tilings.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_fig13_cofinal_squares_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hsquares : Figure13CofinalTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfFig13CofinalSquares
        signalLocalTower hsquares)
      h

/--
Unencoded domino undecidability from the second preferred field-based Section 7
package specialized to cofinal raw Figure 13 square tilings.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_fig13_cofinal_squares_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hsquares : Figure13CofinalTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfFig13CofinalSquares
        signalLocalTower hsquares)
      h

/--
Encoded domino undecidability from the first preferred field-based Section 7
package specialized to Robinson board-level aligned raw Figure 13
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_board_aligned_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfRobinsonBoardLevelAlignedMacroSquares
        signalLocalTower hlevel)
      h

/--
Unencoded domino undecidability from the first preferred field-based Section 7
package specialized to Robinson board-level aligned raw Figure 13
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_board_aligned_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfRobinsonBoardLevelAlignedMacroSquares
        signalLocalTower hlevel)
      h

/--
Encoded domino undecidability from the second preferred field-based Section 7
package specialized to Robinson board-level aligned raw Figure 13
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_board_aligned_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfRobinsonBoardLevelAlignedMacroSquares
        signalLocalTower hlevel)
      h

/--
Unencoded domino undecidability from the second preferred field-based Section 7
package specialized to Robinson board-level aligned raw Figure 13
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_board_aligned_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfRobinsonBoardLevelAlignedMacroSquares
        signalLocalTower hlevel)
      h

/--
Encoded domino undecidability from the first Robinson Section 7 scaffold
package: a local obstruction-signal tower and board-level aligned raw Figure 13
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_position_source
    (data : L2C1RobinsonSection7Data)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfRobinsonSection7Data data) h

/--
Unencoded domino undecidability from the first Robinson Section 7 scaffold
package: a local obstruction-signal tower and board-level aligned raw Figure 13
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_data_position_source
    (data : L2C1RobinsonSection7Data)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfRobinsonSection7Data data) h

/--
Encoded domino undecidability from the second Robinson Section 7 scaffold
package: a local obstruction-signal tower and board-level aligned raw Figure 13
macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_position_source
    (data : L2C2RobinsonSection7Data)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfRobinsonSection7Data data) h

/--
Unencoded domino undecidability from the second Robinson Section 7 scaffold
package: a local obstruction-signal tower and board-level aligned raw Figure 13
macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_data_position_source
    (data : L2C2RobinsonSection7Data)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfRobinsonSection7Data data) h

/--
Encoded domino undecidability from the first paper-facing Robinson Section 7
obstruction-routing package.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_position_source
    (data : L2C1RobinsonSection7ObstructionData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1CompatibleLevelObligationsOfRobinsonSection7ObstructionData data)
      h

/--
Unencoded domino undecidability from the first paper-facing Robinson Section 7
obstruction-routing package.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_position_source
    (data : L2C1RobinsonSection7ObstructionData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1CompatibleLevelObligationsOfRobinsonSection7ObstructionData data)
      h

/--
Encoded domino undecidability from the second paper-facing Robinson Section 7
obstruction-routing package.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_position_source
    (data : L2C2RobinsonSection7ObstructionData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2CompatibleLevelObligationsOfRobinsonSection7ObstructionData data)
      h

/--
Unencoded domino undecidability from the second paper-facing Robinson Section 7
obstruction-routing package.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_position_source
    (data : L2C2RobinsonSection7ObstructionData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2CompatibleLevelObligationsOfRobinsonSection7ObstructionData data)
      h

/--
Encoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      h

/--
Unencoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      h

/--
Encoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      h

/--
Unencoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      h

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and the source-specialized position-code label-index
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_sourceCode
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFrom hindex hcorrect)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and the source-specialized position-code label-index
decoder.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_sourceCode
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFrom hindex hcorrect)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and the source-specialized position-code label-index
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_sourceCode
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFrom hindex hcorrect)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and the source-specialized position-code label-index
decoder.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_sourceCode
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFrom hindex hcorrect)

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      (l2c1RobinsonSection7BoardFreeLineDataOfPositiveBoardLevelTileableSquares
        boardFreeLineActiveCorner hsquares)
      h

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      (l2c1RobinsonSection7BoardFreeLineDataOfPositiveBoardLevelTileableSquares
        boardFreeLineActiveCorner hsquares)
      h

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      (l2c2RobinsonSection7BoardFreeLineDataOfPositiveBoardLevelTileableSquares
        boardFreeLineActiveCorner hsquares)
      h

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      (l2c2RobinsonSection7BoardFreeLineDataOfPositiveBoardLevelTileableSquares
        boardFreeLineActiveCorner hsquares)
      h

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_tiles_plane_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      h

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_fig13_tiles_plane_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      h

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant and a raw Figure 13 plane tiling.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_tiles_plane_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      h

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant and a raw Figure 13 plane tiling.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_fig13_tiles_plane_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      h

/--
Encoded domino undecidability from the first active/corner recognition
obligation at canonical Robinson free crossings and exact positive board-level
raw Figure 13 square tilings.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_active_corner_pos_board_squares_position_source
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares h

/--
Unencoded domino undecidability from the first active/corner recognition
obligation at canonical Robinson free crossings and exact positive board-level
raw Figure 13 square tilings.
-/
theorem
    domino_problem_undecidable_l2c1_active_corner_pos_board_squares_position_source
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares h

/--
Encoded domino undecidability from the second active/corner recognition
obligation at canonical Robinson free crossings and exact positive board-level
raw Figure 13 square tilings.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_active_corner_pos_board_squares_position_source
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares h

/--
Unencoded domino undecidability from the second active/corner recognition
obligation at canonical Robinson free crossings and exact positive board-level
raw Figure 13 square tilings.
-/
theorem
    domino_problem_undecidable_l2c2_active_corner_pos_board_squares_position_source
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares h

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate and exact positive board-level raw Figure 13
square tilings.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_active_corner_pos_board_squares_position_source
      (l2c1ActiveCornerOfOriginZeroCheckedStacks hchecked) hsquares h

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate and exact positive board-level raw Figure 13
square tilings.
-/
theorem
    domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_active_corner_pos_board_squares_position_source
      (l2c1ActiveCornerOfOriginZeroCheckedStacks hchecked) hsquares h

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate and exact positive board-level raw Figure 13
square tilings.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_active_corner_pos_board_squares_position_source
      (l2c2ActiveCornerOfOriginZeroCheckedStacks hchecked) hsquares h

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate and exact positive board-level raw Figure 13
square tilings.
-/
theorem
    domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_active_corner_pos_board_squares_position_source
      (l2c2ActiveCornerOfOriginZeroCheckedStacks hchecked) hsquares h

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate and finite checked positive board-level raw
Figure 13 data.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_position_source
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) h

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate and finite checked positive board-level raw
Figure 13 data.
-/
theorem
    domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_position_source
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) h

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate and finite checked positive board-level raw
Figure 13 data.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_position_source
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) h

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate and finite checked positive board-level raw
Figure 13 data.
-/
theorem
    domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_position_source
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) h

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate and row-major checked raw-boundary board
levels.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_position_source
      hchecked
      (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels hlevel) h

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate and row-major checked raw-boundary board
levels.
-/
theorem
    domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_position_source
      hchecked
      (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels hlevel) h

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate and row-major checked raw-boundary board
levels.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_position_source
      hchecked
      (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels hlevel) h

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate and row-major checked raw-boundary board
levels.
-/
theorem
    domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_position_source
      hchecked
      (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels hlevel) h

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant and finite raw Figure 13 boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      (l2c1RobinsonSection7BoardFreeLineDataOfFig13TileableBoxes
        boardFreeLineActiveCorner hboxes)
      h

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant and finite raw Figure 13 boxes.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      (l2c1RobinsonSection7BoardFreeLineDataOfFig13TileableBoxes
        boardFreeLineActiveCorner hboxes)
      h

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant and finite raw Figure 13 boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      (l2c2RobinsonSection7BoardFreeLineDataOfFig13TileableBoxes
        boardFreeLineActiveCorner hboxes)
      h

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant and finite raw Figure 13 boxes.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_position_source
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      (l2c2RobinsonSection7BoardFreeLineDataOfFig13TileableBoxes
        boardFreeLineActiveCorner hboxes)
      h

/--
Encoded domino undecidability from the first paper-facing obstruction-routing
package, routed through the older signal-tower Section 7 theorem surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_obstruction_as_signal_tower_position_source
    (data : L2C1RobinsonSection7ObstructionData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_position_source
      (l2c1RobinsonSection7DataOfObstructionData data) h

/--
Unencoded domino undecidability from the first paper-facing obstruction-routing
package, routed through the older signal-tower Section 7 theorem surface.
-/
theorem
    domino_problem_undecidable_l2c1_section7_obstruction_as_signal_tower_position_source
    (data : L2C1RobinsonSection7ObstructionData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_data_position_source
      (l2c1RobinsonSection7DataOfObstructionData data) h

/--
Encoded domino undecidability from the second paper-facing obstruction-routing
package, routed through the older signal-tower Section 7 theorem surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_obstruction_as_signal_tower_position_source
    (data : L2C2RobinsonSection7ObstructionData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_position_source
      (l2c2RobinsonSection7DataOfObstructionData data) h

/--
Unencoded domino undecidability from the second paper-facing obstruction-routing
package, routed through the older signal-tower Section 7 theorem surface.
-/
theorem
    domino_problem_undecidable_l2c2_section7_obstruction_as_signal_tower_position_source
    (data : L2C2RobinsonSection7ObstructionData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_data_position_source
      (l2c2RobinsonSection7DataOfObstructionData data) h

/--
Encoded domino undecidability from the first preferred field-based Section 7
package specialized to canonical Figure 16 source raw-boundary macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_canonical_raw_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfCanonicalRawBoundary
        signalLocalTower hlevel)
      h

/--
Unencoded domino undecidability from the first preferred field-based Section 7
package specialized to canonical Figure 16 source raw-boundary macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_canonical_raw_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfCanonicalRawBoundary
        signalLocalTower hlevel)
      h

/--
Encoded domino undecidability from the second preferred field-based Section 7
package specialized to canonical Figure 16 source raw-boundary macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_canonical_raw_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfCanonicalRawBoundary
        signalLocalTower hlevel)
      h

/--
Unencoded domino undecidability from the second preferred field-based Section 7
package specialized to canonical Figure 16 source raw-boundary macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_canonical_raw_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfCanonicalRawBoundary
        signalLocalTower hlevel)
      h

/--
Encoded domino undecidability from the first preferred origin-zero/finite
Figure 13 box package.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_position_source
    (data : L2C1OriginZeroFig13BoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfOriginZeroFig13BoxData data) h

/--
Unencoded domino undecidability from the first preferred origin-zero/finite
Figure 13 box package.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_position_source
    (data : L2C1OriginZeroFig13BoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfOriginZeroFig13BoxData data) h

/--
Encoded domino undecidability from the second preferred origin-zero/finite
Figure 13 box package.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_position_source
    (data : L2C2OriginZeroFig13BoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfOriginZeroFig13BoxData data) h

/--
Unencoded domino undecidability from the second preferred origin-zero/finite
Figure 13 box package.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_position_source
    (data : L2C2OriginZeroFig13BoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfOriginZeroFig13BoxData data) h

/--
Encoded domino undecidability from first-component origin-zero recognizability
and Robinson board-level aligned raw Figure 13 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_board_aligned_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_position_source
      (l2c1RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c1SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      h

/--
Unencoded domino undecidability from first-component origin-zero recognizability
and Robinson board-level aligned raw Figure 13 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_board_aligned_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_data_position_source
      (l2c1RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c1SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      h

/--
Encoded domino undecidability from second-component origin-zero recognizability
and Robinson board-level aligned raw Figure 13 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_board_aligned_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_position_source
      (l2c2RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c2SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      h

/--
Unencoded domino undecidability from second-component origin-zero recognizability
and Robinson board-level aligned raw Figure 13 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_board_aligned_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_data_position_source
      (l2c2RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c2SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      h

/--
Encoded domino undecidability from first-component origin-zero recognizability
and positive Robinson board-level aligned raw Figure 13 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_position_source
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      h

/--
Unencoded domino undecidability from first-component origin-zero recognizability
and positive Robinson board-level aligned raw Figure 13 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_position_source
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      h

/--
Encoded domino undecidability from second-component origin-zero recognizability
and positive Robinson board-level aligned raw Figure 13 macro-squares.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_position_source
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      h

/--
Unencoded domino undecidability from second-component origin-zero recognizability
and positive Robinson board-level aligned raw Figure 13 macro-squares.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_position_source
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      h

/--
Encoded domino undecidability from first-component origin-zero recognizability
and exact checked positive board-level raw Figure 13 data.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_checked_pos_board_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_position_source
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      h

/--
Unencoded domino undecidability from first-component origin-zero recognizability
and exact checked positive board-level raw Figure 13 data.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_checked_pos_board_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_position_source
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      h

/--
Encoded domino undecidability from second-component origin-zero recognizability
and exact checked positive board-level raw Figure 13 data.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_pos_board_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_position_source
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      h

/--
Unencoded domino undecidability from second-component origin-zero recognizability
and exact checked positive board-level raw Figure 13 data.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_checked_pos_board_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_position_source
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      h

/--
Encoded domino undecidability from first-component origin-zero recognizability
and propositional positive board-level raw Figure 13 data.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_raw_pos_board_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelRaw)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_checked_pos_board_position_source
      originZeroWindows
      (checkedPositiveBoardLevels_of_rawPositiveBoardLevels hlevel)
      h

/--
Unencoded domino undecidability from first-component origin-zero recognizability
and propositional positive board-level raw Figure 13 data.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_raw_pos_board_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelRaw)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_checked_pos_board_position_source
      originZeroWindows
      (checkedPositiveBoardLevels_of_rawPositiveBoardLevels hlevel)
      h

/--
Encoded domino undecidability from second-component origin-zero recognizability
and propositional positive board-level raw Figure 13 data.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_raw_pos_board_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelRaw)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_pos_board_position_source
      originZeroWindows
      (checkedPositiveBoardLevels_of_rawPositiveBoardLevels hlevel)
      h

/--
Unencoded domino undecidability from second-component origin-zero recognizability
and propositional positive board-level raw Figure 13 data.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_raw_pos_board_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelRaw)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_checked_pos_board_position_source
      originZeroWindows
      (checkedPositiveBoardLevels_of_rawPositiveBoardLevels hlevel)
      h

/--
Encoded domino undecidability from first-component origin-zero recognizability
and exact positive board-level raw Figure 13 square tilings.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_pos_board_squares_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_position_source
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      h

/--
Unencoded domino undecidability from first-component origin-zero recognizability
and exact positive board-level raw Figure 13 square tilings.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_pos_board_squares_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_position_source
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      h

/--
Encoded domino undecidability from second-component origin-zero recognizability
and exact positive board-level raw Figure 13 square tilings.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_pos_board_squares_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_position_source
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      h

/--
Unencoded domino undecidability from second-component origin-zero recognizability
and exact positive board-level raw Figure 13 square tilings.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_pos_board_squares_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_position_source
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      h

/--
Encoded domino undecidability from first-component origin-zero recognizability
and row-major checked raw-boundary board levels.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_checked_board_levels_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_position_source
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      h

/--
Unencoded domino undecidability from first-component origin-zero recognizability
and row-major checked raw-boundary board levels.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_checked_board_levels_position_source
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_position_source
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      h

/--
Encoded domino undecidability from second-component origin-zero recognizability
and row-major checked raw-boundary board levels.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_position_source
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      h

/--
Unencoded domino undecidability from second-component origin-zero recognizability
and row-major checked raw-boundary board levels.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_position_source
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_position_source
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate via the
bundled Robinson Section 7 signal-tower/translated-board-box obligation.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_obligations_position_source
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toL2C1CompatibleLevelObligations h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the bundled Robinson Section 7 signal-tower/translated-board-box obligation.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_translated_obligations_position_source
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toL2C1CompatibleLevelObligations h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the bundled Robinson Section 7 signal-tower/translated-board-box obligation.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_obligations_position_source
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toL2C2CompatibleLevelObligations h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the bundled Robinson Section 7 signal-tower/translated-board-box obligation.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_translated_obligations_position_source
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toL2C2CompatibleLevelObligations h

/--
Encoded domino undecidability from the first audited L2-blank candidate through
the direct Robinson Section 7 board/free-line layer-patch package.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_layer_patch_obligations_position_source
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid O h

/--
Unencoded domino undecidability from the first audited L2-blank candidate
through the direct Robinson Section 7 board/free-line layer-patch package.
-/
theorem
    domino_problem_undecidable_l2c1_section7_layer_patch_obligations_position_source
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid O h

/--
Encoded domino undecidability from the second audited L2-blank candidate through
the direct Robinson Section 7 board/free-line layer-patch package.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_layer_patch_obligations_position_source
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid O h

/--
Unencoded domino undecidability from the second audited L2-blank candidate
through the direct Robinson Section 7 board/free-line layer-patch package.
-/
theorem
    domino_problem_undecidable_l2c2_section7_layer_patch_obligations_position_source
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid O h

/--
Encoded domino undecidability from the first audited L2-blank candidate through
canonical free-site-rectangle routing and positive translated boxes, routed via
the direct Section 7 board/free-line layer-patch package.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_section7_layer_patches_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_layer_patch_obligations_position_source
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfFreeSiteRectObligations
        O)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate
through canonical free-site-rectangle routing and positive translated boxes,
routed via the direct Section 7 board/free-line layer-patch package.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_section7_layer_patches_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_layer_patch_obligations_position_source
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfFreeSiteRectObligations
        O)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate through
canonical free-site-rectangle routing and positive translated boxes, routed via
the direct Section 7 board/free-line layer-patch package.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_section7_layer_patches_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_layer_patch_obligations_position_source
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfFreeSiteRectObligations
        O)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate
through canonical free-site-rectangle routing and positive translated boxes,
routed via the direct Section 7 board/free-line layer-patch package.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_section7_layer_patches_position_source
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_layer_patch_obligations_position_source
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfFreeSiteRectObligations
        O)
      h

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first audited L2-blank candidate through
the direct Robinson Section 7 board/free-line layer-patch package and
bounded-interior generated position-code rows at concrete numeric label slots.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_layer_patch_obligations_boundedRowsAtIndex
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_layer_patch_obligations_position_source
      O
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndex
        hbounded hcorrect)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first audited L2-blank candidate
through the direct Robinson Section 7 board/free-line layer-patch package and
bounded-interior generated position-code rows at concrete numeric label slots.
-/
theorem
    domino_problem_undecidable_l2c1_section7_layer_patch_obligations_boundedRowsAtIndex
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_layer_patch_obligations_position_source
      O
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndex
        hbounded hcorrect)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate
through the direct Robinson Section 7 board/free-line layer-patch package and
bounded-interior generated position-code rows at concrete numeric label slots.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_layer_patch_obligations_boundedRowsAtIndex
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_layer_patch_obligations_position_source
      O
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndex
        hbounded hcorrect)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate
through the direct Robinson Section 7 board/free-line layer-patch package and
bounded-interior generated position-code rows at concrete numeric label slots.
-/
theorem
    domino_problem_undecidable_l2c2_section7_layer_patch_obligations_boundedRowsAtIndex
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_layer_patch_obligations_position_source
      O
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndex
        hbounded hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows routed through the named Robinson Section 7
board/free-line layer-patch obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toSection7BoardFreeLineLayerPatchObligations h

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows routed through the named Robinson Section 7
board/free-line layer-patch obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toSection7BoardFreeLineLayerPatchObligations h

/--
Encoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows routed through the named Robinson Section 7
board/free-line layer-patch obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toSection7BoardFreeLineLayerPatchObligations h

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows routed through the named Robinson Section 7
board/free-line layer-patch obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toSection7BoardFreeLineLayerPatchObligations h

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toL2C1CompatibleLevelObligations h

/--
Unencoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toL2C1CompatibleLevelObligations h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toL2C2CompatibleLevelObligations h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows routed through the
signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_obligations_position_source
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_compatible_level_obligations_position_source
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toL2C2CompatibleLevelObligations h

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows and a raw Figure 13 plane tiling routed
through the signal-tower/translated-box obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_plane_position_source
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
    encoded_domino_problem_undecidable_l2c1_signal_tower_direct_obligations_position_source
      (l2c1OriginZeroSignalTowerFig13DirectObligations
        originZeroWindows hplane) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows and a raw Figure 13 plane tiling routed
through the signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_plane_position_source
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
    domino_problem_undecidable_l2c1_signal_tower_direct_obligations_position_source
      (l2c1OriginZeroSignalTowerFig13DirectObligations
        originZeroWindows hplane) h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows and a raw Figure 13 plane tiling routed
through the signal-tower/translated-box obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_plane_position_source
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
    encoded_domino_problem_undecidable_l2c2_signal_tower_direct_obligations_position_source
      (l2c2OriginZeroSignalTowerFig13DirectObligations
        originZeroWindows hplane) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows and a raw Figure 13 plane tiling routed
through the signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_plane_position_source
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
    domino_problem_undecidable_l2c2_signal_tower_direct_obligations_position_source
      (l2c2OriginZeroSignalTowerFig13DirectObligations
        originZeroWindows hplane) h

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows and finite Figure 13 boxes routed through the
signal-tower/translated-box obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_position_source
      (l2c1OriginZeroFig13BoxDataOfOriginZeroWindows
        originZeroWindows hboxes) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows and finite Figure 13 boxes routed
through the signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_position_source
      (l2c1OriginZeroFig13BoxDataOfOriginZeroWindows
        originZeroWindows hboxes) h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows and finite Figure 13 boxes routed through the
signal-tower/translated-box obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_position_source
      (l2c2OriginZeroFig13BoxDataOfOriginZeroWindows
        originZeroWindows hboxes) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows and finite Figure 13 boxes routed
through the signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_position_source
      (l2c2OriginZeroFig13BoxDataOfOriginZeroWindows
        originZeroWindows hboxes) h

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
finite origin-zero checked layer stacks and finite Figure 13 boxes routed
through the signal-tower/translated-box obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_position_source
      (l2c1OriginZeroFig13BoxDataOfCheckedStacks hchecked hboxes) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using finite origin-zero checked layer stacks and finite Figure 13 boxes routed
through the signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_position_source
      (l2c1OriginZeroFig13BoxDataOfCheckedStacks hchecked hboxes) h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
finite origin-zero checked layer stacks and finite Figure 13 boxes routed
through the signal-tower/translated-box obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_position_source
      (l2c2OriginZeroFig13BoxDataOfCheckedStacks hchecked hboxes) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using finite origin-zero checked layer stacks and finite Figure 13 boxes routed
through the signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hboxes : Figure13TileableBoxes)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_position_source
      (l2c2OriginZeroFig13BoxDataOfCheckedStacks hchecked hboxes) h

/--
Encoded domino undecidability from the first bundled checked signal-tower and
raw Figure 13 plane package.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_plane_data_position_source
    (data : L2C1CheckedSignalTowerFig13PlaneData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfCheckedFig13PlaneData data) h

/--
Unencoded domino undecidability from the first bundled checked signal-tower and
raw Figure 13 plane package.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_plane_data_position_source
    (data : L2C1CheckedSignalTowerFig13PlaneData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfCheckedFig13PlaneData data) h

/--
Encoded domino undecidability from the second bundled checked signal-tower and
raw Figure 13 plane package.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_plane_data_position_source
    (data : L2C2CheckedSignalTowerFig13PlaneData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfCheckedFig13PlaneData data) h

/--
Unencoded domino undecidability from the second bundled checked signal-tower and
raw Figure 13 plane package.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_plane_data_position_source
    (data : L2C2CheckedSignalTowerFig13PlaneData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfCheckedFig13PlaneData data) h

/--
Encoded domino undecidability from the first bundled checked signal-tower and
finite Figure 13 box package.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_box_data_position_source
    (data : L2C1CheckedSignalTowerFig13BoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfCheckedFig13BoxData data) h

/--
Unencoded domino undecidability from the first bundled checked signal-tower and
finite Figure 13 box package.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_box_data_position_source
    (data : L2C1CheckedSignalTowerFig13BoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      (l2c1SignalTowerTranslatedBoxDataOfCheckedFig13BoxData data) h

/--
Encoded domino undecidability from the second bundled checked signal-tower and
finite Figure 13 box package.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_box_data_position_source
    (data : L2C2CheckedSignalTowerFig13BoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfCheckedFig13BoxData data) h

/--
Unencoded domino undecidability from the second bundled checked signal-tower and
finite Figure 13 box package.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_box_data_position_source
    (data : L2C2CheckedSignalTowerFig13BoxData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      (l2c2SignalTowerTranslatedBoxDataOfCheckedFig13BoxData data) h

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
finite origin-zero checked layer stacks and shifted raw-boundary Figure 16
board checks routed through the signal-tower/translated-box obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_checks_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_position_source
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using finite origin-zero checked layer stacks and shifted raw-boundary Figure 16
board checks routed through the signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_checks_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_position_source
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
finite origin-zero checked layer stacks and shifted raw-boundary Figure 16
board checks routed through the signal-tower/translated-box obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_checks_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_position_source
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using finite origin-zero checked layer stacks and shifted raw-boundary Figure 16
board checks routed through the signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_checks_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_position_source
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
finite origin-zero checked layer stacks and row-major checked raw-boundary
Figure 16 board rows routed through the signal-tower/translated-box obligation
surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_rows_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_position_source
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using finite origin-zero checked layer stacks and row-major checked
raw-boundary Figure 16 board rows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_rows_position_source
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_position_source
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
finite origin-zero checked layer stacks and row-major checked raw-boundary
Figure 16 board rows routed through the signal-tower/translated-box obligation
surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_rows_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_position_source
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using finite origin-zero checked layer stacks and row-major checked
raw-boundary Figure 16 board rows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_rows_position_source
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_position_source
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
the finite checked signal-tower board package and source-position obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_board_data_position_source
    (data : L2C1CheckedSignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_direct_obligations_position_source
      (l2c1SignalTowerDirectObligationsOfCheckedBoardData data) h

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using the finite checked signal-tower board package and source-position
obligations.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_board_data_position_source
    (data : L2C1CheckedSignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_direct_obligations_position_source
      (l2c1SignalTowerDirectObligationsOfCheckedBoardData data) h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
the finite checked signal-tower board package and source-position obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_board_data_position_source
    (data : L2C2CheckedSignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_direct_obligations_position_source
      (l2c2SignalTowerDirectObligationsOfCheckedBoardData data) h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using the finite checked signal-tower board package and source-position
obligations.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_board_data_position_source
    (data : L2C2CheckedSignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_direct_obligations_position_source
      (l2c2SignalTowerDirectObligationsOfCheckedBoardData data) h

/--
Encoded domino undecidability from the first finite checked board package via
the proof-facing active/corner raw-board route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_board_data_active_corner_position_source
    (data : L2C1CheckedSignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_position_source
      data.checkedStacks data.boardLevels h

/--
Unencoded domino undecidability from the first finite checked board package via
the proof-facing active/corner raw-board route.
-/
theorem
    domino_problem_undecidable_l2c1_checked_board_data_active_corner_position_source
    (data : L2C1CheckedSignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_position_source
      data.checkedStacks data.boardLevels h

/--
Encoded domino undecidability from the second finite checked board package via
the proof-facing active/corner raw-board route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_board_data_active_corner_position_source
    (data : L2C2CheckedSignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_position_source
      data.checkedStacks data.boardLevels h

/--
Unencoded domino undecidability from the second finite checked board package via
the proof-facing active/corner raw-board route.
-/
theorem
    domino_problem_undecidable_l2c2_checked_board_data_active_corner_position_source
    (data : L2C2CheckedSignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_position_source
      data.checkedStacks data.boardLevels h

/--
Encoded domino undecidability from the first field-based Section 7 board
package and source-position obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_board_data_position_source
    (data : L2C1SignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_position_source
      (l2c1RobinsonSection7DataOfSignalTowerBoardData data)
      h

/--
Unencoded domino undecidability from the first field-based Section 7 board
package and source-position obligations.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_board_data_position_source
    (data : L2C1SignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_data_position_source
      (l2c1RobinsonSection7DataOfSignalTowerBoardData data)
      h

/--
Encoded domino undecidability from the second field-based Section 7 board
package and source-position obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_board_data_position_source
    (data : L2C2SignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_position_source
      (l2c2RobinsonSection7DataOfSignalTowerBoardData data)
      h

/--
Unencoded domino undecidability from the second field-based Section 7 board
package and source-position obligations.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_board_data_position_source
    (data : L2C2SignalTowerBoardData)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_data_position_source
      (l2c2RobinsonSection7DataOfSignalTowerBoardData data)
      h

/--
Encoded domino undecidability from the first field-based local signal tower,
explicit shifted board-level checks, and source-position obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_board_checks_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_position_source
      (l2c1RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      h

/--
Unencoded domino undecidability from the first field-based local signal tower,
explicit shifted board-level checks, and source-position obligations.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_board_checks_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_data_position_source
      (l2c1RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      h

/--
Encoded domino undecidability from the second field-based local signal tower,
explicit shifted board-level checks, and source-position obligations.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_board_checks_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_position_source
      (l2c2RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      h

/--
Unencoded domino undecidability from the second field-based local signal tower,
explicit shifted board-level checks, and source-position obligations.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_board_checks_position_source
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_data_position_source
      (l2c2RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows and shifted raw-boundary Figure 16 board
checks routed through finite Figure 13 boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_checks_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows and shifted raw-boundary Figure 16
board checks routed through finite Figure 13 boxes.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_checks_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows and shifted raw-boundary Figure 16 board
checks routed through finite Figure 13 boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_checks_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows and shifted raw-boundary Figure 16
board checks routed through finite Figure 13 boxes.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_checks_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      h

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows and row-major checked raw-boundary Figure 16
board rows routed through finite Figure 13 boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_rows_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      h

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows and row-major checked raw-boundary
Figure 16 board rows routed through finite Figure 13 boxes.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_rows_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      h

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows and row-major checked raw-boundary Figure 16
board rows routed through finite Figure 13 boxes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_rows_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      h

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows and row-major checked raw-boundary
Figure 16 board rows routed through finite Figure 13 boxes.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_rows_position_source
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
Encoded domino undecidability from the first audited L2-blank candidate, using
Robinson's field-based Section 7 local signal tower, the raw Figure 13 plane
tiling for translated board boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c1_signal_tower_fig13_plane_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations.ofL2C1Fig13TilesPlane
        htower hplane).toFigure18RoutedCertificate
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using Robinson's field-based Section 7 local signal tower, the raw Figure 13
plane tiling for translated board boxes, and generated interior position-code
rows.
-/
theorem domino_problem_undecidable_l2c1_signal_tower_fig13_plane_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations.ofL2C1Fig13TilesPlane
        htower hplane).toFigure18RoutedCertificate
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
Robinson's field-based Section 7 local signal tower, the raw Figure 13 plane
tiling for translated board boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_signal_tower_fig13_plane_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations.ofL2C2Fig13TilesPlane
        htower hplane).toFigure18RoutedCertificate
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using Robinson's field-based Section 7 local signal tower, the raw Figure 13
plane tiling for translated board boxes, and generated interior position-code
rows.
-/
theorem domino_problem_undecidable_l2c2_signal_tower_fig13_plane_interiorRows
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations.ofL2C2Fig13TilesPlane
        htower hplane).toFigure18RoutedCertificate
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via the
pair-free Robinson Section 7 signal-tower/translated-board-box obligation and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_direct_obligations_interiorRows
    (O : NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the pair-free Robinson Section 7 signal-tower/translated-board-box obligation
and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_direct_obligations_interiorRows
    (O : NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the pair-free Robinson Section 7 signal-tower/translated-board-box obligation
and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_direct_obligations_interiorRows
    (O : NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_routed_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the pair-free Robinson Section 7 signal-tower/translated-board-box obligation
and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_direct_obligations_interiorRows
    (O : NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_routed_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toFigure18RoutedCertificate hinterior hcorrect

/--
Encoded domino undecidability from the first preferred field-based Section 7
package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
    (data : L2C1SignalTowerTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_direct_obligations_interiorRows
      (l2c1SignalTowerDirectObligationsOfTranslatedBoxData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first preferred field-based Section 7
package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
    (data : L2C1SignalTowerTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_direct_obligations_interiorRows
      (l2c1SignalTowerDirectObligationsOfTranslatedBoxData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second preferred field-based Section 7
package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
    (data : L2C2SignalTowerTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_direct_obligations_interiorRows
      (l2c2SignalTowerDirectObligationsOfTranslatedBoxData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second preferred field-based Section 7
package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
    (data : L2C2SignalTowerTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_direct_obligations_interiorRows
      (l2c2SignalTowerDirectObligationsOfTranslatedBoxData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the first Robinson Section 7 scaffold
package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_interiorRows
    (data : L2C1RobinsonSection7Data)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
      (l2c1SignalTowerTranslatedBoxDataOfRobinsonSection7Data data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first Robinson Section 7 scaffold
package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_data_interiorRows
    (data : L2C1RobinsonSection7Data)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
      (l2c1SignalTowerTranslatedBoxDataOfRobinsonSection7Data data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second Robinson Section 7 scaffold
package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_interiorRows
    (data : L2C2RobinsonSection7Data)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
      (l2c2SignalTowerTranslatedBoxDataOfRobinsonSection7Data data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second Robinson Section 7 scaffold
package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_data_interiorRows
    (data : L2C2RobinsonSection7Data)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
      (l2c2SignalTowerTranslatedBoxDataOfRobinsonSection7Data data)
      hinterior hcorrect

/--
Encoded domino undecidability from the first paper-facing Robinson Section 7
obstruction-routing package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorRows
    (data : L2C1RobinsonSection7ObstructionData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      (l2c1CompatibleLevelObligationsOfRobinsonSection7ObstructionData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first paper-facing Robinson Section 7
obstruction-routing package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorRows
    (data : L2C1RobinsonSection7ObstructionData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      (l2c1CompatibleLevelObligationsOfRobinsonSection7ObstructionData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second paper-facing Robinson Section 7
obstruction-routing package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorRows
    (data : L2C2RobinsonSection7ObstructionData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      (l2c2CompatibleLevelObligationsOfRobinsonSection7ObstructionData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second paper-facing Robinson Section 7
obstruction-routing package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorRows
    (data : L2C2RobinsonSection7ObstructionData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      (l2c2CompatibleLevelObligationsOfRobinsonSection7ObstructionData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorRows
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorRows
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorRows
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorRows
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      hinterior hcorrect

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and bounded-interior generated position-code rows at
concrete numeric label slots.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_boundedRowsAtIndex
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_layer_patch_obligations_boundedRowsAtIndex
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      hbounded hcorrect

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and bounded-interior generated position-code rows at
concrete numeric label slots.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_boundedRowsAtIndex
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_layer_patch_obligations_boundedRowsAtIndex
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      hbounded hcorrect

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and bounded-interior generated position-code rows at
concrete numeric label slots.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_boundedRowsAtIndex
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_layer_patch_obligations_boundedRowsAtIndex
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      hbounded hcorrect

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and bounded-interior generated position-code rows at
concrete numeric label slots.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_boundedRowsAtIndex
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_layer_patch_obligations_boundedRowsAtIndex
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfBoardFreeLineData data)
      hbounded hcorrect

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant, exact positive board-level raw Figure 13 square tilings, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorRows
      (l2c1RobinsonSection7BoardFreeLineDataOfPositiveBoardLevelTileableSquares
        boardFreeLineActiveCorner hsquares)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant, exact positive board-level raw Figure 13 square tilings, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorRows
      (l2c1RobinsonSection7BoardFreeLineDataOfPositiveBoardLevelTileableSquares
        boardFreeLineActiveCorner hsquares)
      hinterior hcorrect

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant, exact positive board-level raw Figure 13 square tilings, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorRows
      (l2c2RobinsonSection7BoardFreeLineDataOfPositiveBoardLevelTileableSquares
        boardFreeLineActiveCorner hsquares)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant, exact positive board-level raw Figure 13 square tilings, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorRows
      (l2c2RobinsonSection7BoardFreeLineDataOfPositiveBoardLevelTileableSquares
        boardFreeLineActiveCorner hsquares)
      hinterior hcorrect

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant, a raw Figure 13 plane tiling, and generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_tiles_plane_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRows
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant, a raw Figure 13 plane tiling, and generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_fig13_tiles_plane_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRows
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior hcorrect

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant, a raw Figure 13 plane tiling, and generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_tiles_plane_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRows
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant, a raw Figure 13 plane tiling, and generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_fig13_tiles_plane_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRows
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior hcorrect

/--
Encoded domino undecidability from the first active/corner recognition
obligation at canonical Robinson free crossings, exact positive board-level
raw Figure 13 square tilings, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_active_corner_pos_board_squares_interiorRows
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRows
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares hinterior hcorrect

/--
Unencoded domino undecidability from the first active/corner recognition
obligation at canonical Robinson free crossings, exact positive board-level
raw Figure 13 square tilings, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_active_corner_pos_board_squares_interiorRows
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRows
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares hinterior hcorrect

/--
Encoded domino undecidability from the second active/corner recognition
obligation at canonical Robinson free crossings, exact positive board-level
raw Figure 13 square tilings, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_active_corner_pos_board_squares_interiorRows
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRows
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares hinterior hcorrect

/--
Unencoded domino undecidability from the second active/corner recognition
obligation at canonical Robinson free crossings, exact positive board-level
raw Figure 13 square tilings, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_active_corner_pos_board_squares_interiorRows
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRows
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, exact positive board-level raw Figure 13
square tilings, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_active_corner_pos_board_squares_interiorRows
      (l2c1ActiveCornerOfOriginZeroCheckedStacks hchecked)
      hsquares hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, exact positive board-level raw Figure 13
square tilings, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_active_corner_pos_board_squares_interiorRows
      (l2c1ActiveCornerOfOriginZeroCheckedStacks hchecked)
      hsquares hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, exact positive board-level raw Figure 13
square tilings, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_active_corner_pos_board_squares_interiorRows
      (l2c2ActiveCornerOfOriginZeroCheckedStacks hchecked)
      hsquares hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, exact positive board-level raw Figure 13
square tilings, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_active_corner_pos_board_squares_interiorRows
      (l2c2ActiveCornerOfOriginZeroCheckedStacks hchecked)
      hsquares hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, finite checked positive board-level raw
Figure 13 data, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_interiorRows
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, finite checked positive board-level raw
Figure 13 data, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_interiorRows
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, finite checked positive board-level raw
Figure 13 data, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_interiorRows
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, finite checked positive board-level raw
Figure 13 data, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_interiorRows
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, row-major checked raw-boundary board levels,
and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_interiorRows
      hchecked (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels
        hlevel) hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, row-major checked raw-boundary board levels,
and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_interiorRows
      hchecked (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels
        hlevel) hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, row-major checked raw-boundary board levels,
and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_interiorRows
      hchecked (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels
        hlevel) hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, row-major checked raw-boundary board levels,
and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_interiorRows
      hchecked (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels
        hlevel) hinterior hcorrect

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant, finite raw Figure 13 boxes, and generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorRows
      (l2c1RobinsonSection7BoardFreeLineDataOfFig13TileableBoxes
        boardFreeLineActiveCorner hboxes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant, finite raw Figure 13 boxes, and generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorRows
      (l2c1RobinsonSection7BoardFreeLineDataOfFig13TileableBoxes
        boardFreeLineActiveCorner hboxes)
      hinterior hcorrect

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant, finite raw Figure 13 boxes, and generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorRows
      (l2c2RobinsonSection7BoardFreeLineDataOfFig13TileableBoxes
        boardFreeLineActiveCorner hboxes)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant, finite raw Figure 13 boxes, and generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_interiorRows
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorRows
      (l2c2RobinsonSection7BoardFreeLineDataOfFig13TileableBoxes
        boardFreeLineActiveCorner hboxes)
      hinterior hcorrect

/--
Encoded domino undecidability from the first preferred field-based Section 7
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorPackage
    (data : L2C1SignalTowerTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first preferred field-based Section 7
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorPackage
    (data : L2C1SignalTowerTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second preferred field-based Section 7
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorPackage
    (data : L2C2SignalTowerTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second preferred field-based Section 7
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorPackage
    (data : L2C2SignalTowerTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorPackage
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorPackage
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorPackage
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorPackage
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and the packaged source-uniform generated interior
position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorPackage
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and the packaged source-uniform generated interior
position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorPackage
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and the packaged source-uniform generated interior
position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorPackage
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and the packaged source-uniform generated interior
position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorPackage
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from origin-zero active/corner windows, finite
active-corner layer patches, and the packaged source-uniform generated interior
position-code decoder for the first audited L2-blank candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_layer_patches_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from origin-zero active/corner windows, finite
active-corner layer patches, and the packaged source-uniform generated interior
position-code decoder for the first audited L2-blank candidate.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_layer_patches_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from origin-zero active/corner windows, finite
active-corner layer patches, and the packaged source-uniform generated interior
position-code decoder for the second audited L2-blank candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from origin-zero active/corner windows, finite
active-corner layer patches, and the packaged source-uniform generated interior
position-code decoder for the second audited L2-blank candidate.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_layer_patches_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first checked-stack/layer-patch finite
scaffold package and the packaged source-uniform generated interior position
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorPackage
    (data : L2C1CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first checked-stack/layer-patch finite
scaffold package and the packaged source-uniform generated interior position
decoder.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorPackage
    (data : L2C1CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second checked-stack/layer-patch finite
scaffold package and the packaged source-uniform generated interior position
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorPackage
    (data : L2C2CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second checked-stack/layer-patch finite
scaffold package and the packaged source-uniform generated interior position
decoder.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorPackage
    (data : L2C2CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows, canonical checked compatible Figure 16
macro-squares, and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorPackage
      (l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows, canonical checked compatible Figure 16
macro-squares, and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorPackage
      (l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, canonical checked compatible Figure 16
macro-squares, and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorPackage
      (l2c2CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, canonical checked compatible Figure 16
macro-squares, and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorPackage
      (l2c2CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows, checked compatible Figure 16 level data, and
the packaged source-uniform generated interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_level_data_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_interiorPackage
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows, checked compatible Figure 16 level data, and
the packaged source-uniform generated interior position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_level_data_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_interiorPackage
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, checked compatible Figure 16 level data, and
the packaged source-uniform generated interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_level_data_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_interiorPackage
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, checked compatible Figure 16 level data, and
the packaged source-uniform generated interior position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_level_data_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_interiorPackage
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first origin-zero Section 7
layer-patch obligation surface and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_interiorPackage
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first origin-zero Section 7
layer-patch obligation surface and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_interiorPackage
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second origin-zero Section 7
layer-patch obligation surface and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_interiorPackage
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second origin-zero Section 7
layer-patch obligation surface and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_interiorPackage
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first Robinson Section 7 scaffold
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_interiorPackage
    (data : L2C1RobinsonSection7Data)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorPackage
      (l2c1SignalTowerTranslatedBoxDataOfRobinsonSection7Data data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first Robinson Section 7 scaffold
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_data_interiorPackage
    (data : L2C1RobinsonSection7Data)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorPackage
      (l2c1SignalTowerTranslatedBoxDataOfRobinsonSection7Data data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second Robinson Section 7 scaffold
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_interiorPackage
    (data : L2C2RobinsonSection7Data)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorPackage
      (l2c2SignalTowerTranslatedBoxDataOfRobinsonSection7Data data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second Robinson Section 7 scaffold
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_data_interiorPackage
    (data : L2C2RobinsonSection7Data)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorPackage
      (l2c2SignalTowerTranslatedBoxDataOfRobinsonSection7Data data)
      hinterior hcorrect

/--
Encoded domino undecidability from the first paper-facing Robinson Section 7
obstruction-routing package and the packaged source-uniform generated interior
position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorPackage
    (data : L2C1RobinsonSection7ObstructionData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first paper-facing Robinson Section 7
obstruction-routing package and the packaged source-uniform generated interior
position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorPackage
    (data : L2C1RobinsonSection7ObstructionData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second paper-facing Robinson Section 7
obstruction-routing package and the packaged source-uniform generated interior
position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorPackage
    (data : L2C2RobinsonSection7ObstructionData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second paper-facing Robinson Section 7
obstruction-routing package and the packaged source-uniform generated interior
position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorPackage
    (data : L2C2RobinsonSection7ObstructionData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first preferred field-based Section 7
package specialized to cofinal raw Figure 13 square tilings and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_fig13_cofinal_squares_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hsquares : Figure13CofinalTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
      (l2c1SignalTowerTranslatedBoxDataOfFig13CofinalSquares
        signalLocalTower hsquares)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first preferred field-based Section 7
package specialized to cofinal raw Figure 13 square tilings and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_fig13_cofinal_squares_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hsquares : Figure13CofinalTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
      (l2c1SignalTowerTranslatedBoxDataOfFig13CofinalSquares
        signalLocalTower hsquares)
      hinterior hcorrect

/--
Encoded domino undecidability from the second preferred field-based Section 7
package specialized to cofinal raw Figure 13 square tilings and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_fig13_cofinal_squares_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hsquares : Figure13CofinalTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
      (l2c2SignalTowerTranslatedBoxDataOfFig13CofinalSquares
        signalLocalTower hsquares)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second preferred field-based Section 7
package specialized to cofinal raw Figure 13 square tilings and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_fig13_cofinal_squares_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hsquares : Figure13CofinalTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
      (l2c2SignalTowerTranslatedBoxDataOfFig13CofinalSquares
        signalLocalTower hsquares)
      hinterior hcorrect

/--
Encoded domino undecidability from the first preferred field-based Section 7
package specialized to Robinson board-level aligned raw Figure 13
macro-squares and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_board_aligned_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
      (l2c1SignalTowerTranslatedBoxDataOfRobinsonBoardLevelAlignedMacroSquares
        signalLocalTower hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first preferred field-based Section 7
package specialized to Robinson board-level aligned raw Figure 13
macro-squares and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_board_aligned_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
      (l2c1SignalTowerTranslatedBoxDataOfRobinsonBoardLevelAlignedMacroSquares
        signalLocalTower hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second preferred field-based Section 7
package specialized to Robinson board-level aligned raw Figure 13
macro-squares and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_board_aligned_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
      (l2c2SignalTowerTranslatedBoxDataOfRobinsonBoardLevelAlignedMacroSquares
        signalLocalTower hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second preferred field-based Section 7
package specialized to Robinson board-level aligned raw Figure 13
macro-squares and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_board_aligned_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
      (l2c2SignalTowerTranslatedBoxDataOfRobinsonBoardLevelAlignedMacroSquares
        signalLocalTower hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first preferred field-based Section 7
package specialized to canonical Figure 16 source raw-boundary macro-squares
and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_canonical_raw_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
      (l2c1SignalTowerTranslatedBoxDataOfCanonicalRawBoundary
        signalLocalTower hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first preferred field-based Section 7
package specialized to canonical Figure 16 source raw-boundary macro-squares
and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_canonical_raw_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
      (l2c1SignalTowerTranslatedBoxDataOfCanonicalRawBoundary
        signalLocalTower hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second preferred field-based Section 7
package specialized to canonical Figure 16 source raw-boundary macro-squares
and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_canonical_raw_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
      (l2c2SignalTowerTranslatedBoxDataOfCanonicalRawBoundary
        signalLocalTower hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second preferred field-based Section 7
package specialized to canonical Figure 16 source raw-boundary macro-squares
and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_canonical_raw_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
      (l2c2SignalTowerTranslatedBoxDataOfCanonicalRawBoundary
        signalLocalTower hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first preferred origin-zero/finite
Figure 13 box package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_interiorRows
    (data : L2C1OriginZeroFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
      (l2c1SignalTowerTranslatedBoxDataOfOriginZeroFig13BoxData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first preferred origin-zero/finite
Figure 13 box package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_interiorRows
    (data : L2C1OriginZeroFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRows
      (l2c1SignalTowerTranslatedBoxDataOfOriginZeroFig13BoxData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second preferred origin-zero/finite
Figure 13 box package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_interiorRows
    (data : L2C2OriginZeroFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
      (l2c2SignalTowerTranslatedBoxDataOfOriginZeroFig13BoxData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second preferred origin-zero/finite
Figure 13 box package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_interiorRows
    (data : L2C2OriginZeroFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRows
      (l2c2SignalTowerTranslatedBoxDataOfOriginZeroFig13BoxData data)
      hinterior hcorrect

/--
Encoded domino undecidability from first-component origin-zero recognizability,
Robinson board-level aligned raw Figure 13 macro-squares, and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_board_aligned_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_interiorRows
      (l2c1RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c1SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from first-component origin-zero recognizability,
Robinson board-level aligned raw Figure 13 macro-squares, and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_board_aligned_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_data_interiorRows
      (l2c1RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c1SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from second-component origin-zero recognizability,
Robinson board-level aligned raw Figure 13 macro-squares, and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_board_aligned_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_interiorRows
      (l2c2RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c2SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from second-component origin-zero recognizability,
Robinson board-level aligned raw Figure 13 macro-squares, and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_board_aligned_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_data_interiorRows
      (l2c2RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c2SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from first-component origin-zero recognizability,
positive Robinson board-level aligned raw Figure 13 macro-squares, and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorRows
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from first-component origin-zero recognizability,
positive Robinson board-level aligned raw Figure 13 macro-squares, and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorRows
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from second-component origin-zero recognizability,
positive Robinson board-level aligned raw Figure 13 macro-squares, and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorRows
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from second-component origin-zero recognizability,
positive Robinson board-level aligned raw Figure 13 macro-squares, and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorRows
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from first-component origin-zero recognizability,
exact checked positive board-level raw Figure 13 data, and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_checked_pos_board_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_interiorRows
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from first-component origin-zero recognizability,
exact checked positive board-level raw Figure 13 data, and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_checked_pos_board_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_interiorRows
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from second-component origin-zero recognizability,
exact checked positive board-level raw Figure 13 data, and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_pos_board_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_interiorRows
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from second-component origin-zero recognizability,
exact checked positive board-level raw Figure 13 data, and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_checked_pos_board_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_interiorRows
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from first-component origin-zero recognizability,
exact positive board-level raw Figure 13 square tilings, and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_pos_board_squares_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorRows
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      hinterior hcorrect

/--
Unencoded domino undecidability from first-component origin-zero recognizability,
exact positive board-level raw Figure 13 square tilings, and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_pos_board_squares_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorRows
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      hinterior hcorrect

/--
Encoded domino undecidability from second-component origin-zero recognizability,
exact positive board-level raw Figure 13 square tilings, and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_pos_board_squares_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorRows
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      hinterior hcorrect

/--
Unencoded domino undecidability from second-component origin-zero recognizability,
exact positive board-level raw Figure 13 square tilings, and generated
interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_pos_board_squares_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorRows
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      hinterior hcorrect

/--
Encoded domino undecidability from first-component origin-zero recognizability,
row-major checked raw-boundary board levels, and generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_checked_board_levels_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorRows
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from first-component origin-zero recognizability,
row-major checked raw-boundary board levels, and generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_checked_board_levels_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorRows
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from second-component origin-zero recognizability,
row-major checked raw-boundary board levels, and generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorRows
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from second-component origin-zero recognizability,
row-major checked raw-boundary board levels, and generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorRows
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from first-component origin-zero recognizability,
Robinson board-level aligned raw Figure 13 macro-squares, and the packaged
generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_board_aligned_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_interiorPackage
      (l2c1RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c1SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from first-component origin-zero recognizability,
Robinson board-level aligned raw Figure 13 macro-squares, and the packaged
generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_board_aligned_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_data_interiorPackage
      (l2c1RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c1SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from second-component origin-zero recognizability,
Robinson board-level aligned raw Figure 13 macro-squares, and the packaged
generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_board_aligned_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_interiorPackage
      (l2c2RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c2SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from second-component origin-zero recognizability,
Robinson board-level aligned raw Figure 13 macro-squares, and the packaged
generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_board_aligned_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_data_interiorPackage
      (l2c2RobinsonSection7DataOfRobinsonBoardLevelAlignedMacroSquares
        (l2c2SignalTowerOfOriginZeroWindows originZeroWindows) hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from first-component origin-zero recognizability,
positive Robinson board-level aligned raw Figure 13 macro-squares, and the
packaged generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorPackage
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from first-component origin-zero recognizability,
positive Robinson board-level aligned raw Figure 13 macro-squares, and the
packaged generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorPackage
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from second-component origin-zero recognizability,
positive Robinson board-level aligned raw Figure 13 macro-squares, and the
packaged generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorPackage
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from second-component origin-zero recognizability,
positive Robinson board-level aligned raw Figure 13 macro-squares, and the
packaged generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorPackage
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelAlignedMacroSquares
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from first-component origin-zero recognizability,
exact checked positive board-level raw Figure 13 data, and the packaged
generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_checked_pos_board_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_interiorPackage
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from first-component origin-zero recognizability,
exact checked positive board-level raw Figure 13 data, and the packaged
generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_checked_pos_board_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_positive_board_aligned_interiorPackage
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from second-component origin-zero recognizability,
exact checked positive board-level raw Figure 13 data, and the packaged
generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_pos_board_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_interiorPackage
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from second-component origin-zero recognizability,
exact checked positive board-level raw Figure 13 data, and the packaged
generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_checked_pos_board_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_positive_board_aligned_interiorPackage
      originZeroWindows
      (robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevels
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from first-component origin-zero recognizability,
exact positive board-level raw Figure 13 square tilings, and the packaged
generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_pos_board_squares_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorPackage
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      hinterior hcorrect

/--
Unencoded domino undecidability from first-component origin-zero recognizability,
exact positive board-level raw Figure 13 square tilings, and the packaged
generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_pos_board_squares_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorPackage
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      hinterior hcorrect

/--
Encoded domino undecidability from second-component origin-zero recognizability,
exact positive board-level raw Figure 13 square tilings, and the packaged
generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_pos_board_squares_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorPackage
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      hinterior hcorrect

/--
Unencoded domino undecidability from second-component origin-zero recognizability,
exact positive board-level raw Figure 13 square tilings, and the packaged
generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_pos_board_squares_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorPackage
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsPositiveBoardLevelTileableSquares
        originZeroWindows hsquares)
      hinterior hcorrect

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant, exact positive board-level raw Figure 13 square tilings, and the
packaged generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant, exact positive board-level raw Figure 13 square tilings, and the
packaged generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant, exact positive board-level raw Figure 13 square tilings, and the
packaged generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant, exact positive board-level raw Figure 13 square tilings, and the
packaged generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant, a raw Figure 13 plane tiling, and the packaged generated interior
position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_tiles_plane_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorPackage
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant, a raw Figure 13 plane tiling, and the packaged generated interior
position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_fig13_tiles_plane_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorPackage
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior hcorrect

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant, a raw Figure 13 plane tiling, and the packaged generated interior
position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_tiles_plane_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorPackage
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant, a raw Figure 13 plane tiling, and the packaged generated interior
position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_fig13_tiles_plane_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorPackage
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior hcorrect

/--
Encoded domino undecidability from the first active/corner recognition
obligation at canonical Robinson free crossings, exact positive board-level
raw Figure 13 square tilings, and the packaged generated interior position-code
source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_active_corner_pos_board_squares_interiorPackage
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorPackage
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares hinterior hcorrect

/--
Unencoded domino undecidability from the first active/corner recognition
obligation at canonical Robinson free crossings, exact positive board-level
raw Figure 13 square tilings, and the packaged generated interior position-code
source route.
-/
theorem
    domino_problem_undecidable_l2c1_active_corner_pos_board_squares_interiorPackage
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorPackage
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares hinterior hcorrect

/--
Encoded domino undecidability from the second active/corner recognition
obligation at canonical Robinson free crossings, exact positive board-level
raw Figure 13 square tilings, and the packaged generated interior position-code
source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_active_corner_pos_board_squares_interiorPackage
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorPackage
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares hinterior hcorrect

/--
Unencoded domino undecidability from the second active/corner recognition
obligation at canonical Robinson free crossings, exact positive board-level
raw Figure 13 square tilings, and the packaged generated interior position-code
source route.
-/
theorem
    domino_problem_undecidable_l2c2_active_corner_pos_board_squares_interiorPackage
    (activeCorner :
      Section7CanonicalFreeSiteRectActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorPackage
      (section7BoardFreeLineActiveCorner_of_activeCorner activeCorner)
      hsquares hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, exact positive board-level raw Figure 13
square tilings, and the packaged generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_interiorPackage
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_active_corner_pos_board_squares_interiorPackage
      (l2c1ActiveCornerOfOriginZeroCheckedStacks hchecked)
      hsquares hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, exact positive board-level raw Figure 13
square tilings, and the packaged generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_interiorPackage
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_active_corner_pos_board_squares_interiorPackage
      (l2c1ActiveCornerOfOriginZeroCheckedStacks hchecked)
      hsquares hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, exact positive board-level raw Figure 13
square tilings, and the packaged generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_interiorPackage
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_active_corner_pos_board_squares_interiorPackage
      (l2c2ActiveCornerOfOriginZeroCheckedStacks hchecked)
      hsquares hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, exact positive board-level raw Figure 13
square tilings, and the packaged generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_interiorPackage
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_active_corner_pos_board_squares_interiorPackage
      (l2c2ActiveCornerOfOriginZeroCheckedStacks hchecked)
      hsquares hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, finite checked positive board-level raw
Figure 13 data, and the packaged generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_interiorPackage
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_interiorPackage
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, finite checked positive board-level raw
Figure 13 data, and the packaged generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_interiorPackage
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_active_corner_pos_board_squares_interiorPackage
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, finite checked positive board-level raw
Figure 13 data, and the packaged generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_interiorPackage
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_interiorPackage
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, finite checked positive board-level raw
Figure 13 data, and the packaged generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_interiorPackage
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure13PositiveBoardLevelChecked)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_active_corner_pos_board_squares_interiorPackage
      hchecked (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevels
        hlevel) hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, row-major checked raw-boundary board levels,
and the packaged generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_interiorPackage
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_interiorPackage
      hchecked (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels
        hlevel) hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
first audited L2-blank candidate, row-major checked raw-boundary board levels,
and the packaged generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_interiorPackage
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_active_corner_checked_pos_board_interiorPackage
      hchecked (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels
        hlevel) hinterior hcorrect

/--
Encoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, row-major checked raw-boundary board levels,
and the packaged generated interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_interiorPackage
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_interiorPackage
      hchecked (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels
        hlevel) hinterior hcorrect

/--
Unencoded domino undecidability from finite origin-zero checked stacks for the
second audited L2-blank candidate, row-major checked raw-boundary board levels,
and the packaged generated interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_interiorPackage
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_active_corner_checked_pos_board_interiorPackage
      hchecked (checkedPositiveBoardLevels_of_rawBoundaryCheckedBoardLevels
        hlevel) hinterior hcorrect

/--
Encoded domino undecidability from the first finite checked board package via
the proof-facing active/corner raw-board route and the packaged source-uniform
generated interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_board_data_active_corner_interiorPackage
    (data : L2C1CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_interiorPackage
      data.checkedStacks data.boardLevels hinterior hcorrect

/--
Unencoded domino undecidability from the first finite checked board package via
the proof-facing active/corner raw-board route and the packaged source-uniform
generated interior position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c1_checked_board_data_active_corner_interiorPackage
    (data : L2C1CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_interiorPackage
      data.checkedStacks data.boardLevels hinterior hcorrect

/--
Encoded domino undecidability from the second finite checked board package via
the proof-facing active/corner raw-board route and the packaged source-uniform
generated interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_board_data_active_corner_interiorPackage
    (data : L2C2CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_interiorPackage
      data.checkedStacks data.boardLevels hinterior hcorrect

/--
Unencoded domino undecidability from the second finite checked board package via
the proof-facing active/corner raw-board route and the packaged source-uniform
generated interior position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c2_checked_board_data_active_corner_interiorPackage
    (data : L2C2CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_interiorPackage
      data.checkedStacks data.boardLevels hinterior hcorrect

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant, finite raw Figure 13 boxes, and the packaged generated interior
position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant, finite raw Figure 13 boxes, and the packaged generated interior
position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant, finite raw Figure 13 boxes, and the packaged generated interior
position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant, finite raw Figure 13 boxes, and the packaged generated interior
position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_interiorPackage
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from first-component origin-zero recognizability,
row-major checked raw-boundary board levels, and the packaged generated
interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_checked_board_levels_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorPackage
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from first-component origin-zero recognizability,
row-major checked raw-boundary board levels, and the packaged generated
interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_checked_board_levels_interiorPackage
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_obstruction_data_interiorPackage
      (l2c1RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from second-component origin-zero recognizability,
row-major checked raw-boundary board levels, and the packaged generated
interior position-code source route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorPackage
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from second-component origin-zero recognizability,
row-major checked raw-boundary board levels, and the packaged generated
interior position-code source route.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_interiorPackage
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_obstruction_data_interiorPackage
      (l2c2RobinsonSection7ObstructionDataOfOriginZeroWindowsCheckedBoardLevels
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first preferred origin-zero/finite
Figure 13 box package and the packaged generated interior position-code source
route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_interiorPackage
    (data : L2C1OriginZeroFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first preferred origin-zero/finite
Figure 13 box package and the packaged generated interior position-code source
route.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_interiorPackage
    (data : L2C1OriginZeroFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second preferred origin-zero/finite
Figure 13 box package and the packaged generated interior position-code source
route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_interiorPackage
    (data : L2C2OriginZeroFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second preferred origin-zero/finite
Figure 13 box package and the packaged generated interior position-code source
route.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_interiorPackage
    (data : L2C2OriginZeroFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate via the
bundled Robinson Section 7 signal-tower/translated-board-box obligation and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_obligations_interiorRows
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      O.toL2C1CompatibleLevelObligations hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the bundled Robinson Section 7 signal-tower/translated-board-box obligation and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_translated_obligations_interiorRows
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      O.toL2C1CompatibleLevelObligations hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the bundled Robinson Section 7 signal-tower/translated-board-box obligation and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_obligations_interiorRows
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      O.toL2C2CompatibleLevelObligations hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the bundled Robinson Section 7 signal-tower/translated-board-box obligation and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_translated_obligations_interiorRows
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      O.toL2C2CompatibleLevelObligations hinterior hcorrect

/--
Encoded domino undecidability from the first Section 7 board/free-line package
with translated active-corner boxes and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
          data))
      hinterior hcorrect

/--
Unencoded domino undecidability from the first Section 7 board/free-line package
with translated active-corner boxes and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
          data))
      hinterior hcorrect

/--
Encoded domino undecidability from the second Section 7 board/free-line package
with translated active-corner boxes and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_interiorRows
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
          data))
      hinterior hcorrect

/--
Unencoded domino undecidability from the second Section 7 board/free-line package
with translated active-corner boxes and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_interiorRows
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
          data))
      hinterior hcorrect

/--
Encoded domino undecidability from the first Section 7 board/free-line package
with centered positive active-corner boxes and generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
          data))
      hinterior hcorrect

/--
Unencoded domino undecidability from the first Section 7 board/free-line package
with centered positive active-corner boxes and generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
          data))
      hinterior hcorrect

/--
Encoded domino undecidability from the second Section 7 board/free-line package
with centered positive active-corner boxes and generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRows
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
          data))
      hinterior hcorrect

/--
Unencoded domino undecidability from the second Section 7 board/free-line package
with centered positive active-corner boxes and generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRows
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
          data))
      hinterior hcorrect

/--
Encoded domino undecidability from the first Section 7 board/free-line package
with finite active-corner layer patches and generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRows
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first Section 7 board/free-line package
with finite active-corner layer patches and generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRows
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second Section 7 board/free-line package
with finite active-corner layer patches and generated interior position-code
rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRows
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second Section 7 board/free-line package
with finite active-corner layer patches and generated interior position-code
rows.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRows
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfLayerPatchData
        data)
      hinterior hcorrect

/--
Encoded domino undecidability from origin-zero active/corner windows plus finite
active-corner layer patches and generated interior position-code rows for the
first audited L2-blank candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_layer_patches_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfOriginZeroWindowsLayerPatches
        originZeroWindows patches)
      hinterior hcorrect

/--
Unencoded domino undecidability from origin-zero active/corner windows plus
finite active-corner layer patches and generated interior position-code rows
for the first audited L2-blank candidate.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_layer_patches_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfOriginZeroWindowsLayerPatches
        originZeroWindows patches)
      hinterior hcorrect

/--
Encoded domino undecidability from origin-zero active/corner windows plus finite
active-corner layer patches and generated interior position-code rows for the
second audited L2-blank candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfOriginZeroWindowsLayerPatches
        originZeroWindows patches)
      hinterior hcorrect

/--
Unencoded domino undecidability from origin-zero active/corner windows plus
finite active-corner layer patches and generated interior position-code rows
for the second audited L2-blank candidate.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_layer_patches_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfOriginZeroWindowsLayerPatches
        originZeroWindows patches)
      hinterior hcorrect

/--
Encoded domino undecidability from the first checked-stack/layer-patch finite
scaffold package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRows
    (data : L2C1CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRows
      (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
        data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first checked-stack/layer-patch finite
scaffold package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRows
    (data : L2C1CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRows
      (l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
        data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second checked-stack/layer-patch finite
scaffold package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRows
    (data : L2C2CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRows
      (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
        data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second checked-stack/layer-patch finite
scaffold package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRows
    (data : L2C2CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRows
      (l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
        data)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows, canonical checked compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRows
      (l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows, canonical checked compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRows
      (l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, canonical checked compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRows
      (l2c2CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, canonical checked compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRows
      (l2c2CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
        originZeroWindows hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows, checked compatible Figure 16 level data, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_level_data_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_interiorRows
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate using
origin-zero active/corner windows, checked compatible Figure 16 level data, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_level_data_interiorRows
    (originZeroWindows : L2C1OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_interiorRows
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, checked compatible Figure 16 level data, and
generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_level_data_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_interiorRows
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, checked compatible Figure 16 level data, and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_level_data_interiorRows
    (originZeroWindows : L2C2OriginZeroWindows)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_compatible_fig16_interiorRows
      originZeroWindows
      (canonicalCheckedRecognizedCompatibleMacroSquares_of_checkedLevelData
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate through
the direct Robinson Section 7 board/free-line layer-patch package and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_layer_patch_obligations_interiorRows
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid O
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate
through the direct Robinson Section 7 board/free-line layer-patch package and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_section7_layer_patch_obligations_interiorRows
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid O
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate through
the direct Robinson Section 7 board/free-line layer-patch package and generated
interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_layer_patch_obligations_interiorRows
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid O
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate
through the direct Robinson Section 7 board/free-line layer-patch package and
generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_section7_layer_patch_obligations_interiorRows
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid O
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate through
canonical free-site-rectangle routing, positive translated boxes, and generated
interior position-code rows, routed via the direct Section 7 layer-patch
package.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_free_site_rect_section7_layer_patches_interiorRows
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_layer_patch_obligations_interiorRows
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfFreeSiteRectObligations
        O)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate
through canonical free-site-rectangle routing, positive translated boxes, and
generated interior position-code rows, routed via the direct Section 7
layer-patch package.
-/
theorem
    domino_problem_undecidable_l2c1_free_site_rect_section7_layer_patches_interiorRows
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_layer_patch_obligations_interiorRows
      (l2c1Section7BoardFreeLineLayerPatchObligationsOfFreeSiteRectObligations
        O)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate through
canonical free-site-rectangle routing, positive translated boxes, and generated
interior position-code rows, routed via the direct Section 7 layer-patch
package.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_free_site_rect_section7_layer_patches_interiorRows
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_layer_patch_obligations_interiorRows
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfFreeSiteRectObligations
        O)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate
through canonical free-site-rectangle routing, positive translated boxes, and
generated interior position-code rows, routed via the direct Section 7
layer-patch package.
-/
theorem
    domino_problem_undecidable_l2c2_free_site_rect_section7_layer_patches_interiorRows
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_layer_patch_obligations_interiorRows
      (l2c2Section7BoardFreeLineLayerPatchObligationsOfFreeSiteRectObligations
        O)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows, routed through the named Robinson Section 7
board/free-line layer-patch obligation surface and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toSection7BoardFreeLineLayerPatchObligations hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows, routed through the named Robinson Section 7
board/free-line layer-patch obligation surface and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      O.toSection7BoardFreeLineLayerPatchObligations hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows, routed through the named Robinson Section 7
board/free-line layer-patch obligation surface and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toSection7BoardFreeLineLayerPatchObligations hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows, routed through the named Robinson Section 7
board/free-line layer-patch obligation surface and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_section7_board_free_line_layer_patches_interiorRows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      O.toSection7BoardFreeLineLayerPatchObligations hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows routed through the signal-tower/translated-box
obligation surface and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_obligations_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      O.toL2C1CompatibleLevelObligations hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows routed through the
signal-tower/translated-box obligation surface and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_obligations_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      O.toL2C1CompatibleLevelObligations hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows routed through the signal-tower/translated-box
obligation surface and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_obligations_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      O.toL2C2CompatibleLevelObligations hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows routed through the
signal-tower/translated-box obligation surface and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_obligations_interiorRows
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
      O.toL2C2CompatibleLevelObligations hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows, a raw Figure 13 plane tiling, and generated
interior position-code rows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_plane_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_direct_obligations_interiorRows
      (l2c1OriginZeroSignalTowerFig13DirectObligations
        originZeroWindows hplane) hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows, a raw Figure 13 plane tiling, and
generated interior position-code rows routed through the
signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_plane_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_direct_obligations_interiorRows
      (l2c1OriginZeroSignalTowerFig13DirectObligations
        originZeroWindows hplane) hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows, a raw Figure 13 plane tiling, and generated
interior position-code rows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_plane_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_direct_obligations_interiorRows
      (l2c2OriginZeroSignalTowerFig13DirectObligations
        originZeroWindows hplane) hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows, a raw Figure 13 plane tiling, and
generated interior position-code rows routed through the
signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_plane_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_direct_obligations_interiorRows
      (l2c2OriginZeroSignalTowerFig13DirectObligations
        originZeroWindows hplane) hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows, finite Figure 13 boxes, and generated
interior position-code rows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_direct_obligations_interiorRows
      (l2c1OriginZeroSignalTowerFig13BoxDirectObligations
        originZeroWindows hboxes) hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows, finite Figure 13 boxes, and generated
interior position-code rows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_direct_obligations_interiorRows
      (l2c1OriginZeroSignalTowerFig13BoxDirectObligations
        originZeroWindows hboxes) hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows, finite Figure 13 boxes, and generated
interior position-code rows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_direct_obligations_interiorRows
      (l2c2OriginZeroSignalTowerFig13BoxDirectObligations
        originZeroWindows hboxes) hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows, finite Figure 13 boxes, and generated
interior position-code rows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_direct_obligations_interiorRows
      (l2c2OriginZeroSignalTowerFig13BoxDirectObligations
        originZeroWindows hboxes) hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows, finite Figure 13 boxes, and the packaged
source-uniform generated interior position-code decoder routed through the
signal-tower/translated-box obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows, finite Figure 13 boxes, and the
packaged source-uniform generated interior position-code decoder routed through
the signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows, finite Figure 13 boxes, and the packaged
source-uniform generated interior position-code decoder routed through the
signal-tower/translated-box obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows, finite Figure 13 boxes, and the
packaged source-uniform generated interior position-code decoder routed through
the signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_position_source
      originZeroWindows hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
finite origin-zero checked layer stacks, finite Figure 13 boxes, and generated
interior position-code rows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_position_source
      hchecked hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using finite origin-zero checked layer stacks, finite Figure 13 boxes, and
generated interior position-code rows routed through the
signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_position_source
      hchecked hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
finite origin-zero checked layer stacks, finite Figure 13 boxes, and generated
interior position-code rows routed through the signal-tower/translated-box
obligation surface.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_position_source
      hchecked hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using finite origin-zero checked layer stacks, finite Figure 13 boxes, and
generated interior position-code rows routed through the
signal-tower/translated-box obligation surface.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hboxes : Figure13TileableBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_position_source
      hchecked hboxes
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first bundled checked signal-tower and
raw Figure 13 plane package, with generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_plane_data_interiorRows
    (data : L2C1CheckedSignalTowerFig13PlaneData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_plane_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first bundled checked signal-tower and
raw Figure 13 plane package, with generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_plane_data_interiorRows
    (data : L2C1CheckedSignalTowerFig13PlaneData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_plane_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second bundled checked signal-tower and
raw Figure 13 plane package, with generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_plane_data_interiorRows
    (data : L2C2CheckedSignalTowerFig13PlaneData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_plane_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second bundled checked signal-tower and
raw Figure 13 plane package, with generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_plane_data_interiorRows
    (data : L2C2CheckedSignalTowerFig13PlaneData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_plane_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first bundled checked signal-tower and
finite Figure 13 box package, with generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_box_data_interiorRows
    (data : L2C1CheckedSignalTowerFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the first bundled checked signal-tower and
finite Figure 13 box package, with generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_box_data_interiorRows
    (data : L2C1CheckedSignalTowerFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the second bundled checked signal-tower and
finite Figure 13 box package, with generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_box_data_interiorRows
    (data : L2C2CheckedSignalTowerFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Unencoded domino undecidability from the second bundled checked signal-tower and
finite Figure 13 box package, with generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_box_data_interiorRows
    (data : L2C2CheckedSignalTowerFig13BoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRows
        hinterior hcorrect)

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
finite origin-zero checked layer stacks, shifted raw-boundary Figure 16 board
checks, and generated interior position-code rows through the signal-tower
route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_checks_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_interiorRows
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using finite origin-zero checked layer stacks, shifted raw-boundary Figure 16
board checks, and generated interior position-code rows through the
signal-tower route.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_checks_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_interiorRows
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
finite origin-zero checked layer stacks, shifted raw-boundary Figure 16 board
checks, and generated interior position-code rows through the signal-tower
route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_checks_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_interiorRows
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using finite origin-zero checked layer stacks, shifted raw-boundary Figure 16
board checks, and generated interior position-code rows through the
signal-tower route.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_checks_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_interiorRows
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
finite origin-zero checked layer stacks, row-major checked raw-boundary Figure
16 board rows, and generated interior position-code rows through the
signal-tower route.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_rows_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_interiorRows
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using finite origin-zero checked layer stacks, row-major checked raw-boundary
Figure 16 board rows, and generated interior position-code rows through the
signal-tower route.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_rows_interiorRows
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_boxes_interiorRows
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
finite origin-zero checked layer stacks, row-major checked raw-boundary Figure
16 board rows, and generated interior position-code rows through the
signal-tower route.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_rows_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_interiorRows
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using finite origin-zero checked layer stacks, row-major checked raw-boundary
Figure 16 board rows, and generated interior position-code rows through the
signal-tower route.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_rows_interiorRows
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_boxes_interiorRows
      hchecked
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
the finite checked signal-tower board package and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_board_data_interiorRows
    (data : L2C1CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_direct_obligations_interiorRows
      (l2c1SignalTowerDirectObligationsOfCheckedBoardData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using the finite checked signal-tower board package and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_board_data_interiorRows
    (data : L2C1CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_direct_obligations_interiorRows
      (l2c1SignalTowerDirectObligationsOfCheckedBoardData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
the finite checked signal-tower board package and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_board_data_interiorRows
    (data : L2C2CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_direct_obligations_interiorRows
      (l2c2SignalTowerDirectObligationsOfCheckedBoardData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using the finite checked signal-tower board package and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_board_data_interiorRows
    (data : L2C2CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_direct_obligations_interiorRows
      (l2c2SignalTowerDirectObligationsOfCheckedBoardData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the first finite checked board package via
the proof-facing active/corner raw-board route and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_board_data_active_corner_interiorRows
    (data : L2C1CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_interiorRows
      data.checkedStacks data.boardLevels hinterior hcorrect

/--
Unencoded domino undecidability from the first finite checked board package via
the proof-facing active/corner raw-board route and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_checked_board_data_active_corner_interiorRows
    (data : L2C1CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_active_corner_raw_boards_interiorRows
      data.checkedStacks data.boardLevels hinterior hcorrect

/--
Encoded domino undecidability from the second finite checked board package via
the proof-facing active/corner raw-board route and generated interior
position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_board_data_active_corner_interiorRows
    (data : L2C2CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_interiorRows
      data.checkedStacks data.boardLevels hinterior hcorrect

/--
Unencoded domino undecidability from the second finite checked board package via
the proof-facing active/corner raw-board route and generated interior
position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_checked_board_data_active_corner_interiorRows
    (data : L2C2CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_active_corner_raw_boards_interiorRows
      data.checkedStacks data.boardLevels hinterior hcorrect

/--
Encoded domino undecidability from the first field-based Section 7 board
package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_board_data_interiorRows
    (data : L2C1SignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_interiorRows
      (l2c1RobinsonSection7DataOfSignalTowerBoardData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first field-based Section 7 board
package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_board_data_interiorRows
    (data : L2C1SignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_data_interiorRows
      (l2c1RobinsonSection7DataOfSignalTowerBoardData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second field-based Section 7 board
package and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_board_data_interiorRows
    (data : L2C2SignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_interiorRows
      (l2c2RobinsonSection7DataOfSignalTowerBoardData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second field-based Section 7 board
package and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_board_data_interiorRows
    (data : L2C2SignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_data_interiorRows
      (l2c2RobinsonSection7DataOfSignalTowerBoardData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the first field-based Section 7 board
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_board_data_interiorPackage
    (data : L2C1SignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_interiorPackage
      (l2c1RobinsonSection7DataOfSignalTowerBoardData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first field-based Section 7 board
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_board_data_interiorPackage
    (data : L2C1SignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_data_interiorPackage
      (l2c1RobinsonSection7DataOfSignalTowerBoardData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the second field-based Section 7 board
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_board_data_interiorPackage
    (data : L2C2SignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_interiorPackage
      (l2c2RobinsonSection7DataOfSignalTowerBoardData data)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second field-based Section 7 board
package and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_board_data_interiorPackage
    (data : L2C2SignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_data_interiorPackage
      (l2c2RobinsonSection7DataOfSignalTowerBoardData data)
      hinterior hcorrect

/--
Encoded domino undecidability from the first field-based local signal tower,
explicit shifted board-level checks, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_board_checks_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_interiorRows
      (l2c1RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first field-based local signal tower,
explicit shifted board-level checks, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_board_checks_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_data_interiorRows
      (l2c1RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      hinterior hcorrect

/--
Encoded domino undecidability from the second field-based local signal tower,
explicit shifted board-level checks, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_board_checks_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_interiorRows
      (l2c2RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second field-based local signal tower,
explicit shifted board-level checks, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_board_checks_interiorRows
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_data_interiorRows
      (l2c2RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      hinterior hcorrect

/--
Encoded domino undecidability from the first field-based local signal tower,
explicit shifted board-level checks, and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_signal_tower_board_checks_interiorPackage
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_data_interiorPackage
      (l2c1RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first field-based local signal tower,
explicit shifted board-level checks, and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c1_signal_tower_board_checks_interiorPackage
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_data_interiorPackage
      (l2c1RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      hinterior hcorrect

/--
Encoded domino undecidability from the second field-based local signal tower,
explicit shifted board-level checks, and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_signal_tower_board_checks_interiorPackage
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_data_interiorPackage
      (l2c2RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second field-based local signal tower,
explicit shifted board-level checks, and the packaged source-uniform generated
interior position-code decoder.
-/
theorem
    domino_problem_undecidable_l2c2_signal_tower_board_checks_interiorPackage
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_data_interiorPackage
      (l2c2RobinsonSection7DataOfBoardLevelChecks
        signalLocalTower boardLevelChecks)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows, shifted raw-boundary Figure 16 board checks,
and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_checks_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorRows
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows, shifted raw-boundary Figure 16 board
checks, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_checks_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorRows
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows, shifted raw-boundary Figure 16 board checks,
and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_checks_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorRows
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows, shifted raw-boundary Figure 16 board
checks, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_checks_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorRows
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows, row-major checked raw-boundary Figure 16
board rows, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_rows_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorRows
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows, row-major checked raw-boundary Figure
16 board rows, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_rows_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorRows
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows, row-major checked raw-boundary Figure 16
board rows, and generated interior position-code rows.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_rows_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorRows
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows, row-major checked raw-boundary Figure
16 board rows, and generated interior position-code rows.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_rows_interiorRows
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorRows
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows, shifted raw-boundary Figure 16 board checks,
and the packaged source-uniform generated interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_checks_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorPackage
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows, shifted raw-boundary Figure 16 board
checks, and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_checks_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorPackage
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows, shifted raw-boundary Figure 16 board checks,
and the packaged source-uniform generated interior position-code decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_checks_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorPackage
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows, shifted raw-boundary Figure 16 board
checks, and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_checks_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorPackage
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryBoardLevelChecks
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the first audited L2-blank candidate, using
origin-zero active/corner windows, row-major checked raw-boundary Figure 16
board rows, and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_rows_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorPackage
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the first audited L2-blank candidate,
using origin-zero active/corner windows, row-major checked raw-boundary Figure
16 board rows, and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_rows_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_boxes_interiorPackage
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Encoded domino undecidability from the second audited L2-blank candidate, using
origin-zero active/corner windows, row-major checked raw-boundary Figure 16
board rows, and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_rows_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorPackage
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
      hinterior hcorrect

/--
Unencoded domino undecidability from the second audited L2-blank candidate,
using origin-zero active/corner windows, row-major checked raw-boundary Figure
16 board rows, and the packaged source-uniform generated interior position-code
decoder.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_rows_interiorPackage
    (originZeroWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_boxes_interiorPackage
      originZeroWindows
      (tileableBoxes_fig13Tiles_of_canonicalRawBoundaryCheckedBoardLevels
        hlevel)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
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
