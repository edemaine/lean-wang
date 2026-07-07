/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure18Reduction
import LeanWang.TM0FoldedPositionReduction

/-!
Final Figure 18 packaging with the generated folded-position semantic
correctness theorem imported.

`OllingerRobinsonFigure18Reduction` keeps the `positionProgramData`
correctness theorem as an explicit parameter so finite scaffold edits do not
force the large semantic proof file to rebuild.  This module is the final
integration layer: it imports that semantic proof and discharges the
`PositionSourceObligations` parameter for the concrete Figure 18 routes.
-/

noncomputable section

namespace LeanWang

open Nat.Partrec (Code)
open OllingerRobinson
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData

namespace TM0FoldedReduction

set_option linter.style.longLine false

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, fixed Robinson Section 7 obstruction-geometry routing,
finite scaffold/payload layer patches, and generated interior position-code
rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_fixed_geometry_routing_layer_interiorRowsCorrect
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
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_fixed_geometry_routing_layer_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, fixed Robinson Section 7 obstruction-geometry routing,
finite scaffold/payload layer patches, and generated interior position-code
rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_fixed_geometry_routing_layer_interiorRowsCorrect
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
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_fixed_geometry_routing_layer_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, fixed Robinson Section 7 obstruction-geometry routing,
finite scaffold/payload layer patches, and generated interior position-code
rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_fixed_geometry_routing_layer_interiorRowsCorrect
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
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_fixed_geometry_routing_layer_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, fixed Robinson Section 7 obstruction-geometry routing,
finite scaffold/payload layer patches, and generated interior position-code
rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_fixed_geometry_routing_layer_interiorRowsCorrect
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
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_fixed_geometry_routing_layer_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank Figure 18
candidate, fixed Robinson Section 7 product-witness routing,
finite scaffold/payload layer patches, and generated interior position-code
rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c1_product_layer_interiorRowsCorrect
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
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c1_fixed_geometry_product_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank Figure 18
candidate, fixed Robinson Section 7 product-witness routing,
finite scaffold/payload layer patches, and generated interior position-code
rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c1_product_layer_interiorRowsCorrect
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
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c1_fixed_geometry_product_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank Figure 18
candidate, fixed Robinson Section 7 product-witness routing,
finite scaffold/payload layer patches, and generated interior position-code
rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_of_figure13_l2c2_product_layer_interiorRowsCorrect
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
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_l2c2_fixed_geometry_product_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank Figure 18
candidate, fixed Robinson Section 7 product-witness routing,
finite scaffold/payload layer patches, and generated interior position-code
rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_of_figure13_l2c2_product_layer_interiorRowsCorrect
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
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_l2c2_fixed_geometry_product_position_source
      hrouting patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical raw-boundary Figure 16
macro-squares, and generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_interiorRowsCorrect
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical raw-boundary Figure 16
macro-squares, and generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_interiorRowsCorrect
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_raw_boundary_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical raw-boundary Figure 16
macro-squares, and generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_interiorRowsCorrect
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, canonical raw-boundary Figure 16
macro-squares, and generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_interiorRowsCorrect
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_raw_boundary_fig16_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
tiling-dependent Robinson geometry, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_geom_combined_tower_obligations_interiorRowsCorrect
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_geom_combined_tower_obligations_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
tiling-dependent Robinson geometry, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_geom_combined_tower_obligations_interiorRowsCorrect
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_geom_combined_tower_obligations_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
tiling-dependent Robinson geometry, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_geom_combined_tower_obligations_interiorRowsCorrect
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_geom_combined_tower_obligations_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
tiling-dependent Robinson geometry, translated active-box obligations, the
Robinson Section 7 tower/indexed-box certificate route, and generated interior
position-code rows, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_geom_combined_tower_obligations_interiorRowsCorrect
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_geom_combined_tower_obligations_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, shifted source/free-grid board-level
checks, and generated interior position-code rows, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_section7_geom_tower_board_checks_interiorRowsCorrect
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_section7_geom_tower_board_checks_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
Robinson Section 7 obstruction routing, shifted source/free-grid board-level
checks, and generated interior position-code rows, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_section7_geom_tower_board_checks_interiorRowsCorrect
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_section7_geom_tower_board_checks_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, shifted source/free-grid board-level
checks, and generated interior position-code rows, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_section7_geom_tower_board_checks_interiorRowsCorrect
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_section7_geom_tower_board_checks_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
Robinson Section 7 obstruction routing, shifted source/free-grid board-level
checks, and generated interior position-code rows, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_section7_geom_tower_board_checks_interiorRowsCorrect
    (section7Routing :
      LayeredSection7ObstructionRoutingInvariant
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid))
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_section7_geom_tower_board_checks_position_source
      section7Routing hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows and a raw Figure 13 plane tiling routed
through the signal-tower/translated-box obligation surface, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_plane_interiorRowsCorrect
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_plane_position_source
      originZeroWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
origin-zero active/corner windows and a raw Figure 13 plane tiling routed
through the signal-tower/translated-box obligation surface, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_plane_interiorRowsCorrect
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_signal_tower_fig13_plane_position_source
      originZeroWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows and a raw Figure 13 plane tiling routed
through the signal-tower/translated-box obligation surface, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_plane_interiorRowsCorrect
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_plane_position_source
      originZeroWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
origin-zero active/corner windows and a raw Figure 13 plane tiling routed
through the signal-tower/translated-box obligation surface, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_plane_interiorRowsCorrect
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_signal_tower_fig13_plane_position_source
      originZeroWindows hplane
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite checked Figure 18 layer stacks, shifted source/free-grid board-level
checks, and generated interior position-code rows routed through Robinson's
Section 7 signal-tower surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_checks_interiorRowsCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_checks_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite checked Figure 18 layer stacks, shifted source/free-grid board-level
checks, and generated interior position-code rows routed through Robinson's
Section 7 signal-tower surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_checks_interiorRowsCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_checks_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite checked Figure 18 layer stacks, shifted source/free-grid board-level
checks, and generated interior position-code rows routed through Robinson's
Section 7 signal-tower surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_checks_interiorRowsCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_checks_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite checked Figure 18 layer stacks, shifted source/free-grid board-level
checks, and generated interior position-code rows routed through Robinson's
Section 7 signal-tower surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_checks_interiorRowsCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_checks_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite checked Figure 18 layer stacks, row-major checked raw-boundary board
levels, and generated interior position-code rows routed through Robinson's
Section 7 signal-tower surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_rows_interiorRowsCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig13_rows_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite checked Figure 18 layer stacks, row-major checked raw-boundary board
levels, and generated interior position-code rows routed through Robinson's
Section 7 signal-tower surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_rows_interiorRowsCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig13_rows_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite checked Figure 18 layer stacks, row-major checked raw-boundary board
levels, and generated interior position-code rows routed through Robinson's
Section 7 signal-tower surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_rows_interiorRowsCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig13_rows_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite checked Figure 18 layer stacks, row-major checked raw-boundary board
levels, and generated interior position-code rows routed through Robinson's
Section 7 signal-tower surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_rows_interiorRowsCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig13_rows_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and finite-checked canonical
raw-boundary Figure 16 macro-squares, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_raw_boundary_bool_interiorRowsCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_raw_boundary_bool_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and finite-checked canonical
raw-boundary Figure 16 macro-squares, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_raw_boundary_bool_interiorRowsCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_raw_boundary_bool_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and finite-checked canonical
raw-boundary Figure 16 macro-squares, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_raw_boundary_bool_interiorRowsCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_raw_boundary_bool_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and finite-checked canonical
raw-boundary Figure 16 macro-squares, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_raw_boundary_bool_interiorRowsCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryMacroSquaresBool)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_raw_boundary_bool_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and row-major checked raw-boundary
Figure 16 level data, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_level_data_interiorRowsCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_level_data_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and row-major checked raw-boundary
Figure 16 level data, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_level_data_interiorRowsCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_level_data_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and row-major checked raw-boundary
Figure 16 level data, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_level_data_interiorRowsCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_level_data_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and row-major checked raw-boundary
Figure 16 level data, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_level_data_interiorRowsCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalRawBoundaryCheckedLevelData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_level_data_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first preferred field-based Section 7
package, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRowsCorrect
    (data : L2C1SignalTowerTranslatedBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first preferred field-based Section 7
package, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_signal_tower_translated_box_data_interiorRowsCorrect
    (data : L2C1SignalTowerTranslatedBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second preferred field-based Section 7
package, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRowsCorrect
    (data : L2C2SignalTowerTranslatedBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second preferred field-based Section 7
package, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_signal_tower_translated_box_data_interiorRowsCorrect
    (data : L2C2SignalTowerTranslatedBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first preferred origin-zero/finite
Figure 13 box package, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_interiorRowsCorrect
    (data : L2C1OriginZeroFig13BoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first preferred origin-zero/finite
Figure 13 box package, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_interiorRowsCorrect
    (data : L2C1OriginZeroFig13BoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second preferred origin-zero/finite
Figure 13 box package, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_interiorRowsCorrect
    (data : L2C2OriginZeroFig13BoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second preferred origin-zero/finite
Figure 13 box package, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_interiorRowsCorrect
    (data : L2C2OriginZeroFig13BoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_fig13_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
      data hinterior
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Unencoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
      data hinterior
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Encoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRows
      data hinterior
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Unencoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRows
      data hinterior
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the generated one-row position-code
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_oneRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the generated one-row position-code
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_oneRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the generated bounded-interior
position-code rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_boundedRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the generated bounded-interior
position-code rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_boundedRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_boundedRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_boundedRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the generated one-row position-code
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_oneRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the generated one-row position-code
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_oneRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the generated bounded-interior
position-code rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the generated bounded-interior
position-code rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

/--
Encoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

/--
Unencoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_boundedRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_boundedRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

/--
Encoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

/--
Unencoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_boundedRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_boundedRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first Section 7 board/free-line
translated-box package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first Section 7 board/free-line
translated-box package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second Section 7 board/free-line
translated-box package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second Section 7 board/free-line
translated-box package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first Section 7 board/free-line
translated-box package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_decoderStepCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first Section 7 board/free-line
translated-box package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_decoderStepCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second Section 7 board/free-line
translated-box package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_decoderStepCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second Section 7 board/free-line
translated-box package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_decoderStepCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first Section 7 board/free-line
translated-box package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_globalCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first Section 7 board/free-line
translated-box package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_globalCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second Section 7 board/free-line
translated-box package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_globalCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second Section 7 board/free-line
translated-box package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_globalCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_decoderStepCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_decoderStepCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hstep

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_decoderStepCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_decoderStepCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hstep

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_decoderStepCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_decoderStepCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hstep

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_decoderStepCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_decoderStepCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hstep

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_globalCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_globalCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_globalCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_globalCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_globalCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_globalCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_globalCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_globalCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_sourceCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_sourceCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_sourceCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_sourceCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first canonical free-site
active/corner recognition package, finite compatible Figure 16 level checks,
and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_free_site_compatible_fig16_sourceCodeCorrect
    (canonicalActiveCorner : L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks : Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_sourceCodeCorrect
      (l2c1CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
        canonicalActiveCorner compatibleLevelChecks)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first canonical free-site
active/corner recognition package, finite compatible Figure 16 level checks,
and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_free_site_compatible_fig16_sourceCodeCorrect
    (canonicalActiveCorner : L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks : Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_sourceCodeCorrect
      (l2c1CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
        canonicalActiveCorner compatibleLevelChecks)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second canonical free-site
active/corner recognition package, finite compatible Figure 16 level checks,
and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_free_site_compatible_fig16_sourceCodeCorrect
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks : Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_sourceCodeCorrect
      (l2c2CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
        canonicalActiveCorner compatibleLevelChecks)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second canonical free-site
active/corner recognition package, finite compatible Figure 16 level checks,
and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_free_site_compatible_fig16_sourceCodeCorrect
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks : Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_sourceCodeCorrect
      (l2c2CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
        canonicalActiveCorner compatibleLevelChecks)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (canonicalActiveCorner : L2C1CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (canonicalActiveCorner : L2C1CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the source-specialized
position-code label-index decoder, with `positionProgramData` semantic
correctness discharged for the first audited L2 candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stacks_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the source-specialized
position-code label-index decoder, with `positionProgramData` semantic
correctness discharged for the first audited L2 candidate.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stacks_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the source-specialized
position-code label-index decoder, with `positionProgramData` semantic
correctness discharged for the second audited L2 candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stacks_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the source-specialized
position-code label-index decoder, with `positionProgramData` semantic
correctness discharged for the second audited L2 candidate.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stacks_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first origin-zero Section 7 layer-patch
obligation surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_interiorRowsCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first origin-zero Section 7 layer-patch
obligation surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_interiorRowsCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second origin-zero Section 7 layer-patch
obligation surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_interiorRowsCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second origin-zero Section 7
layer-patch obligation surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_interiorRowsCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from origin-zero active/corner windows and finite
active-corner layer patches for the first audited L2-blank candidate, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from origin-zero active/corner windows and
finite active-corner layer patches for the first audited L2-blank candidate,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from origin-zero active/corner windows and finite
active-corner layer patches for the second audited L2-blank candidate, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from origin-zero active/corner windows and
finite active-corner layer patches for the second audited L2-blank candidate,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant and a raw Figure 13 plane tiling, with `positionProgramData`
semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_tiles_plane_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRowsCorrect
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant and a raw Figure 13 plane tiling, with `positionProgramData`
semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_board_free_line_fig13_tiles_plane_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRowsCorrect
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant and a raw Figure 13 plane tiling, with `positionProgramData`
semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_tiles_plane_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRowsCorrect
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant and a raw Figure 13 plane tiling, with `positionProgramData`
semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_board_free_line_fig13_tiles_plane_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRowsCorrect
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant and finite raw Figure 13 boxes, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant and finite raw Figure 13 boxes, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant and finite raw Figure 13 boxes, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant and finite raw Figure 13 boxes, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the generated position-code decoder step, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_decoderStepCorrect
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
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the generated position-code decoder step, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_decoderStepCorrect
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
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_globalCodeCorrect
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
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_globalCodeCorrect
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
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_sourceCodeCorrect
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
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_sourceCodeCorrect
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
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

end TM0FoldedReduction

end LeanWang
