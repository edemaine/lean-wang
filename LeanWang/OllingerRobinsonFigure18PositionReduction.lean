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
compatible Robinson level grids and canonical checked compatible Figure 16
macro-squares, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_level_fig16_interiorRowsCorrect
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_level_compatible_fig16_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
macro-squares, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_level_fig16_interiorRowsCorrect
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_level_compatible_fig16_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
macro-squares, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_level_fig16_interiorRowsCorrect
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_level_compatible_fig16_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
compatible Robinson level grids and canonical checked compatible Figure 16
macro-squares, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_level_fig16_interiorRowsCorrect
    (hgrids :
      OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_level_compatible_fig16_position_source
      hgrids hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked compatible
Figure 16 macro-squares, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_signal_tower_fig16_interiorRowsCorrect
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_signal_tower_fig16_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked compatible
Figure 16 macro-squares, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_l2c1_signal_tower_fig16_interiorRowsCorrect
    (htower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_signal_tower_fig16_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked compatible
Figure 16 macro-squares, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_signal_tower_fig16_interiorRowsCorrect
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_signal_tower_fig16_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
the field-based Robinson Section 7 signal tower and canonical checked compatible
Figure 16 macro-squares, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_l2c2_signal_tower_fig16_interiorRowsCorrect
    (htower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_signal_tower_fig16_position_source
      htower hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and canonical checked compatible
Figure 16 macro-squares, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_fig16_interiorRowsCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_signal_tower_fig16_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first audited L2-blank candidate via
finite origin-zero checked layer stacks and canonical checked compatible
Figure 16 macro-squares, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_fig16_interiorRowsCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_signal_tower_fig16_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and canonical checked compatible
Figure 16 macro-squares, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_fig16_interiorRowsCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_signal_tower_fig16_position_source
      hchecked hlevel
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second audited L2-blank candidate via
finite origin-zero checked layer stacks and canonical checked compatible
Figure 16 macro-squares, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_fig16_interiorRowsCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_signal_tower_fig16_position_source
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

end TM0FoldedReduction

end LeanWang
