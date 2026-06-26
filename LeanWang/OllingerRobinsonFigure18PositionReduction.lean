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

end TM0FoldedReduction

end LeanWang
