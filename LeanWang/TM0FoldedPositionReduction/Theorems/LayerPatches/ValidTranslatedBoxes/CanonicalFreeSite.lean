/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.Theorems.LayerPatches.ValidTranslatedBoxes.CheckedStacks

/-!
Canonical-free-site valid-translated-box final theorem wrappers for the generated
position-coded folded reduction.

This module keeps the canonical free-site route separate from the checked-stack
wrappers, so each final theorem surface can be rebuilt independently.
-/

namespace LeanWang

namespace TM0FoldedReduction

set_option linter.style.longLine false in
/--
The scaffold tiles used by the second audited L2-blank candidate.
-/
abbrev L2C2Figure18ScaffoldTiles : TileSet :=
  _root_.LeanWang.OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData.l2Component2Figure18ScaffoldData.scaffold.tiles

set_option linter.style.longLine false in
/--
Valid translated boxes for every positive scale in the second audited
L2-blank candidate scaffold.
-/
abbrev L2C2Figure18ScaffoldValidTranslatedBoxes : Prop :=
  ∀ r : Nat, 0 < r →
    ∃ origin : Int × Int,
      ∃ base : TranslatedBoxPattern L2C2Figure18ScaffoldTiles r origin,
        ValidTranslatedBoxTiling L2C2Figure18ScaffoldTiles r origin base

set_option linter.style.longLine false in
/--
Encoded domino undecidability from canonical free-site routing and valid
translated scaffold boxes for the second audited L2-blank candidate, with
generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_position_source
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (source : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_position_source
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    source

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from canonical free-site routing and valid
translated scaffold boxes for the second audited L2-blank candidate, with
generated-position source obligations.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_position_source
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (source : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_position_source
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    source

set_option linter.style.longLine false in
/--
Encoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and the source-specialized generated position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_sourceCodeCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_sourceCodeCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and the source-specialized generated position-code
label-index decoder.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_sourceCodeCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_sourceCodeCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and generated one-row position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_oneRowsCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_oneRowsCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and generated one-row position-code rows.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_oneRowsCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_oneRowsCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and generated bounded-interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_boundedRowsCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_boundedRowsCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and generated bounded-interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_boundedRowsCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_boundedRowsCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and bounded-interior generated position-code rows
at concrete numeric label slots.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_boundedRowsAtIndexCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_boundedRowsAtIndexCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and bounded-interior generated position-code rows
at concrete numeric label slots.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_boundedRowsAtIndexCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_boundedRowsAtIndexCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_interiorRowsCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_interiorRowsCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_interiorRowsCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_interiorRowsCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hinterior

set_option linter.style.longLine false in
/--
Encoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and interior generated position-code rows at
concrete numeric label slots.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_interiorRowsAtIndexCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_interiorRowsAtIndexCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and interior generated position-code rows at
concrete numeric label slots.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_interiorRowsAtIndexCorrect
    (routing : L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes : L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_canonical_free_site_routing_layer_patches_interiorRowsAtIndexCorrect
    routing
    (l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hinterior

end TM0FoldedReduction

end LeanWang
