/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13Data

/-!
Combined finite audit certificate for the Figure 13/Figure 16 scaffold data.

The raw Figure 13 tile list, the TSV-derived layer decomposition, and the
Figure 16 substitution table are maintained in separate modules.  This file
packages the finite facts that downstream Section 7 scaffold checks need from
both sources, without editing the large transcription file.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace LayeredFigure18ScaffoldData
namespace ConcreteData

/--
Combined finite audit certificate for the human Figure 13/Figure 16
transcription.

The Figure 13 fields certify the 92 indexed layer rows from
`figures/fig13-human.tsv`; the Figure 16 fields certify the substitution table
and its local edge checks.  Downstream scaffold lemmas can depend on this single
object when they need both the raw Figure 13 layer lookup and the checked
Figure 16 block semantics.
-/
structure Figure13Figure16AuditCertificate : Prop where
  fig13TilesLength : fig13Tiles.length = 92
  fig13TilesNodup : fig13Tiles.Nodup
  figure13Layers : Figure13LayerTranscriptionCertificate
  figure16Substitution : Figure16.HumanTranscriptionCertificate
  figure16RuleValid :
    ∀ source : Figure16.RuleSource,
      ValidRectangle Figure16.Symbol.tileSet source.block.rectangle
  figure16RuleTileable :
    ∀ _ : Figure16.RuleSource,
      TileableSquare Figure16.Symbol.tileSet 2

/-- The checked finite audit package for the concrete Figure 13/Figure 16 data. -/
theorem figure13Figure16AuditCertificate :
    Figure13Figure16AuditCertificate where
  fig13TilesLength := fig13Tiles_length
  fig13TilesNodup := fig13Tiles_nodup
  figure13Layers := figure13LayerTranscriptionCertificate
  figure16Substitution := Figure16.humanTranscriptionCertificate
  figure16RuleValid := Figure16.RuleSource.block_validRectangle_symbolTileSet
  figure16RuleTileable := Figure16.RuleSource.block_tileableSquare_symbolTileSet

/--
The checked Figure 13 stack attached to a site rectangle expands to a valid
Figure 16 symbol rectangle in every layer.

This is the first finite-check-facing consequence of the combined audit data:
once the local stack compatibility Boolean is proved for a site rectangle, the
three layer substitutions are ordinary valid Wang rectangles over the component
symbol tileset.
-/
theorem checkedLayerStackOfSiteRectangle_expandedRectangle_valid {w h : Nat}
    (R : SiteRectangle w h)
    (hcompatible :
      (checkedLayerStackRectangleOfSiteRectangle R).compatibleBool layerData
        (checkedLayerStackRectangleOfSiteRectangle_lookupBool R) = true)
    (layer : Layer) :
    ValidRectangle Figure16.Symbol.tileSet
      (Figure16.BlockGrid.expandedRectangle
        ((checkedLayerStackOfSiteRectangle R hcompatible).blockGrid layer)) :=
  (checkedLayerStackOfSiteRectangle R hcompatible).expandedRectangle_valid layer

/--
Square specialization of
`checkedLayerStackOfSiteRectangle_expandedRectangle_valid`.
-/
theorem checkedLayerStackOfSiteRectangle_tileableExpandedSquare {n : Nat}
    (R : SiteRectangle n n)
    (hcompatible :
      (checkedLayerStackRectangleOfSiteRectangle R).compatibleBool layerData
        (checkedLayerStackRectangleOfSiteRectangle_lookupBool R) = true)
    (layer : Layer) :
    TileableSquare Figure16.Symbol.tileSet (2 * n) :=
  (checkedLayerStackOfSiteRectangle R hcompatible).tileableExpandedSquare layer

end ConcreteData
end LayeredFigure18ScaffoldData
end Figure13Layers
end OllingerRobinson
end LeanWang
