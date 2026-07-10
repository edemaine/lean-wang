/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104Tiles
import LeanWang.OllingerRobinsonFigure18Obstruction

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
  figure16ParentIndexCandidateHistogram :
    parentIndexCandidateCountHistogram =
      [(1, 20), (2, 82), (3, 51), (4, 36), (5, 15),
        (7, 28), (8, 48), (24, 48), (40, 40)]
  figure16RadiusZeroParentIndexAmbiguous :
    allTargetsHaveUniqueParentIndexBool = false
  figure16EveryTargetHasParentIndex :
    allTargetsHaveParentIndexBool = true
  figure16ChildIndexCandidateCountHistogram :
    childIndexCandidateCountHistogram = [(0, 12), (1, 356)]
  figure16MissingChildParentQuadrants :
    missingChildParentQuadrants =
      [(68, .southwest), (69, .southwest), (70, .southwest),
        (71, .southwest), (72, .southwest), (73, .southwest),
        (74, .southwest), (75, .southwest), (76, .southwest),
        (77, .southwest), (78, .southwest), (79, .southwest)]
  figure16ComponentTripleCounts :
    (currentComponentTriples.length,
      substitutionImageComponentTriples.length,
      oneStepClosedComponentTriples.length,
      (substitutionImageOf oneStepClosedComponentTriples).length) =
        (92, 103, 104, 103)
  figure16OneStepClosedUniqueChildren :
    oneStepClosedUniqueChildrenBool = true
  figure16OneStepClosedUnderSubstitution :
    oneStepClosedUnderSubstitutionBool = true
  figure16Closed104AlphabetLength : Closed104.alphabet.length = 104
  figure16Closed104ChildrenUnique : Closed104.allChildrenUniqueBool = true
  figure16Closed104ChildRectanglesValid :
    Closed104.allChildRectanglesValidBool = true
  figure16Closed104HorizontalBoundariesPreserved :
    Closed104.allHorizontalBoundariesPreservedBool = true
  figure16Closed104VerticalBoundariesPreserved :
    Closed104.allVerticalBoundariesPreservedBool = true
  figure16AlignedBlockCount :
    alignedCompatibleChildBlockCount = 92
  figure16AlignedBlocksAreSingleRawTiles :
    allAlignedCompatibleBlocksHaveSameIndexBool = true
  figure16AlignedBlockUniqueParent :
    allAlignedCompatibleBlocksHaveUniqueParentBool = true
  figure18RawEdgeObstruction :
    ¬ TileableSquare figure18ScaffoldTiles 3

/-- The checked finite audit package for the concrete Figure 13/Figure 16 data. -/
theorem figure13Figure16AuditCertificate :
    Figure13Figure16AuditCertificate where
  fig13TilesLength := fig13Tiles_length
  fig13TilesNodup := fig13Tiles_nodup
  figure13Layers := figure13LayerTranscriptionCertificate
  figure16Substitution := Figure16.humanTranscriptionCertificate
  figure16RuleValid := Figure16.RuleSource.block_validRectangle_symbolTileSet
  figure16RuleTileable := Figure16.RuleSource.block_tileableSquare_symbolTileSet
  figure16ParentIndexCandidateHistogram := parentIndexCandidateCountHistogram_eq
  figure16RadiusZeroParentIndexAmbiguous :=
    allTargetsHaveUniqueParentIndexBool_eq_false
  figure16EveryTargetHasParentIndex := allTargetsHaveParentIndexBool_eq_true
  figure16ChildIndexCandidateCountHistogram :=
    childIndexCandidateCountHistogram_eq
  figure16MissingChildParentQuadrants := missingChildParentQuadrants_eq
  figure16ComponentTripleCounts := componentTripleCounts_eq
  figure16OneStepClosedUniqueChildren := oneStepClosedUniqueChildrenBool_eq_true
  figure16OneStepClosedUnderSubstitution :=
    oneStepClosedUnderSubstitutionBool_eq_true
  figure16Closed104AlphabetLength := Closed104.alphabet_length
  figure16Closed104ChildrenUnique := Closed104.allChildrenUniqueBool_eq_true
  figure16Closed104ChildRectanglesValid :=
    Closed104.allChildRectanglesValidBool_eq_true
  figure16Closed104HorizontalBoundariesPreserved :=
    Closed104.allHorizontalBoundariesPreservedBool_eq_true
  figure16Closed104VerticalBoundariesPreserved :=
    Closed104.allVerticalBoundariesPreservedBool_eq_true
  figure16AlignedBlockCount := alignedCompatibleChildBlockCount_eq
  figure16AlignedBlocksAreSingleRawTiles :=
    allAlignedCompatibleBlocksHaveSameIndexBool_eq_true
  figure16AlignedBlockUniqueParent :=
    allAlignedCompatibleBlocksHaveUniqueParentBool_eq_true
  figure18RawEdgeObstruction :=
    Figure18Site.not_tileableSquare_figure18ScaffoldTiles_three

/-- The concrete Figure 13 transcription has a thin-layer component at every index. -/
theorem layerData_componentAtLayerAt_thin (index : Fin 92) :
    layerData.componentAtLayerAt index .thin =
      some (LayerComponent.thin (thinComponentAt index)) := by
  rw [← sparseLayerRows_layerData]
  exact sparseLayerRows.separateLayerRows.layerData_componentAtLayerAt_thin
    (sparseLayerRows_thinAt index)

/-- The concrete Figure 13 transcription has a thick-layer component at every index. -/
theorem layerData_componentAtLayerAt_thick (index : Fin 92) :
    layerData.componentAtLayerAt index .thick =
      some (LayerComponent.thick (thickComponentAt index)) := by
  rw [← sparseLayerRows_layerData]
  exact sparseLayerRows.separateLayerRows.layerData_componentAtLayerAt_thick
    (sparseLayerRows_thickAt index)

/-- The concrete Figure 13 transcription has a black-layer component at every index. -/
theorem layerData_componentAtLayerAt_black (index : Fin 92) :
    layerData.componentAtLayerAt index .black =
      some (LayerComponent.black (blackComponentAt index)) := by
  rw [← sparseLayerRows_layerData]
  exact sparseLayerRows.separateLayerRows.layerData_componentAtLayerAt_black
    (sparseLayerRows_blackAt index)

/--
Every concrete Figure 13 tile row has a component in every Figure 16 layer.
-/
theorem layerData_componentAtLayerAt_exists
    (index : Fin 92) (layer : Layer) :
    ∃ component : LayerComponent,
      layerData.componentAtLayerAt index layer = some component ∧
        component.layer = layer := by
  cases layer with
  | thin =>
      refine ⟨LayerComponent.thin (thinComponentAt index),
        layerData_componentAtLayerAt_thin index, rfl⟩
  | thick =>
      refine ⟨LayerComponent.thick (thickComponentAt index),
        layerData_componentAtLayerAt_thick index, rfl⟩
  | black =>
      refine ⟨LayerComponent.black (blackComponentAt index),
        layerData_componentAtLayerAt_black index, rfl⟩

/--
Site-level form of `layerData_componentAtLayerAt_exists`.
-/
theorem layerData_componentAtSiteLayer_exists
    (site : Figure18Site) (layer : Layer) :
    ∃ component : LayerComponent,
      layerData.componentAtSiteLayer site layer = some component ∧
        component.layer = layer :=
  layerData_componentAtLayerAt_exists site.index layer

/--
Every concrete Figure 13 site/layer component selects a unique certified
Figure 16 substitution rule.
-/
theorem layerData_componentAtSiteLayer_exists_certifiedSubstitutionRule
    (site : Figure18Site) (layer : Layer) :
    ∃ component : LayerComponent,
      layerData.componentAtSiteLayer site layer = some component ∧
        component.layer = layer ∧
          ∃! rule : Figure16.SubstitutionRule,
            rule ∈ Figure16.certifiedSubstitutionTable.rules ∧
              rule.source = component.ruleSource := by
  rcases layerData_componentAtSiteLayer_exists site layer with
    ⟨component, hcomponent, hlayer⟩
  exact ⟨component, hcomponent, hlayer,
    Figure16.certifiedSubstitutionTable.exists_unique_rule_for_source
      component.ruleSource⟩

/--
The certified rule selected by every concrete Figure 13 site/layer component
expands to that component's Figure 16 block.
-/
theorem layerData_componentAtSiteLayer_certifiedSubstitutionRule_block
    {site : Figure18Site} {layer : Layer} {component : LayerComponent}
    (_hcomponent : layerData.componentAtSiteLayer site layer = some component)
    {rule : Figure16.SubstitutionRule}
    (hrule : rule ∈ Figure16.certifiedSubstitutionTable.rules)
    (hsource : rule.source = component.ruleSource) :
    rule.block = component.block := by
  rw [Figure16.certifiedSubstitutionTable.block_eq_source_block hrule,
    hsource]
  rfl

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

/--
The first audited L2 blank candidate passes the finite generated
site-pair/layer-stack compatibility check.
-/
theorem l2Component1BlankCandidate_pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      l2Component1BlankCandidateActiveSiteData
      l2Component1BlankCandidateCornerSite = true :=
  l2Component1BlankCandidatePairCompatibilityBool

/--
The second audited L2 blank candidate passes the finite generated
site-pair/layer-stack compatibility check.
-/
theorem l2Component2BlankCandidate_pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      l2Component2BlankCandidateActiveSiteData
      l2Component2BlankCandidateCornerSite = true :=
  l2Component2BlankCandidatePairCompatibilityBool

/--
Every locally compatible square rectangle using only the first L2 candidate's
listed active sites and corner has a matching compatible checked Figure 13/16
layer stack.
-/
theorem l2Component1BlankCandidate_exists_compatible_checkedLayerStackRectangle
    {n : Nat} (R : SiteRectangle n n)
    (hsites : ∀ i : Fin n, ∀ j : Fin n,
      R i j = l2Component1BlankCandidateCornerSite ∨
        R i j ∈ l2Component1BlankCandidateActiveSiteData.sites)
    (hh : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible (R i j) (R ⟨i.val + 1, hi⟩ j) = true)
    (hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible (R i j) (R i ⟨j.val + 1, hj⟩) = true) :
    ∃ (stackData : CheckedLayerStackRectangle n n),
      ∃ (_hsite : stackData.sites.matchesSiteRectangleBool R = true),
        ∃ (hmatch :
          (sparseRawDataOfSites l2Component1BlankCandidateActiveSiteData
            l2Component1BlankCandidateCornerSite).layerStackRectangleMatchesBool
              stackData = true),
          stackData.compatibleBool
            (sparseRawDataOfSites l2Component1BlankCandidateActiveSiteData
              l2Component1BlankCandidateCornerSite).layerData
            (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
              hmatch) = true :=
  sparseRawDataOfSites_exists_compatible_checkedLayerStackRectangle
    l2Component1BlankCandidateActiveSiteData
    l2Component1BlankCandidateCornerSite
    l2Component1BlankCandidate_pairCompatibility R hsites hh hv

/--
Every locally compatible square rectangle using only the second L2 candidate's
listed active sites and corner has a matching compatible checked Figure 13/16
layer stack.
-/
theorem l2Component2BlankCandidate_exists_compatible_checkedLayerStackRectangle
    {n : Nat} (R : SiteRectangle n n)
    (hsites : ∀ i : Fin n, ∀ j : Fin n,
      R i j = l2Component2BlankCandidateCornerSite ∨
        R i j ∈ l2Component2BlankCandidateActiveSiteData.sites)
    (hh : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible (R i j) (R ⟨i.val + 1, hi⟩ j) = true)
    (hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible (R i j) (R i ⟨j.val + 1, hj⟩) = true) :
    ∃ (stackData : CheckedLayerStackRectangle n n),
      ∃ (_hsite : stackData.sites.matchesSiteRectangleBool R = true),
        ∃ (hmatch :
          (sparseRawDataOfSites l2Component2BlankCandidateActiveSiteData
            l2Component2BlankCandidateCornerSite).layerStackRectangleMatchesBool
              stackData = true),
          stackData.compatibleBool
            (sparseRawDataOfSites l2Component2BlankCandidateActiveSiteData
              l2Component2BlankCandidateCornerSite).layerData
            (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
              hmatch) = true :=
  sparseRawDataOfSites_exists_compatible_checkedLayerStackRectangle
    l2Component2BlankCandidateActiveSiteData
    l2Component2BlankCandidateCornerSite
    l2Component2BlankCandidate_pairCompatibility R hsites hh hv

end ConcreteData
end LayeredFigure18ScaffoldData
end Figure13Layers
end OllingerRobinson
end LeanWang
