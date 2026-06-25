/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13Transcription
import LeanWang.OllingerRobinsonFigure16

/-!
Layer decomposition interface for the Figure 13 tiles.

Figure 16 is stated in terms of the three individual layers that appear in the
Ollinger/Robinson tiles.  Figure 13, by contrast, lists the superimposed Wang
tiles.  This module gives the eventual 92-row transcription a precise Lean
shape: each raw Figure 13 tile may be annotated by its thin, thick, and black
layer components, and those components determine the Figure 16 substitution
rules that act on the tile.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers

/-- Which of the three Figure 16 layers a component belongs to. -/
inductive Layer where
  | thin
  | thick
  | black
deriving DecidableEq, Repr

namespace Layer

def all : List Layer := [.thin, .thick, .black]

theorem mem_all (layer : Layer) : layer ∈ all := by
  cases layer <;> decide

theorem all_nodup : all.Nodup := by
  decide

end Layer

/-- A single Figure 16 layer component appearing in a raw Figure 13 tile. -/
inductive LayerComponent where
  | thin (component : Figure16.Thin)
  | thick (component : Figure16.Thick)
  | black (component : Figure16.Black)
deriving DecidableEq, Repr

namespace LayerComponent

def layer : LayerComponent → Layer
  | .thin _ => .thin
  | .thick _ => .thick
  | .black _ => .black

def symbol : LayerComponent → Figure16.Symbol
  | .thin component => .thin component
  | .thick component => .thick component
  | .black component => .black component

def ruleSource : LayerComponent → Figure16.RuleSource
  | .thin component => .l2Component1 component
  | .thick component => .l2Component2 component
  | .black component => .l3 component

def block (component : LayerComponent) : Figure16.Block :=
  component.ruleSource.block

theorem symbol_mem_all (component : LayerComponent) :
    component.symbol ∈ Figure16.Symbol.all :=
  Figure16.Symbol.mem_all component.symbol

theorem ruleSource_mem_all (component : LayerComponent) :
    component.ruleSource ∈ Figure16.RuleSource.all :=
  Figure16.RuleSource.mem_all component.ruleSource

theorem exists_substitutionRule (component : LayerComponent) :
    ∃ rule : Figure16.SubstitutionRule,
      rule ∈ Figure16.substitutionRules ∧
        rule.source = component.ruleSource ∧ rule.block = component.block := by
  refine ⟨Figure16.SubstitutionRule.ofSource component.ruleSource,
    Figure16.SubstitutionRule.ofSource_mem component.ruleSource, rfl, ?_⟩
  rfl

theorem block_validRectangle_symbolTileSet (component : LayerComponent) :
    ValidRectangle Figure16.Symbol.tileSet component.block.rectangle := by
  exact component.ruleSource.block_validRectangle_symbolTileSet

end LayerComponent

/-- The layer components visible in one raw Figure 13 tile. -/
structure Components where
  thin : Option Figure16.Thin
  thick : Option Figure16.Thick
  black : Option Figure16.Black
deriving DecidableEq, Repr

namespace Components

def empty : Components where
  thin := none
  thick := none
  black := none

def toLayerComponents (components : Components) : List LayerComponent :=
  (match components.thin with
    | none => []
    | some component => [LayerComponent.thin component]) ++
  (match components.thick with
    | none => []
    | some component => [LayerComponent.thick component]) ++
  (match components.black with
    | none => []
    | some component => [LayerComponent.black component])

def componentAtLayer (components : Components) : Layer → Option LayerComponent
  | .thin => components.thin.map LayerComponent.thin
  | .thick => components.thick.map LayerComponent.thick
  | .black => components.black.map LayerComponent.black

def symbols (components : Components) : List Figure16.Symbol :=
  components.toLayerComponents.map LayerComponent.symbol

/--
Figure 16 substitution rules directly selected by the components of a Figure 13
tile.  The `phi_L1(*)` rule is global background data and is kept separately
from component-indexed tile rows.
-/
def ruleSources (components : Components) : List Figure16.RuleSource :=
  components.toLayerComponents.map LayerComponent.ruleSource

def ruleBlocks (components : Components) : List Figure16.Block :=
  components.toLayerComponents.map LayerComponent.block

theorem layer_nodup (components : Components) :
    (components.toLayerComponents.map LayerComponent.layer).Nodup := by
  rcases components with ⟨thin, thick, black⟩
  cases thin <;> cases thick <;> cases black <;>
    simp [toLayerComponents, LayerComponent.layer]

theorem componentAtLayer_eq_some_iff
    {components : Components} {layer : Layer} {component : LayerComponent} :
    components.componentAtLayer layer = some component ↔
      component ∈ components.toLayerComponents ∧ component.layer = layer := by
  rcases components with ⟨thin, thick, black⟩
  cases layer <;> cases thin <;> cases thick <;> cases black <;>
    cases component <;>
    simp [componentAtLayer, toLayerComponents, LayerComponent.layer, eq_comm]

theorem componentAtLayer_mem
    {components : Components} {layer : Layer} {component : LayerComponent}
    (hcomponent : components.componentAtLayer layer = some component) :
    component ∈ components.toLayerComponents :=
  (componentAtLayer_eq_some_iff.1 hcomponent).1

theorem componentAtLayer_layer
    {components : Components} {layer : Layer} {component : LayerComponent}
    (hcomponent : components.componentAtLayer layer = some component) :
    component.layer = layer :=
  (componentAtLayer_eq_some_iff.1 hcomponent).2

theorem componentAtLayer_eq_some_of_mem
    {components : Components} {component : LayerComponent}
    (hcomponent : component ∈ components.toLayerComponents) :
    components.componentAtLayer component.layer = some component := by
  rw [componentAtLayer_eq_some_iff]
  exact ⟨hcomponent, rfl⟩

theorem eq_of_mem_same_layer
    {components : Components} {left right : LayerComponent}
    (hleft : left ∈ components.toLayerComponents)
    (hright : right ∈ components.toLayerComponents)
    (hlayer : left.layer = right.layer) :
    left = right := by
  have hleftLookup := componentAtLayer_eq_some_of_mem hleft
  have hrightLookup := componentAtLayer_eq_some_of_mem hright
  rw [hlayer, hrightLookup] at hleftLookup
  simpa using hleftLookup.symm

theorem componentAtLayer_isSome_iff_exists
    {components : Components} {layer : Layer} :
    (components.componentAtLayer layer).isSome ↔
      ∃ component : LayerComponent,
        component ∈ components.toLayerComponents ∧ component.layer = layer := by
  constructor
  · intro hsome
    rcases hcomponent : components.componentAtLayer layer with _ | component
    · simp [hcomponent] at hsome
    · exact ⟨component, componentAtLayer_eq_some_iff.1 hcomponent⟩
  · rintro ⟨component, hcomponent, hlayer⟩
    rw [← hlayer]
    rw [componentAtLayer_eq_some_of_mem hcomponent]
    rfl

theorem mem_ruleSources_iff_exists_layerComponent
    {components : Components} {source : Figure16.RuleSource} :
    source ∈ components.ruleSources ↔
      ∃ component : LayerComponent,
        component ∈ components.toLayerComponents ∧
          component.ruleSource = source := by
  simp [ruleSources]

theorem mem_ruleSources_all
    {components : Components} {source : Figure16.RuleSource}
    (hsource : source ∈ components.ruleSources) :
    source ∈ Figure16.RuleSource.all := by
  rcases mem_ruleSources_iff_exists_layerComponent.1 hsource with
    ⟨component, _hcomponent, rfl⟩
  exact component.ruleSource_mem_all

theorem exists_substitutionRule_of_mem_ruleSources
    {components : Components} {source : Figure16.RuleSource}
    (hsource : source ∈ components.ruleSources) :
    ∃ rule : Figure16.SubstitutionRule,
      rule ∈ Figure16.substitutionRules ∧ rule.source = source ∧
        rule.block = source.block := by
  rcases mem_ruleSources_iff_exists_layerComponent.1 hsource with
    ⟨component, _hcomponent, rfl⟩
  simpa [LayerComponent.block] using component.exists_substitutionRule

theorem validRectangle_of_mem_ruleSources
    {components : Components} {source : Figure16.RuleSource}
    (hsource : source ∈ components.ruleSources) :
    ValidRectangle Figure16.Symbol.tileSet source.block.rectangle := by
  rcases mem_ruleSources_iff_exists_layerComponent.1 hsource with
    ⟨component, _hcomponent, rfl⟩
  exact component.block_validRectangle_symbolTileSet

theorem mem_symbols_all
    {components : Components} {symbol : Figure16.Symbol}
    (hsymbol : symbol ∈ components.symbols) :
    symbol ∈ Figure16.Symbol.all := by
  rcases List.mem_map.1 hsymbol with ⟨component, _hcomponent, rfl⟩
  exact component.symbol_mem_all

end Components

/-- A raw Figure 13 tile paired with its layer annotation. -/
structure LayeredTile where
  index : Fin 92
  components : Components
deriving DecidableEq, Repr

namespace LayeredTile

def rawTile (tile : LayeredTile) : WangTile :=
  fig13Tile tile.index

def ruleSources (tile : LayeredTile) : List Figure16.RuleSource :=
  tile.components.ruleSources

def layerComponents (tile : LayeredTile) : List LayerComponent :=
  tile.components.toLayerComponents

def componentAtLayer (tile : LayeredTile) (layer : Layer) : Option LayerComponent :=
  tile.components.componentAtLayer layer

theorem layer_nodup (tile : LayeredTile) :
    (tile.layerComponents.map LayerComponent.layer).Nodup :=
  tile.components.layer_nodup

theorem componentAtLayer_eq_some_iff
    {tile : LayeredTile} {layer : Layer} {component : LayerComponent} :
    tile.componentAtLayer layer = some component ↔
      component ∈ tile.layerComponents ∧ component.layer = layer :=
  Components.componentAtLayer_eq_some_iff

theorem mem_ruleSources_all
    {tile : LayeredTile} {source : Figure16.RuleSource}
    (hsource : source ∈ tile.ruleSources) :
    source ∈ Figure16.RuleSource.all :=
  tile.components.mem_ruleSources_all hsource

end LayeredTile

/--
A 92-row layer transcription, ordered exactly like `fig13Tiles` and
`figure13-indexed.png`.
-/
structure Transcription where
  rows : List Components
  length_eq : rows.length = 92

namespace Transcription

def componentsAt (D : Transcription) (index : Fin 92) : Components :=
  D.rows.get ⟨index.val, by simp [D.length_eq, index.isLt]⟩

def layeredTileAt (D : Transcription) (index : Fin 92) : LayeredTile where
  index := index
  components := D.componentsAt index

def ruleSourcesAt (D : Transcription) (index : Fin 92) :
    List Figure16.RuleSource :=
  (D.componentsAt index).ruleSources

def layerComponentsAt (D : Transcription) (index : Fin 92) :
    List LayerComponent :=
  (D.componentsAt index).toLayerComponents

def componentAtLayerAt (D : Transcription) (index : Fin 92)
    (layer : Layer) : Option LayerComponent :=
  (D.componentsAt index).componentAtLayer layer

def specs (D : Transcription) : List LayeredTile :=
  (List.finRange 92).map D.layeredTileAt

theorem rows_getElem?_componentsAt (D : Transcription) (index : Fin 92) :
    D.rows[index.val]? = some (D.componentsAt index) := by
  unfold componentsAt
  exact List.getElem?_eq_getElem (by simp [D.length_eq, index.isLt])

@[simp]
theorem specs_length (D : Transcription) :
    D.specs.length = 92 := by
  simp [specs]

theorem layeredTileAt_mem_specs (D : Transcription) (index : Fin 92) :
    D.layeredTileAt index ∈ D.specs := by
  exact List.mem_map.2 ⟨index, List.mem_finRange index, rfl⟩

theorem layeredTileAt_rawTile (D : Transcription) (index : Fin 92) :
    (D.layeredTileAt index).rawTile = fig13Tile index :=
  rfl

theorem layerComponentsAt_eq_layeredTileAt
    (D : Transcription) (index : Fin 92) :
    D.layerComponentsAt index = (D.layeredTileAt index).layerComponents :=
  rfl

theorem layerComponentsAt_layer_nodup (D : Transcription) (index : Fin 92) :
    ((D.layerComponentsAt index).map LayerComponent.layer).Nodup :=
  (D.componentsAt index).layer_nodup

theorem componentAtLayerAt_eq_layeredTileAt
    (D : Transcription) (index : Fin 92) (layer : Layer) :
    D.componentAtLayerAt index layer =
      (D.layeredTileAt index).componentAtLayer layer :=
  rfl

theorem componentAtLayerAt_eq_some_iff
    {D : Transcription} {index : Fin 92} {layer : Layer}
    {component : LayerComponent} :
    D.componentAtLayerAt index layer = some component ↔
      component ∈ D.layerComponentsAt index ∧ component.layer = layer :=
  Components.componentAtLayer_eq_some_iff

theorem mem_ruleSourcesAt_all
    (D : Transcription) (index : Fin 92) {source : Figure16.RuleSource}
    (hsource : source ∈ D.ruleSourcesAt index) :
    source ∈ Figure16.RuleSource.all :=
  Components.mem_ruleSources_all hsource

theorem validRectangle_of_mem_ruleSourcesAt
    (D : Transcription) (index : Fin 92) {source : Figure16.RuleSource}
    (hsource : source ∈ D.ruleSourcesAt index) :
    ValidRectangle Figure16.Symbol.tileSet source.block.rectangle :=
  Components.validRectangle_of_mem_ruleSources hsource

/--
Layer components at a Figure 18 quarter-site.  The layer annotation belongs to
the underlying raw Figure 13 tile, so this intentionally depends only on
`site.index`, not on `site.quadrant`.
-/
def componentsAtSite (D : Transcription) (site : Figure18Site) : Components :=
  D.componentsAt site.index

def layeredTileAtSite (D : Transcription) (site : Figure18Site) : LayeredTile :=
  D.layeredTileAt site.index

def layerComponentsAtSite (D : Transcription) (site : Figure18Site) :
    List LayerComponent :=
  D.layerComponentsAt site.index

def componentAtSiteLayer (D : Transcription) (site : Figure18Site)
    (layer : Layer) : Option LayerComponent :=
  D.componentAtLayerAt site.index layer

def ruleSourcesAtSite (D : Transcription) (site : Figure18Site) :
    List Figure16.RuleSource :=
  D.ruleSourcesAt site.index

theorem componentsAtSite_eq_index (D : Transcription) (site : Figure18Site) :
    D.componentsAtSite site = D.componentsAt site.index :=
  rfl

theorem layeredTileAtSite_eq_index (D : Transcription) (site : Figure18Site) :
    D.layeredTileAtSite site = D.layeredTileAt site.index :=
  rfl

theorem layerComponentsAtSite_eq_index (D : Transcription) (site : Figure18Site) :
    D.layerComponentsAtSite site = D.layerComponentsAt site.index :=
  rfl

theorem componentAtSiteLayer_eq_index
    (D : Transcription) (site : Figure18Site) (layer : Layer) :
    D.componentAtSiteLayer site layer =
      D.componentAtLayerAt site.index layer :=
  rfl

theorem ruleSourcesAtSite_eq_index (D : Transcription) (site : Figure18Site) :
    D.ruleSourcesAtSite site = D.ruleSourcesAt site.index :=
  rfl

theorem layeredTileAtSite_rawTile (D : Transcription) (site : Figure18Site) :
    (D.layeredTileAtSite site).rawTile = site.rawTile :=
  rfl

theorem layerComponentsAtSite_layer_nodup
    (D : Transcription) (site : Figure18Site) :
    ((D.layerComponentsAtSite site).map LayerComponent.layer).Nodup :=
  D.layerComponentsAt_layer_nodup site.index

theorem componentAtSiteLayer_eq_some_iff
    {D : Transcription} {site : Figure18Site} {layer : Layer}
    {component : LayerComponent} :
    D.componentAtSiteLayer site layer = some component ↔
      component ∈ D.layerComponentsAtSite site ∧ component.layer = layer :=
  D.componentAtLayerAt_eq_some_iff

theorem componentAtSiteLayer_mem
    {D : Transcription} {site : Figure18Site} {layer : Layer}
    {component : LayerComponent}
    (hcomponent : D.componentAtSiteLayer site layer = some component) :
    component ∈ D.layerComponentsAtSite site :=
  (componentAtSiteLayer_eq_some_iff.1 hcomponent).1

theorem componentAtSiteLayer_layer
    {D : Transcription} {site : Figure18Site} {layer : Layer}
    {component : LayerComponent}
    (hcomponent : D.componentAtSiteLayer site layer = some component) :
    component.layer = layer :=
  (componentAtSiteLayer_eq_some_iff.1 hcomponent).2

theorem mem_ruleSourcesAtSite_all
    (D : Transcription) (site : Figure18Site) {source : Figure16.RuleSource}
    (hsource : source ∈ D.ruleSourcesAtSite site) :
    source ∈ Figure16.RuleSource.all :=
  D.mem_ruleSourcesAt_all site.index hsource

theorem validRectangle_of_mem_ruleSourcesAtSite
    (D : Transcription) (site : Figure18Site) {source : Figure16.RuleSource}
    (hsource : source ∈ D.ruleSourcesAtSite site) :
    ValidRectangle Figure16.Symbol.tileSet source.block.rectangle :=
  D.validRectangle_of_mem_ruleSourcesAt site.index hsource

theorem componentAtSiteLayer_block_validRectangle
    {D : Transcription} {site : Figure18Site} {layer : Layer}
    {component : LayerComponent}
    (_hcomponent : D.componentAtSiteLayer site layer = some component) :
    ValidRectangle Figure16.Symbol.tileSet component.block.rectangle :=
  component.block_validRectangle_symbolTileSet

end Transcription

/-- A rectangle of Figure 18 quarter-sites. -/
abbrev SiteRectangle (w h : Nat) := Fin w → Fin h → Figure18Site

namespace SiteRectangle

def indexRect {w h : Nat} (R : SiteRectangle w h) : Fin w → Fin h → Fin 92 :=
  fun i j => (R i j).index

def quadrantRect {w h : Nat} (R : SiteRectangle w h) : Fin w → Fin h → Quadrant :=
  fun i j => (R i j).quadrant

def tileRect {w h : Nat} (R : SiteRectangle w h) : Rectangle w h :=
  fun i j => (R i j).tile

def rawTileRect {w h : Nat} (R : SiteRectangle w h) : Rectangle w h :=
  fun i j => (R i j).rawTile

theorem tileRect_eq {w h : Nat} (R : SiteRectangle w h)
    (i : Fin w) (j : Fin h) :
    R.tileRect i j =
      fig13QuarterTile (R.indexRect i j) (R.quadrantRect i j) :=
  rfl

theorem rawTileRect_eq {w h : Nat} (R : SiteRectangle w h)
    (i : Fin w) (j : Fin h) :
    R.rawTileRect i j = fig13Tile (R.indexRect i j) :=
  rfl

end SiteRectangle

/--
A rectangle of Figure 18 sites together with the component selected in one
Figure 16 layer at every site.
-/
structure LayerComponentRectangle
    (D : Transcription) {w h : Nat} (R : SiteRectangle w h)
    (layer : Layer) where
  componentRect : Fin w → Fin h → LayerComponent
  lookup : ∀ i : Fin w, ∀ j : Fin h,
    D.componentAtSiteLayer (R i j) layer = some (componentRect i j)

namespace LayerComponentRectangle

def symbolRect
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) :
    Fin w → Fin h → Figure16.Symbol :=
  fun i j => (C.componentRect i j).symbol

def blockGrid
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) :
    Figure16.BlockGrid w h :=
  fun i j => (C.componentRect i j).block

def ruleSourceRect
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) :
    Fin w → Fin h → Figure16.RuleSource :=
  fun i j => (C.componentRect i j).ruleSource

theorem component_layer
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) (i : Fin w) (j : Fin h) :
    (C.componentRect i j).layer = layer :=
  D.componentAtSiteLayer_layer (C.lookup i j)

theorem component_mem_site
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) (i : Fin w) (j : Fin h) :
    C.componentRect i j ∈ D.layerComponentsAtSite (R i j) :=
  D.componentAtSiteLayer_mem (C.lookup i j)

theorem ruleSource_mem_all
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) (i : Fin w) (j : Fin h) :
    C.ruleSourceRect i j ∈ Figure16.RuleSource.all :=
  (C.componentRect i j).ruleSource_mem_all

theorem block_validRectangle_symbolTileSet
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) (i : Fin w) (j : Fin h) :
    ValidRectangle Figure16.Symbol.tileSet (C.blockGrid i j).rectangle :=
  (C.componentRect i j).block_validRectangle_symbolTileSet

theorem symbol_mem_all
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) (i : Fin w) (j : Fin h) :
    C.symbolRect i j ∈ Figure16.Symbol.all :=
  (C.componentRect i j).symbol_mem_all

end LayerComponentRectangle

/--
Boundary certificate for the Figure 16 block grid induced by a layer-component
rectangle.

The per-cell block compatibility follows from the certified Figure 16
substitution table; the two fields here are exactly the remaining neighbor
checks needed to expand the macroblocks into a valid component grid.
-/
structure CompatibleLayerComponentRectangle
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) where
  hBoundary : ∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
    (C.blockGrid i j).hBoundaryMatches (C.blockGrid ⟨i.val + 1, hi⟩ j)
  vBoundary : ∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
    (C.blockGrid i j).vBoundaryMatches (C.blockGrid i ⟨j.val + 1, hj⟩)

namespace CompatibleLayerComponentRectangle

theorem cell_compatible
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : LayerComponentRectangle D R layer}
    (_certificate : CompatibleLayerComponentRectangle C)
    (i : Fin w) (j : Fin h) :
    (C.blockGrid i j).Compatible :=
  (C.componentRect i j).ruleSource.block_compatible

theorem blockGrid_compatible
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : LayerComponentRectangle D R layer}
    (certificate : CompatibleLayerComponentRectangle C) :
    Figure16.BlockGrid.Compatible C.blockGrid := by
  exact ⟨certificate.cell_compatible, certificate.hBoundary, certificate.vBoundary⟩

theorem expandedTile_mem_symbolTileSet
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : LayerComponentRectangle D R layer}
    (_certificate : CompatibleLayerComponentRectangle C)
    (i : Fin w) (j : Fin h) (di dj : Fin 2) :
    Figure16.BlockGrid.expandedTile C.blockGrid i j di dj ∈
      Figure16.Symbol.tileSet :=
  Figure16.BlockGrid.expandedTile_mem_symbolTileSet C.blockGrid i j di dj

theorem expanded_hMatches_within
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : LayerComponentRectangle D R layer}
    (certificate : CompatibleLayerComponentRectangle C)
    (i : Fin w) (j : Fin h) (dj : Fin 2) :
    WangTile.HMatches
      (Figure16.BlockGrid.expandedTile C.blockGrid i j ⟨0, by decide⟩ dj)
      (Figure16.BlockGrid.expandedTile C.blockGrid i j ⟨1, by decide⟩ dj) :=
  Figure16.BlockGrid.expanded_hMatches_within
    certificate.blockGrid_compatible i j dj

theorem expanded_hMatches_boundary
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : LayerComponentRectangle D R layer}
    (certificate : CompatibleLayerComponentRectangle C)
    (i : Fin w) (j : Fin h) (hi : i.val + 1 < w) (dj : Fin 2) :
    WangTile.HMatches
      (Figure16.BlockGrid.expandedTile C.blockGrid i j ⟨1, by decide⟩ dj)
      (Figure16.BlockGrid.expandedTile C.blockGrid
        ⟨i.val + 1, hi⟩ j ⟨0, by decide⟩ dj) :=
  Figure16.BlockGrid.expanded_hMatches_boundary
    certificate.blockGrid_compatible i j hi dj

theorem expanded_vMatches_within
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : LayerComponentRectangle D R layer}
    (certificate : CompatibleLayerComponentRectangle C)
    (i : Fin w) (j : Fin h) (di : Fin 2) :
    WangTile.VMatches
      (Figure16.BlockGrid.expandedTile C.blockGrid i j di ⟨0, by decide⟩)
      (Figure16.BlockGrid.expandedTile C.blockGrid i j di ⟨1, by decide⟩) :=
  Figure16.BlockGrid.expanded_vMatches_within
    certificate.blockGrid_compatible i j di

theorem expanded_vMatches_boundary
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : LayerComponentRectangle D R layer}
    (certificate : CompatibleLayerComponentRectangle C)
    (i : Fin w) (j : Fin h) (hj : j.val + 1 < h) (di : Fin 2) :
    WangTile.VMatches
      (Figure16.BlockGrid.expandedTile C.blockGrid i j di ⟨1, by decide⟩)
      (Figure16.BlockGrid.expandedTile C.blockGrid
        i ⟨j.val + 1, hj⟩ di ⟨0, by decide⟩) :=
  Figure16.BlockGrid.expanded_vMatches_boundary
    certificate.blockGrid_compatible i j hj di

end CompatibleLayerComponentRectangle

/--
All three Figure 16 layer-component rectangles over the same Figure 18 site
rectangle, with compatibility certificates for each induced macroblock grid.
-/
structure LayerStackRectangle
    (D : Transcription) {w h : Nat} (R : SiteRectangle w h) where
  thin : LayerComponentRectangle D R .thin
  thick : LayerComponentRectangle D R .thick
  black : LayerComponentRectangle D R .black
  thinCompatible : CompatibleLayerComponentRectangle thin
  thickCompatible : CompatibleLayerComponentRectangle thick
  blackCompatible : CompatibleLayerComponentRectangle black

namespace LayerStackRectangle

def componentRect
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : LayerStackRectangle D R) : Layer → Fin w → Fin h → LayerComponent
  | .thin => S.thin.componentRect
  | .thick => S.thick.componentRect
  | .black => S.black.componentRect

def blockGrid
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : LayerStackRectangle D R) (layer : Layer) : Figure16.BlockGrid w h :=
  match layer with
  | .thin => S.thin.blockGrid
  | .thick => S.thick.blockGrid
  | .black => S.black.blockGrid

theorem component_layer
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : LayerStackRectangle D R) (layer : Layer) (i : Fin w) (j : Fin h) :
    (S.componentRect layer i j).layer = layer := by
  cases layer
  · exact S.thin.component_layer i j
  · exact S.thick.component_layer i j
  · exact S.black.component_layer i j

theorem blockGrid_compatible
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : LayerStackRectangle D R) (layer : Layer) :
    Figure16.BlockGrid.Compatible (S.blockGrid layer) := by
  cases layer
  · exact S.thinCompatible.blockGrid_compatible
  · exact S.thickCompatible.blockGrid_compatible
  · exact S.blackCompatible.blockGrid_compatible

theorem expandedTile_mem_symbolTileSet
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : LayerStackRectangle D R) (layer : Layer)
    (i : Fin w) (j : Fin h) (di dj : Fin 2) :
    Figure16.BlockGrid.expandedTile (S.blockGrid layer) i j di dj ∈
      Figure16.Symbol.tileSet := by
  cases layer
  · exact S.thinCompatible.expandedTile_mem_symbolTileSet i j di dj
  · exact S.thickCompatible.expandedTile_mem_symbolTileSet i j di dj
  · exact S.blackCompatible.expandedTile_mem_symbolTileSet i j di dj

theorem expanded_hMatches_boundary
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : LayerStackRectangle D R) (layer : Layer)
    (i : Fin w) (j : Fin h) (hi : i.val + 1 < w) (dj : Fin 2) :
    WangTile.HMatches
      (Figure16.BlockGrid.expandedTile (S.blockGrid layer)
        i j ⟨1, by decide⟩ dj)
      (Figure16.BlockGrid.expandedTile (S.blockGrid layer)
        ⟨i.val + 1, hi⟩ j ⟨0, by decide⟩ dj) := by
  cases layer
  · exact S.thinCompatible.expanded_hMatches_boundary i j hi dj
  · exact S.thickCompatible.expanded_hMatches_boundary i j hi dj
  · exact S.blackCompatible.expanded_hMatches_boundary i j hi dj

theorem expanded_vMatches_boundary
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : LayerStackRectangle D R) (layer : Layer)
    (i : Fin w) (j : Fin h) (hj : j.val + 1 < h) (di : Fin 2) :
    WangTile.VMatches
      (Figure16.BlockGrid.expandedTile (S.blockGrid layer)
        i j di ⟨1, by decide⟩)
      (Figure16.BlockGrid.expandedTile (S.blockGrid layer)
        i ⟨j.val + 1, hj⟩ di ⟨0, by decide⟩) := by
  cases layer
  · exact S.thinCompatible.expanded_vMatches_boundary i j hj di
  · exact S.thickCompatible.expanded_vMatches_boundary i j hj di
  · exact S.blackCompatible.expanded_vMatches_boundary i j hj di

end LayerStackRectangle

/-- Site rectangle extracted from an indexed active-corner window. -/
def siteRectangleOfIndexedActiveCornerWindow
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn) :
    SiteRectangle n n :=
  fun i j => {
    index := window.indexRect i j
    quadrant := window.quadrantRect i j
  }

theorem siteRectangleOfIndexedActiveCornerWindow_index
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (i : Fin n) (j : Fin n) :
    (siteRectangleOfIndexedActiveCornerWindow window i j).index =
      window.indexRect i j :=
  rfl

theorem siteRectangleOfIndexedActiveCornerWindow_quadrant
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (i : Fin n) (j : Fin n) :
    (siteRectangleOfIndexedActiveCornerWindow window i j).quadrant =
      window.quadrantRect i j :=
  rfl

theorem siteRectangleOfIndexedActiveCornerWindow_tile
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (i : Fin n) (j : Fin n) :
    (siteRectangleOfIndexedActiveCornerWindow window i j).tile =
      window.baseRect i j :=
  rfl

abbrev IndexedActiveCornerWindowLayerComponents
    (D : Transcription)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (layer : Layer) : Type :=
  LayerComponentRectangle D
    (siteRectangleOfIndexedActiveCornerWindow window) layer

abbrev CompatibleIndexedActiveCornerWindowLayerComponents
    (D : Transcription)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    {window : Figure18IndexedActiveCornerWindow table x n hn}
    {layer : Layer}
    (C : IndexedActiveCornerWindowLayerComponents D window layer) : Prop :=
  CompatibleLayerComponentRectangle C

abbrev IndexedActiveCornerWindowLayerStack
    (D : Transcription)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn) : Type :=
  LayerStackRectangle D
    (siteRectangleOfIndexedActiveCornerWindow window)

/--
An indexed active-corner window together with compatible Figure 13/16 layer
data over the same site rectangle.
-/
structure Figure18IndexedActiveCornerWindowWithLayerStack
    (D : Transcription) (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  window : Figure18IndexedActiveCornerWindow table x n hn
  layerStack : IndexedActiveCornerWindowLayerStack D window

/--
Layered strengthening of `HasFigure18IndexedActiveCornerWindows`.

This is the intended finite-data target for the recognizable-free-square side:
each extracted Figure 18 active window also carries compatible Figure 16 layer
data.
-/
def HasFigure18IndexedActiveCornerWindowsWithLayerStack
    (D : Transcription) (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18IndexedActiveCornerWindowWithLayerStack D table x n hn)

theorem hasFigure18IndexedActiveCornerWindows_of_layerStack
    {D : Transcription} {table : Figure18RoleTable}
    (hwindow : HasFigure18IndexedActiveCornerWindowsWithLayerStack D table) :
    HasFigure18IndexedActiveCornerWindows table := by
  intro T seed x hx n hn
  rcases hwindow x hx n hn with ⟨window⟩
  exact ⟨window.window⟩

/-- Site rectangle extracted from an indexed routed fixed-corner square. -/
def siteRectangleOfIndexedRoutedFixedCornerSquare
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn) :
    SiteRectangle n n :=
  window.siteRect

theorem siteRectangleOfIndexedRoutedFixedCornerSquare_eq
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn) :
    siteRectangleOfIndexedRoutedFixedCornerSquare window = window.siteRect :=
  rfl

theorem siteRectangleOfIndexedRoutedFixedCornerSquare_tile
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (i : Fin n) (j : Fin n) :
    (siteRectangleOfIndexedRoutedFixedCornerSquare window i j).tile =
      window.baseRect i j :=
  rfl

abbrev IndexedRoutedFixedCornerSquareLayerComponents
    (D : Transcription)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (layer : Layer) : Type :=
  LayerComponentRectangle D
    (siteRectangleOfIndexedRoutedFixedCornerSquare window) layer

abbrev CompatibleIndexedRoutedFixedCornerSquareLayerComponents
    (D : Transcription)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    {window : Figure18IndexedRoutedFixedCornerSquare table x n hn}
    {layer : Layer}
    (C : IndexedRoutedFixedCornerSquareLayerComponents D window layer) : Prop :=
  CompatibleLayerComponentRectangle C

abbrev IndexedRoutedFixedCornerSquareLayerStack
    (D : Transcription)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn) : Type :=
  LayerStackRectangle D
    (siteRectangleOfIndexedRoutedFixedCornerSquare window)

/--
An indexed routed fixed-corner square together with compatible Figure 13/16
layer data over its routed site rectangle.
-/
structure Figure18IndexedRoutedFixedCornerSquareWithLayerStack
    (D : Transcription) (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  window : Figure18IndexedRoutedFixedCornerSquare table x n hn
  layerStack : IndexedRoutedFixedCornerSquareLayerStack D window

/--
Layered strengthening of `HasFigure18IndexedRoutedFixedCornerSquares`.

This is the intended finite-data target for the routed-forcing side: each
routed payload square also carries compatible Figure 16 layer data on the
scaffold sites used to read the payload.
-/
def HasFigure18IndexedRoutedFixedCornerSquaresWithLayerStack
    (D : Transcription) (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18IndexedRoutedFixedCornerSquareWithLayerStack
          D table x n hn)

theorem hasFigure18IndexedRoutedFixedCornerSquares_of_layerStack
    {D : Transcription} {table : Figure18RoleTable}
    (hrouted : HasFigure18IndexedRoutedFixedCornerSquaresWithLayerStack D table) :
    HasFigure18IndexedRoutedFixedCornerSquares table := by
  intro T seed x hx n hn
  rcases hrouted x hx n hn with ⟨window⟩
  exact ⟨window.window⟩

/--
Layered certificate for the direct indexed-active Figure 18 route.

The layered fields are the stronger finite-data target; `toFigure18Certificate`
forgets the layer data and reuses the existing scaffold certificate pipeline.
-/
structure LayeredFigure18Certificate
    (D : Transcription) (table : Figure18RoleTable) : Prop where
  indexedRecognizable :
    HasFigure18IndexedActiveCornerWindowsWithLayerStack D table
  realizes : RealizesActiveCornerSquares table.presentation.toScaffold

namespace LayeredFigure18Certificate

def toFigure18Certificate
    {D : Transcription} {table : Figure18RoleTable}
    (certificate : LayeredFigure18Certificate D table) :
    Figure18Certificate table where
  indexedRecognizable :=
    hasFigure18IndexedActiveCornerWindows_of_layerStack
      certificate.indexedRecognizable
  realizes := certificate.realizes

theorem isScaffold
    {D : Transcription} {table : Figure18RoleTable}
    (certificate : LayeredFigure18Certificate D table) :
    IsScaffold table.presentation.toScaffold :=
  certificate.toFigure18Certificate.isScaffold

end LayeredFigure18Certificate

/--
Layered certificate for the indexed-routed Figure 18 route.

This is the preferred certificate shape for the Ollinger/Robinson scaffold once
the concrete Figure 13 layer transcription and routed free-coordinate proof are
filled in.
-/
structure LayeredFigure18IndexedRoutedCertificate
    (D : Transcription) (table : Figure18RoleTable) : Prop where
  indexedRoutedForces :
    HasFigure18IndexedRoutedFixedCornerSquaresWithLayerStack D table
  realizes : RealizesActiveCornerSquares table.presentation.toScaffold

namespace LayeredFigure18IndexedRoutedCertificate

def toFigure18IndexedRoutedCertificate
    {D : Transcription} {table : Figure18RoleTable}
    (certificate : LayeredFigure18IndexedRoutedCertificate D table) :
    Figure18IndexedRoutedCertificate table where
  indexedRoutedForces :=
    hasFigure18IndexedRoutedFixedCornerSquares_of_layerStack
      certificate.indexedRoutedForces
  realizes := certificate.realizes

def toFigure18RoutedCertificate
    {D : Transcription} {table : Figure18RoleTable}
    (certificate : LayeredFigure18IndexedRoutedCertificate D table) :
    Figure18RoutedCertificate table :=
  certificate.toFigure18IndexedRoutedCertificate.toRoutedCertificate

def toFigure18FlexibleCertificate
    {D : Transcription} {table : Figure18RoleTable}
    (certificate : LayeredFigure18IndexedRoutedCertificate D table) :
    Figure18FlexibleCertificate table :=
  certificate.toFigure18IndexedRoutedCertificate.toFlexibleCertificate

theorem isScaffold
    {D : Transcription} {table : Figure18RoleTable}
    (certificate : LayeredFigure18IndexedRoutedCertificate D table) :
    IsScaffold table.presentation.toScaffold :=
  certificate.toFigure18IndexedRoutedCertificate.isScaffold

end LayeredFigure18IndexedRoutedCertificate

/-- Concrete Figure 18 package using a layered direct indexed-active certificate. -/
structure LayeredFigure18Instance where
  layerData : Transcription
  table : Figure18RoleTable
  certificate : LayeredFigure18Certificate layerData table

namespace LayeredFigure18Instance

def toFigure18Instance (I : LayeredFigure18Instance) :
    Figure18Instance where
  table := I.table
  certificate := I.certificate.toFigure18Certificate

def finite (I : LayeredFigure18Instance) : FiniteCheckedTranscription :=
  I.table.finiteCheckedTranscription

def presentation (I : LayeredFigure18Instance) : ScaffoldPresentation :=
  I.table.presentation

theorem presentation_tiles (I : LayeredFigure18Instance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.toFigure18Instance.presentation_tiles

theorem isScaffold (I : LayeredFigure18Instance) :
    IsScaffold I.presentation.toScaffold :=
  I.toFigure18Instance.isScaffold

end LayeredFigure18Instance

/--
Concrete Figure 18 package using the preferred layered indexed-routed
certificate shape.
-/
structure LayeredFigure18IndexedRoutedInstance where
  layerData : Transcription
  table : Figure18RoleTable
  certificate : LayeredFigure18IndexedRoutedCertificate layerData table

namespace LayeredFigure18IndexedRoutedInstance

def toFigure18IndexedRoutedInstance
    (I : LayeredFigure18IndexedRoutedInstance) :
    Figure18IndexedRoutedInstance where
  table := I.table
  certificate := I.certificate.toFigure18IndexedRoutedCertificate

def toFigure18RoutedInstance
    (I : LayeredFigure18IndexedRoutedInstance) :
    Figure18RoutedInstance where
  table := I.table
  certificate := I.certificate.toFigure18RoutedCertificate

def toFigure18FlexibleInstance
    (I : LayeredFigure18IndexedRoutedInstance) :
    Figure18FlexibleInstance where
  table := I.table
  certificate := I.certificate.toFigure18FlexibleCertificate

def finite (I : LayeredFigure18IndexedRoutedInstance) :
    FiniteCheckedTranscription :=
  I.table.finiteCheckedTranscription

def presentation (I : LayeredFigure18IndexedRoutedInstance) :
    ScaffoldPresentation :=
  I.table.presentation

theorem toFigure18IndexedRoutedInstance_table
    (I : LayeredFigure18IndexedRoutedInstance) :
    I.toFigure18IndexedRoutedInstance.table = I.table :=
  rfl

theorem toFigure18RoutedInstance_table
    (I : LayeredFigure18IndexedRoutedInstance) :
    I.toFigure18RoutedInstance.table = I.table :=
  rfl

theorem toFigure18FlexibleInstance_table
    (I : LayeredFigure18IndexedRoutedInstance) :
    I.toFigure18FlexibleInstance.table = I.table :=
  rfl

theorem presentation_tiles (I : LayeredFigure18IndexedRoutedInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.toFigure18IndexedRoutedInstance.presentation_tiles

theorem isScaffold (I : LayeredFigure18IndexedRoutedInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.toFigure18IndexedRoutedInstance.isScaffold

end LayeredFigure18IndexedRoutedInstance

end Figure13Layers
end OllingerRobinson
end LeanWang
