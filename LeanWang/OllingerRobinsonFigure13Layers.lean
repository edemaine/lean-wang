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

def Component : Layer → Type
  | .thin => Figure16.Thin
  | .thick => Figure16.Thick
  | .black => Figure16.Black

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

def ofLayer : (layer : Layer) → layer.Component → LayerComponent
  | .thin, component => .thin component
  | .thick, component => .thick component
  | .black, component => .black component

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

@[simp]
theorem ofLayer_layer (layer : Layer) (component : layer.Component) :
    (ofLayer layer component).layer = layer := by
  cases layer <;> rfl

@[simp]
theorem ofLayer_thin (component : Figure16.Thin) :
    ofLayer .thin component = .thin component :=
  rfl

@[simp]
theorem ofLayer_thick (component : Figure16.Thick) :
    ofLayer .thick component = .thick component :=
  rfl

@[simp]
theorem ofLayer_black (component : Figure16.Black) :
    ofLayer .black component = .black component :=
  rfl

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

def ofOptions
    (thin : Option Figure16.Thin)
    (thick : Option Figure16.Thick)
    (black : Option Figure16.Black) : Components where
  thin := thin
  thick := thick
  black := black

def ofAll
    (thin : Figure16.Thin) (thick : Figure16.Thick)
    (black : Figure16.Black) : Components :=
  ofOptions (some thin) (some thick) (some black)

@[simp]
theorem ofOptions_thin
    (thin : Option Figure16.Thin)
    (thick : Option Figure16.Thick)
    (black : Option Figure16.Black) :
    (ofOptions thin thick black).thin = thin :=
  rfl

@[simp]
theorem ofOptions_thick
    (thin : Option Figure16.Thin)
    (thick : Option Figure16.Thick)
    (black : Option Figure16.Black) :
    (ofOptions thin thick black).thick = thick :=
  rfl

@[simp]
theorem ofOptions_black
    (thin : Option Figure16.Thin)
    (thick : Option Figure16.Thick)
    (black : Option Figure16.Black) :
    (ofOptions thin thick black).black = black :=
  rfl

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

/--
Flat checked data for a rectangle of Figure 18 quarter-sites.

The list is read row-major with `i + w * j`: west-to-east inside each row, and
south-to-north across rows.  Each entry stores the raw Figure 13 tile index and
the Figure 18 quadrant.
-/
structure CheckedNatSiteRectangle (w h : Nat) where
  specs : List (Nat × Quadrant)
  length_eq : specs.length = w * h
  valid : specs.all (fun spec => decide (spec.1 < 92)) = true

namespace CheckedNatSiteRectangle

def flatIndex {w h : Nat} (_data : CheckedNatSiteRectangle w h)
    (i : Fin w) (j : Fin h) : Nat :=
  i.val + w * j.val

theorem flatIndex_lt {w h : Nat} (data : CheckedNatSiteRectangle w h)
    (i : Fin w) (j : Fin h) :
    data.flatIndex i j < data.specs.length := by
  rw [data.length_eq]
  unfold flatIndex
  have hrow : i.val + w * j.val < w + w * j.val :=
    Nat.add_lt_add_right i.isLt (w * j.val)
  have hrow' : w + w * j.val = w * (j.val + 1) := by
    rw [Nat.mul_succ]
    exact Nat.add_comm _ _
  have hj : j.val + 1 ≤ h := Nat.succ_le_of_lt j.isLt
  calc
    i.val + w * j.val < w + w * j.val := hrow
    _ = w * (j.val + 1) := hrow'
    _ ≤ w * h := Nat.mul_le_mul_left w hj

def specAt {w h : Nat} (data : CheckedNatSiteRectangle w h)
    (i : Fin w) (j : Fin h) : Nat × Quadrant :=
  data.specs.get ⟨data.flatIndex i j, data.flatIndex_lt i j⟩

theorem specAt_mem {w h : Nat} (data : CheckedNatSiteRectangle w h)
    (i : Fin w) (j : Fin h) :
    data.specAt i j ∈ data.specs :=
  List.get_mem data.specs ⟨data.flatIndex i j, data.flatIndex_lt i j⟩

theorem specAt_index_lt {w h : Nat} (data : CheckedNatSiteRectangle w h)
    (i : Fin w) (j : Fin h) :
    (data.specAt i j).1 < 92 := by
  have hcheck := List.all_eq_true.1 data.valid
    (data.specAt i j) (data.specAt_mem i j)
  exact of_decide_eq_true hcheck

def toSiteRectangle {w h : Nat} (data : CheckedNatSiteRectangle w h) :
    SiteRectangle w h :=
  fun i j => {
    index := ⟨(data.specAt i j).1, data.specAt_index_lt i j⟩
    quadrant := (data.specAt i j).2
  }

@[simp]
theorem toSiteRectangle_index_val {w h : Nat}
    (data : CheckedNatSiteRectangle w h) (i : Fin w) (j : Fin h) :
    (data.toSiteRectangle i j).index.val = (data.specAt i j).1 :=
  rfl

@[simp]
theorem toSiteRectangle_quadrant {w h : Nat}
    (data : CheckedNatSiteRectangle w h) (i : Fin w) (j : Fin h) :
    (data.toSiteRectangle i j).quadrant = (data.specAt i j).2 :=
  rfl

def matchesSiteRectangleBool {w h : Nat}
    (data : CheckedNatSiteRectangle w h) (R : SiteRectangle w h) : Bool :=
  (List.finRange w).all fun i =>
    (List.finRange h).all fun j =>
      decide <| data.toSiteRectangle i j = R i j

theorem toSiteRectangle_eq_of_matchesSiteRectangleBool {w h : Nat}
    {data : CheckedNatSiteRectangle w h} {R : SiteRectangle w h}
    (hcheck : data.matchesSiteRectangleBool R = true) :
    data.toSiteRectangle = R := by
  funext i j
  unfold matchesSiteRectangleBool at hcheck
  have hiCheck := List.all_eq_true.1 hcheck i (List.mem_finRange i)
  have hjCheck := List.all_eq_true.1 hiCheck j (List.mem_finRange j)
  exact of_decide_eq_true hjCheck

end CheckedNatSiteRectangle

/--
Flat checked data for a rectangle of Figure 16 components in one layer.

The list uses the same row-major order as `CheckedNatSiteRectangle`: `i + w * j`.
-/
structure CheckedLayerComponentRectangle (w h : Nat) (layer : Layer) where
  specs : List layer.Component
  length_eq : specs.length = w * h

namespace CheckedLayerComponentRectangle

def flatIndex {w h : Nat} {layer : Layer}
    (_data : CheckedLayerComponentRectangle w h layer)
    (i : Fin w) (j : Fin h) : Nat :=
  i.val + w * j.val

theorem flatIndex_lt {w h : Nat} {layer : Layer}
    (data : CheckedLayerComponentRectangle w h layer)
    (i : Fin w) (j : Fin h) :
    data.flatIndex i j < data.specs.length := by
  rw [data.length_eq]
  unfold flatIndex
  have hrow : i.val + w * j.val < w + w * j.val :=
    Nat.add_lt_add_right i.isLt (w * j.val)
  have hrow' : w + w * j.val = w * (j.val + 1) := by
    rw [Nat.mul_succ]
    exact Nat.add_comm _ _
  have hj : j.val + 1 ≤ h := Nat.succ_le_of_lt j.isLt
  calc
    i.val + w * j.val < w + w * j.val := hrow
    _ = w * (j.val + 1) := hrow'
    _ ≤ w * h := Nat.mul_le_mul_left w hj

def componentAt {w h : Nat} {layer : Layer}
    (data : CheckedLayerComponentRectangle w h layer)
    (i : Fin w) (j : Fin h) : layer.Component :=
  data.specs.get ⟨data.flatIndex i j, data.flatIndex_lt i j⟩

def lookupBool
    {w h : Nat} {layer : Layer}
    (D : Transcription) (siteData : CheckedNatSiteRectangle w h)
    (data : CheckedLayerComponentRectangle w h layer) : Bool :=
  (List.finRange w).all fun i =>
    (List.finRange h).all fun j =>
      decide <| D.componentAtSiteLayer (siteData.toSiteRectangle i j) layer =
        some (LayerComponent.ofLayer layer (data.componentAt i j))

theorem lookup_of_lookupBool
    {w h : Nat} {layer : Layer}
    {D : Transcription} {siteData : CheckedNatSiteRectangle w h}
    {data : CheckedLayerComponentRectangle w h layer}
    (hcheck : lookupBool D siteData data = true) :
    ∀ i : Fin w, ∀ j : Fin h,
      D.componentAtSiteLayer (siteData.toSiteRectangle i j) layer =
        some (LayerComponent.ofLayer layer (data.componentAt i j)) := by
  intro i j
  unfold lookupBool at hcheck
  have hiCheck := List.all_eq_true.1 hcheck i (List.mem_finRange i)
  have hjCheck := List.all_eq_true.1 hiCheck j (List.mem_finRange j)
  exact of_decide_eq_true hjCheck

theorem lookupBool_of_lookup
    {w h : Nat} {layer : Layer}
    {D : Transcription} {siteData : CheckedNatSiteRectangle w h}
    {data : CheckedLayerComponentRectangle w h layer}
    (hlookup : ∀ i : Fin w, ∀ j : Fin h,
      D.componentAtSiteLayer (siteData.toSiteRectangle i j) layer =
        some (LayerComponent.ofLayer layer (data.componentAt i j))) :
    lookupBool D siteData data = true := by
  unfold lookupBool
  apply List.all_eq_true.2
  intro i hi
  apply List.all_eq_true.2
  intro j hj
  exact decide_eq_true (hlookup i j)

end CheckedLayerComponentRectangle

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
Layer-component rectangle using the native component type for the selected
layer.  This is a data-entry adapter for Figure 16 transcriptions: thin-layer
rectangles contain `Figure16.Thin`, thick-layer rectangles contain
`Figure16.Thick`, and black-layer rectangles contain `Figure16.Black`.
-/
structure TypedLayerComponentRectangle
    (D : Transcription) {w h : Nat} (R : SiteRectangle w h)
    (layer : Layer) where
  componentRect : Fin w → Fin h → layer.Component
  lookup : ∀ i : Fin w, ∀ j : Fin h,
    D.componentAtSiteLayer (R i j) layer =
      some (LayerComponent.ofLayer layer (componentRect i j))

namespace TypedLayerComponentRectangle

def toLayerComponentRectangle
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : TypedLayerComponentRectangle D R layer) :
    LayerComponentRectangle D R layer where
  componentRect := fun i j => LayerComponent.ofLayer layer (C.componentRect i j)
  lookup := C.lookup

@[simp]
theorem toLayerComponentRectangle_componentRect
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : TypedLayerComponentRectangle D R layer) (i : Fin w) (j : Fin h) :
    C.toLayerComponentRectangle.componentRect i j =
      LayerComponent.ofLayer layer (C.componentRect i j) :=
  rfl

theorem component_layer
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : TypedLayerComponentRectangle D R layer) (i : Fin w) (j : Fin h) :
    (LayerComponent.ofLayer layer (C.componentRect i j)).layer = layer := by
  simp

def blockGrid
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : TypedLayerComponentRectangle D R layer) :
    Figure16.BlockGrid w h :=
  C.toLayerComponentRectangle.blockGrid

end TypedLayerComponentRectangle

namespace CheckedLayerComponentRectangle

def toTypedLayerComponentRectangle
    {w h : Nat} {layer : Layer}
    (D : Transcription) (siteData : CheckedNatSiteRectangle w h)
    (data : CheckedLayerComponentRectangle w h layer)
    (hcheck : lookupBool D siteData data = true) :
    TypedLayerComponentRectangle D siteData.toSiteRectangle layer where
  componentRect := data.componentAt
  lookup := lookup_of_lookupBool hcheck

@[simp]
theorem toTypedLayerComponentRectangle_componentRect
    {w h : Nat} {layer : Layer}
    (D : Transcription) (siteData : CheckedNatSiteRectangle w h)
    (data : CheckedLayerComponentRectangle w h layer)
    (hcheck : lookupBool D siteData data = true)
    (i : Fin w) (j : Fin h) :
    (data.toTypedLayerComponentRectangle D siteData hcheck).componentRect i j =
      data.componentAt i j :=
  rfl

end CheckedLayerComponentRectangle

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

def hBoundaryBool
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) : Bool :=
  (List.finRange w).all fun i =>
    if hi : i.val + 1 < w then
      (List.finRange h).all fun j =>
        decide <| (C.blockGrid i j).hBoundaryMatches
          (C.blockGrid ⟨i.val + 1, hi⟩ j)
    else
      true

def vBoundaryBool
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) : Bool :=
  (List.finRange h).all fun j =>
    if hj : j.val + 1 < h then
      (List.finRange w).all fun i =>
        decide <| (C.blockGrid i j).vBoundaryMatches
          (C.blockGrid i ⟨j.val + 1, hj⟩)
    else
      true

def compatibleBool
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : LayerComponentRectangle D R layer) : Bool :=
  hBoundaryBool C && vBoundaryBool C

theorem hBoundary_of_hBoundaryBool
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : LayerComponentRectangle D R layer}
    (hcheck : hBoundaryBool C = true) :
    ∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
      (C.blockGrid i j).hBoundaryMatches (C.blockGrid ⟨i.val + 1, hi⟩ j) := by
  intro i j hi
  unfold hBoundaryBool at hcheck
  have hiCheck := List.all_eq_true.1 hcheck i (List.mem_finRange i)
  simp [hi] at hiCheck
  simpa using hiCheck j

theorem vBoundary_of_vBoundaryBool
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : LayerComponentRectangle D R layer}
    (hcheck : vBoundaryBool C = true) :
    ∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
      (C.blockGrid i j).vBoundaryMatches (C.blockGrid i ⟨j.val + 1, hj⟩) := by
  intro i j hj
  unfold vBoundaryBool at hcheck
  have hjCheck := List.all_eq_true.1 hcheck j (List.mem_finRange j)
  simp [hj] at hjCheck
  simpa using hjCheck i

theorem of_compatibleBool
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : LayerComponentRectangle D R layer}
    (hcheck : compatibleBool C = true) :
    CompatibleLayerComponentRectangle C := by
  rw [compatibleBool, Bool.and_eq_true] at hcheck
  exact {
    hBoundary := hBoundary_of_hBoundaryBool hcheck.1
    vBoundary := vBoundary_of_vBoundaryBool hcheck.2
  }

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

abbrev CompatibleTypedLayerComponentRectangle
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : TypedLayerComponentRectangle D R layer) : Prop :=
  CompatibleLayerComponentRectangle C.toLayerComponentRectangle

namespace TypedLayerComponentRectangle

def compatibleBool
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    (C : TypedLayerComponentRectangle D R layer) : Bool :=
  CompatibleLayerComponentRectangle.compatibleBool C.toLayerComponentRectangle

theorem compatible_of_compatibleBool
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h} {layer : Layer}
    {C : TypedLayerComponentRectangle D R layer}
    (hcheck : C.compatibleBool = true) :
    CompatibleTypedLayerComponentRectangle C :=
  CompatibleLayerComponentRectangle.of_compatibleBool hcheck

end TypedLayerComponentRectangle

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

def ofCompatibleBool
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (thin : LayerComponentRectangle D R .thin)
    (thick : LayerComponentRectangle D R .thick)
    (black : LayerComponentRectangle D R .black)
    (hthin : CompatibleLayerComponentRectangle.compatibleBool thin = true)
    (hthick : CompatibleLayerComponentRectangle.compatibleBool thick = true)
    (hblack : CompatibleLayerComponentRectangle.compatibleBool black = true) :
    LayerStackRectangle D R where
  thin := thin
  thick := thick
  black := black
  thinCompatible := CompatibleLayerComponentRectangle.of_compatibleBool hthin
  thickCompatible := CompatibleLayerComponentRectangle.of_compatibleBool hthick
  blackCompatible := CompatibleLayerComponentRectangle.of_compatibleBool hblack

@[simp]
theorem ofCompatibleBool_thin
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (thin : LayerComponentRectangle D R .thin)
    (thick : LayerComponentRectangle D R .thick)
    (black : LayerComponentRectangle D R .black)
    (hthin : CompatibleLayerComponentRectangle.compatibleBool thin = true)
    (hthick : CompatibleLayerComponentRectangle.compatibleBool thick = true)
    (hblack : CompatibleLayerComponentRectangle.compatibleBool black = true) :
    (ofCompatibleBool thin thick black hthin hthick hblack).thin = thin :=
  rfl

@[simp]
theorem ofCompatibleBool_thick
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (thin : LayerComponentRectangle D R .thin)
    (thick : LayerComponentRectangle D R .thick)
    (black : LayerComponentRectangle D R .black)
    (hthin : CompatibleLayerComponentRectangle.compatibleBool thin = true)
    (hthick : CompatibleLayerComponentRectangle.compatibleBool thick = true)
    (hblack : CompatibleLayerComponentRectangle.compatibleBool black = true) :
    (ofCompatibleBool thin thick black hthin hthick hblack).thick = thick :=
  rfl

@[simp]
theorem ofCompatibleBool_black
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (thin : LayerComponentRectangle D R .thin)
    (thick : LayerComponentRectangle D R .thick)
    (black : LayerComponentRectangle D R .black)
    (hthin : CompatibleLayerComponentRectangle.compatibleBool thin = true)
    (hthick : CompatibleLayerComponentRectangle.compatibleBool thick = true)
    (hblack : CompatibleLayerComponentRectangle.compatibleBool black = true) :
    (ofCompatibleBool thin thick black hthin hthick hblack).black = black :=
  rfl

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

/--
Typed layer-stack rectangle.  This is equivalent to `LayerStackRectangle`, but
its fields are closer to Figure 16 data entry: each layer uses its own component
type before being embedded into `LayerComponent`.
-/
structure TypedLayerStackRectangle
    (D : Transcription) {w h : Nat} (R : SiteRectangle w h) where
  thin : TypedLayerComponentRectangle D R .thin
  thick : TypedLayerComponentRectangle D R .thick
  black : TypedLayerComponentRectangle D R .black
  thinCompatible : CompatibleTypedLayerComponentRectangle thin
  thickCompatible : CompatibleTypedLayerComponentRectangle thick
  blackCompatible : CompatibleTypedLayerComponentRectangle black

namespace TypedLayerStackRectangle

def ofCompatibleBool
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (thin : TypedLayerComponentRectangle D R .thin)
    (thick : TypedLayerComponentRectangle D R .thick)
    (black : TypedLayerComponentRectangle D R .black)
    (hthin : thin.compatibleBool = true)
    (hthick : thick.compatibleBool = true)
    (hblack : black.compatibleBool = true) :
    TypedLayerStackRectangle D R where
  thin := thin
  thick := thick
  black := black
  thinCompatible := TypedLayerComponentRectangle.compatible_of_compatibleBool hthin
  thickCompatible := TypedLayerComponentRectangle.compatible_of_compatibleBool hthick
  blackCompatible := TypedLayerComponentRectangle.compatible_of_compatibleBool hblack

@[simp]
theorem ofCompatibleBool_thin
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (thin : TypedLayerComponentRectangle D R .thin)
    (thick : TypedLayerComponentRectangle D R .thick)
    (black : TypedLayerComponentRectangle D R .black)
    (hthin : thin.compatibleBool = true)
    (hthick : thick.compatibleBool = true)
    (hblack : black.compatibleBool = true) :
    (ofCompatibleBool thin thick black hthin hthick hblack).thin = thin :=
  rfl

@[simp]
theorem ofCompatibleBool_thick
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (thin : TypedLayerComponentRectangle D R .thin)
    (thick : TypedLayerComponentRectangle D R .thick)
    (black : TypedLayerComponentRectangle D R .black)
    (hthin : thin.compatibleBool = true)
    (hthick : thick.compatibleBool = true)
    (hblack : black.compatibleBool = true) :
    (ofCompatibleBool thin thick black hthin hthick hblack).thick = thick :=
  rfl

@[simp]
theorem ofCompatibleBool_black
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (thin : TypedLayerComponentRectangle D R .thin)
    (thick : TypedLayerComponentRectangle D R .thick)
    (black : TypedLayerComponentRectangle D R .black)
    (hthin : thin.compatibleBool = true)
    (hthick : thick.compatibleBool = true)
    (hblack : black.compatibleBool = true) :
    (ofCompatibleBool thin thick black hthin hthick hblack).black = black :=
  rfl

def toLayerStackRectangle
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : TypedLayerStackRectangle D R) :
    LayerStackRectangle D R where
  thin := S.thin.toLayerComponentRectangle
  thick := S.thick.toLayerComponentRectangle
  black := S.black.toLayerComponentRectangle
  thinCompatible := S.thinCompatible
  thickCompatible := S.thickCompatible
  blackCompatible := S.blackCompatible

@[simp]
theorem toLayerStackRectangle_thin
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : TypedLayerStackRectangle D R) :
    S.toLayerStackRectangle.thin = S.thin.toLayerComponentRectangle :=
  rfl

@[simp]
theorem toLayerStackRectangle_thick
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : TypedLayerStackRectangle D R) :
    S.toLayerStackRectangle.thick = S.thick.toLayerComponentRectangle :=
  rfl

@[simp]
theorem toLayerStackRectangle_black
    {D : Transcription} {w h : Nat} {R : SiteRectangle w h}
    (S : TypedLayerStackRectangle D R) :
    S.toLayerStackRectangle.black = S.black.toLayerComponentRectangle :=
  rfl

end TypedLayerStackRectangle

/--
Flat checked data for all three Figure 16 layers over one Figure 18 site
rectangle.

This is the intended concrete entry point for local Figure 18 scaffold
certificates: `sites` records the Figure 13 tile/quadrant at each position, and
the three component lists record the matching `L1`, `L2`, and `L3` labels.
-/
structure CheckedLayerStackRectangle (w h : Nat) where
  sites : CheckedNatSiteRectangle w h
  thin : CheckedLayerComponentRectangle w h .thin
  thick : CheckedLayerComponentRectangle w h .thick
  black : CheckedLayerComponentRectangle w h .black

namespace CheckedLayerStackRectangle

def siteRectangle {w h : Nat} (data : CheckedLayerStackRectangle w h) :
    SiteRectangle w h :=
  data.sites.toSiteRectangle

def thinLookupBool {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h) : Bool :=
  data.thin.lookupBool D data.sites

def thickLookupBool {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h) : Bool :=
  data.thick.lookupBool D data.sites

def blackLookupBool {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h) : Bool :=
  data.black.lookupBool D data.sites

def lookupBool {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h) : Bool :=
  (data.thinLookupBool D && data.thickLookupBool D) &&
    data.blackLookupBool D

theorem thinLookupBool_of_lookupBool {w h : Nat}
    {D : Transcription} {data : CheckedLayerStackRectangle w h}
    (hcheck : data.lookupBool D = true) :
    data.thinLookupBool D = true := by
  rw [lookupBool, Bool.and_eq_true, Bool.and_eq_true] at hcheck
  exact hcheck.1.1

theorem thickLookupBool_of_lookupBool {w h : Nat}
    {D : Transcription} {data : CheckedLayerStackRectangle w h}
    (hcheck : data.lookupBool D = true) :
    data.thickLookupBool D = true := by
  rw [lookupBool, Bool.and_eq_true, Bool.and_eq_true] at hcheck
  exact hcheck.1.2

theorem blackLookupBool_of_lookupBool {w h : Nat}
    {D : Transcription} {data : CheckedLayerStackRectangle w h}
    (hcheck : data.lookupBool D = true) :
    data.blackLookupBool D = true := by
  rw [lookupBool, Bool.and_eq_true] at hcheck
  exact hcheck.2

theorem lookupBool_of_layer_lookups {w h : Nat}
    {D : Transcription} {data : CheckedLayerStackRectangle w h}
    (hthin : data.thinLookupBool D = true)
    (hthick : data.thickLookupBool D = true)
    (hblack : data.blackLookupBool D = true) :
    data.lookupBool D = true := by
  rw [lookupBool, hthin, hthick, hblack]
  rfl

def thinRectangle {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h)
    (hlookup : data.thinLookupBool D = true) :
    TypedLayerComponentRectangle D data.siteRectangle .thin :=
  data.thin.toTypedLayerComponentRectangle D data.sites hlookup

def thickRectangle {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h)
    (hlookup : data.thickLookupBool D = true) :
    TypedLayerComponentRectangle D data.siteRectangle .thick :=
  data.thick.toTypedLayerComponentRectangle D data.sites hlookup

def blackRectangle {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h)
    (hlookup : data.blackLookupBool D = true) :
    TypedLayerComponentRectangle D data.siteRectangle .black :=
  data.black.toTypedLayerComponentRectangle D data.sites hlookup

def compatibleBool {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h)
    (hlookup : data.lookupBool D = true) : Bool :=
  ((data.thinRectangle D (thinLookupBool_of_lookupBool hlookup)).compatibleBool &&
    (data.thickRectangle D (thickLookupBool_of_lookupBool hlookup)).compatibleBool) &&
      (data.blackRectangle D (blackLookupBool_of_lookupBool hlookup)).compatibleBool

theorem thinCompatibleBool_of_compatibleBool {w h : Nat}
    {D : Transcription} {data : CheckedLayerStackRectangle w h}
    {hlookup : data.lookupBool D = true}
    (hcheck : data.compatibleBool D hlookup = true) :
    (data.thinRectangle D (thinLookupBool_of_lookupBool hlookup)).compatibleBool =
      true := by
  rw [compatibleBool, Bool.and_eq_true, Bool.and_eq_true] at hcheck
  exact hcheck.1.1

theorem thickCompatibleBool_of_compatibleBool {w h : Nat}
    {D : Transcription} {data : CheckedLayerStackRectangle w h}
    {hlookup : data.lookupBool D = true}
    (hcheck : data.compatibleBool D hlookup = true) :
    (data.thickRectangle D (thickLookupBool_of_lookupBool hlookup)).compatibleBool =
      true := by
  rw [compatibleBool, Bool.and_eq_true, Bool.and_eq_true] at hcheck
  exact hcheck.1.2

theorem blackCompatibleBool_of_compatibleBool {w h : Nat}
    {D : Transcription} {data : CheckedLayerStackRectangle w h}
    {hlookup : data.lookupBool D = true}
    (hcheck : data.compatibleBool D hlookup = true) :
    (data.blackRectangle D (blackLookupBool_of_lookupBool hlookup)).compatibleBool =
      true := by
  rw [compatibleBool, Bool.and_eq_true] at hcheck
  exact hcheck.2

def toTypedLayerStackRectangle {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h)
    (hthinLookup : data.thinLookupBool D = true)
    (hthickLookup : data.thickLookupBool D = true)
    (hblackLookup : data.blackLookupBool D = true)
    (hthinCompatible : (data.thinRectangle D hthinLookup).compatibleBool = true)
    (hthickCompatible : (data.thickRectangle D hthickLookup).compatibleBool = true)
    (hblackCompatible : (data.blackRectangle D hblackLookup).compatibleBool = true) :
    TypedLayerStackRectangle D data.siteRectangle :=
  TypedLayerStackRectangle.ofCompatibleBool
    (data.thinRectangle D hthinLookup)
    (data.thickRectangle D hthickLookup)
    (data.blackRectangle D hblackLookup)
    hthinCompatible hthickCompatible hblackCompatible

@[simp]
theorem toTypedLayerStackRectangle_thin
    {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h)
    (hthinLookup : data.thinLookupBool D = true)
    (hthickLookup : data.thickLookupBool D = true)
    (hblackLookup : data.blackLookupBool D = true)
    (hthinCompatible : (data.thinRectangle D hthinLookup).compatibleBool = true)
    (hthickCompatible : (data.thickRectangle D hthickLookup).compatibleBool = true)
    (hblackCompatible : (data.blackRectangle D hblackLookup).compatibleBool = true) :
    (data.toTypedLayerStackRectangle D hthinLookup hthickLookup hblackLookup
      hthinCompatible hthickCompatible hblackCompatible).thin =
      data.thinRectangle D hthinLookup :=
  rfl

@[simp]
theorem toTypedLayerStackRectangle_thick
    {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h)
    (hthinLookup : data.thinLookupBool D = true)
    (hthickLookup : data.thickLookupBool D = true)
    (hblackLookup : data.blackLookupBool D = true)
    (hthinCompatible : (data.thinRectangle D hthinLookup).compatibleBool = true)
    (hthickCompatible : (data.thickRectangle D hthickLookup).compatibleBool = true)
    (hblackCompatible : (data.blackRectangle D hblackLookup).compatibleBool = true) :
    (data.toTypedLayerStackRectangle D hthinLookup hthickLookup hblackLookup
      hthinCompatible hthickCompatible hblackCompatible).thick =
      data.thickRectangle D hthickLookup :=
  rfl

@[simp]
theorem toTypedLayerStackRectangle_black
    {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h)
    (hthinLookup : data.thinLookupBool D = true)
    (hthickLookup : data.thickLookupBool D = true)
    (hblackLookup : data.blackLookupBool D = true)
    (hthinCompatible : (data.thinRectangle D hthinLookup).compatibleBool = true)
    (hthickCompatible : (data.thickRectangle D hthickLookup).compatibleBool = true)
    (hblackCompatible : (data.blackRectangle D hblackLookup).compatibleBool = true) :
    (data.toTypedLayerStackRectangle D hthinLookup hthickLookup hblackLookup
      hthinCompatible hthickCompatible hblackCompatible).black =
      data.blackRectangle D hblackLookup :=
  rfl

def toTypedLayerStackRectangleOfChecks {w h : Nat}
    (D : Transcription) (data : CheckedLayerStackRectangle w h)
    (hlookup : data.lookupBool D = true)
    (hcompatible : data.compatibleBool D hlookup = true) :
    TypedLayerStackRectangle D data.siteRectangle :=
  data.toTypedLayerStackRectangle D
    (thinLookupBool_of_lookupBool hlookup)
    (thickLookupBool_of_lookupBool hlookup)
    (blackLookupBool_of_lookupBool hlookup)
    (thinCompatibleBool_of_compatibleBool hcompatible)
    (thickCompatibleBool_of_compatibleBool hcompatible)
    (blackCompatibleBool_of_compatibleBool hcompatible)

end CheckedLayerStackRectangle

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

namespace Figure18IndexedActiveCornerWindowWithLayerStack

def ofTyped
    {D : Transcription} {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (layerStack : TypedLayerStackRectangle D
      (siteRectangleOfIndexedActiveCornerWindow window)) :
    Figure18IndexedActiveCornerWindowWithLayerStack D table x n hn where
  window := window
  layerStack := layerStack.toLayerStackRectangle

@[simp]
theorem ofTyped_window
    {D : Transcription} {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (layerStack : TypedLayerStackRectangle D
      (siteRectangleOfIndexedActiveCornerWindow window)) :
    (ofTyped window layerStack).window = window :=
  rfl

def ofChecked
    {D : Transcription} {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (data : CheckedLayerStackRectangle n n)
    (hsite : data.sites.matchesSiteRectangleBool
      (siteRectangleOfIndexedActiveCornerWindow window) = true)
    (hlookup : data.lookupBool D = true)
    (hcompatible : data.compatibleBool D hlookup = true) :
    Figure18IndexedActiveCornerWindowWithLayerStack D table x n hn where
  window := window
  layerStack := by
    have hsiteEq :
        data.siteRectangle = siteRectangleOfIndexedActiveCornerWindow window :=
      CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool hsite
    change LayerStackRectangle D (siteRectangleOfIndexedActiveCornerWindow window)
    rw [← hsiteEq]
    exact (data.toTypedLayerStackRectangleOfChecks D hlookup hcompatible).toLayerStackRectangle

@[simp]
theorem ofChecked_window
    {D : Transcription} {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (data : CheckedLayerStackRectangle n n)
    (hsite : data.sites.matchesSiteRectangleBool
      (siteRectangleOfIndexedActiveCornerWindow window) = true)
    (hlookup : data.lookupBool D = true)
    (hcompatible : data.compatibleBool D hlookup = true) :
    (ofChecked window data hsite hlookup hcompatible).window = window :=
  rfl

end Figure18IndexedActiveCornerWindowWithLayerStack

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

namespace Figure18IndexedRoutedFixedCornerSquareWithLayerStack

def ofTyped
    {D : Transcription} {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (layerStack : TypedLayerStackRectangle D
      (siteRectangleOfIndexedRoutedFixedCornerSquare window)) :
    Figure18IndexedRoutedFixedCornerSquareWithLayerStack D table x n hn where
  window := window
  layerStack := layerStack.toLayerStackRectangle

@[simp]
theorem ofTyped_window
    {D : Transcription} {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (layerStack : TypedLayerStackRectangle D
      (siteRectangleOfIndexedRoutedFixedCornerSquare window)) :
    (ofTyped window layerStack).window = window :=
  rfl

def ofChecked
    {D : Transcription} {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (data : CheckedLayerStackRectangle n n)
    (hsite : data.sites.matchesSiteRectangleBool
      (siteRectangleOfIndexedRoutedFixedCornerSquare window) = true)
    (hlookup : data.lookupBool D = true)
    (hcompatible : data.compatibleBool D hlookup = true) :
    Figure18IndexedRoutedFixedCornerSquareWithLayerStack D table x n hn where
  window := window
  layerStack := by
    have hsiteEq :
        data.siteRectangle = siteRectangleOfIndexedRoutedFixedCornerSquare window :=
      CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool hsite
    change LayerStackRectangle D (siteRectangleOfIndexedRoutedFixedCornerSquare window)
    rw [← hsiteEq]
    exact (data.toTypedLayerStackRectangleOfChecks D hlookup hcompatible).toLayerStackRectangle

@[simp]
theorem ofChecked_window
    {D : Transcription} {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (data : CheckedLayerStackRectangle n n)
    (hsite : data.sites.matchesSiteRectangleBool
      (siteRectangleOfIndexedRoutedFixedCornerSquare window) = true)
    (hlookup : data.lookupBool D = true)
    (hcompatible : data.compatibleBool D hlookup = true) :
    (ofChecked window data hsite hlookup hcompatible).window = window :=
  rfl

end Figure18IndexedRoutedFixedCornerSquareWithLayerStack

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

/--
Concrete Figure 18 scaffold data together with the 92-row Figure 13 layer
transcription.

This is the combined Lean target for the Ollinger/Robinson scaffold
instantiation: `scaffoldData` records the checked active quarter-sites and
corner, while `layerData` records the Figure 13 decomposition into the Figure
16 layer components.
-/
structure LayeredFigure18ScaffoldData where
  layerData : Transcription
  scaffoldData : Figure18ScaffoldData

namespace LayeredFigure18ScaffoldData

def activeSiteData (D : LayeredFigure18ScaffoldData) :
    Figure18Site.CheckedNatSpecs :=
  D.scaffoldData.activeSiteData

def activeSites (D : LayeredFigure18ScaffoldData) : List Figure18Site :=
  D.scaffoldData.activeSites

def cornerSite (D : LayeredFigure18ScaffoldData) : Figure18Site :=
  D.scaffoldData.cornerSite

def flatTable (D : LayeredFigure18ScaffoldData) :
    Figure18RoleTable.FlatRoleTable :=
  D.scaffoldData.table

def table (D : LayeredFigure18ScaffoldData) : Figure18RoleTable :=
  D.flatTable.toRoleTable

def finite (D : LayeredFigure18ScaffoldData) :
    FiniteCheckedTranscription :=
  D.table.finiteCheckedTranscription

def presentation (D : LayeredFigure18ScaffoldData) :
    ScaffoldPresentation :=
  D.table.presentation

def scaffold (D : LayeredFigure18ScaffoldData) : Scaffold :=
  D.presentation.toScaffold

theorem activeSites_eq (D : LayeredFigure18ScaffoldData) :
    D.activeSites = D.activeSiteData.sites :=
  rfl

@[simp]
theorem flatTable_cornerSite (D : LayeredFigure18ScaffoldData) :
    D.flatTable.cornerSite = D.cornerSite :=
  rfl

theorem presentation_tiles (D : LayeredFigure18ScaffoldData) :
    D.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles := by
  simpa [presentation, table, flatTable, Figure18ScaffoldData.presentation,
    Figure18ScaffoldData.table, figure18ScaffoldTiles] using
    D.scaffoldData.presentation_tiles

theorem scaffold_tiles (D : LayeredFigure18ScaffoldData) :
    D.scaffold.tiles = TileSubdivision.subdivideTileSet fig13Tiles := by
  simpa [scaffold] using D.presentation_tiles

/--
Checked raw input for the concrete layered Figure 18 scaffold data.

This is the compact data-entry shape for the final transcription: `layerRows`
is the 92-row Figure 13 layer decomposition, `activeSiteSpecs` is the finite
list of active Figure 18 quarter-sites, and `cornerIndex`/`cornerQuadrant`
select the distinguished lower-left corner site.
-/
structure CheckedRawData where
  layerRows : List Components
  layerRows_length : layerRows.length = 92
  activeSiteSpecs : List (Nat × Quadrant)
  activeSiteSpecs_valid :
    Figure18Site.natSpecsValidBool activeSiteSpecs = true
  cornerIndex : Nat
  cornerQuadrant : Quadrant
  cornerIndex_valid : decide (cornerIndex < 92) = true

namespace CheckedRawData

def layerData (data : CheckedRawData) : Transcription where
  rows := data.layerRows
  length_eq := data.layerRows_length

def activeSiteData (data : CheckedRawData) :
    Figure18Site.CheckedNatSpecs where
  specs := data.activeSiteSpecs
  valid := data.activeSiteSpecs_valid

theorem cornerIndex_lt (data : CheckedRawData) :
    data.cornerIndex < 92 :=
  of_decide_eq_true data.cornerIndex_valid

def cornerSite (data : CheckedRawData) : Figure18Site where
  index := ⟨data.cornerIndex, data.cornerIndex_lt⟩
  quadrant := data.cornerQuadrant

def scaffoldData (data : CheckedRawData) : Figure18ScaffoldData where
  activeSiteData := data.activeSiteData
  cornerSite := data.cornerSite

def toLayeredFigure18ScaffoldData (data : CheckedRawData) :
    LayeredFigure18ScaffoldData where
  layerData := data.layerData
  scaffoldData := data.scaffoldData

@[simp]
theorem toLayeredFigure18ScaffoldData_layerData
    (data : CheckedRawData) :
    data.toLayeredFigure18ScaffoldData.layerData = data.layerData :=
  rfl

@[simp]
theorem toLayeredFigure18ScaffoldData_scaffoldData
    (data : CheckedRawData) :
    data.toLayeredFigure18ScaffoldData.scaffoldData = data.scaffoldData :=
  rfl

@[simp]
theorem toLayeredFigure18ScaffoldData_activeSiteData
    (data : CheckedRawData) :
    data.toLayeredFigure18ScaffoldData.activeSiteData =
      data.activeSiteData :=
  rfl

@[simp]
theorem toLayeredFigure18ScaffoldData_cornerSite
    (data : CheckedRawData) :
    data.toLayeredFigure18ScaffoldData.cornerSite = data.cornerSite :=
  rfl

theorem layerData_rows (data : CheckedRawData) :
    data.layerData.rows = data.layerRows :=
  rfl

theorem activeSiteData_specs (data : CheckedRawData) :
    data.activeSiteData.specs = data.activeSiteSpecs :=
  rfl

theorem cornerSite_index_val (data : CheckedRawData) :
    data.cornerSite.index.val = data.cornerIndex :=
  rfl

theorem cornerSite_quadrant (data : CheckedRawData) :
    data.cornerSite.quadrant = data.cornerQuadrant :=
  rfl

end CheckedRawData

/--
Zip three separately transcribed Figure 16 layer rows into Figure 13 component
rows.  This is intentionally truncating like `List.zip`: the checked wrapper
below supplies equal 92-entry lengths before the result is used as raw data.
-/
def zipComponentRows :
    List (Option Figure16.Thin) → List (Option Figure16.Thick) →
      List (Option Figure16.Black) → List Components
  | thin :: thins, thick :: thicks, black :: blacks =>
      Components.ofOptions thin thick black ::
        zipComponentRows thins thicks blacks
  | _, _, _ => []

theorem zipComponentRows_getElem?_eq_some_of_getElem?
    {thins : List (Option Figure16.Thin)}
    {thicks : List (Option Figure16.Thick)}
    {blacks : List (Option Figure16.Black)}
    {i : Nat}
    {thin : Option Figure16.Thin}
    {thick : Option Figure16.Thick}
    {black : Option Figure16.Black}
    (hthin : thins[i]? = some thin)
    (hthick : thicks[i]? = some thick)
    (hblack : blacks[i]? = some black) :
    (zipComponentRows thins thicks blacks)[i]? =
      some (Components.ofOptions thin thick black) := by
  revert thicks blacks i
  induction thins with
  | nil =>
      intro thicks blacks i hthin hthick hblack
      cases i <;> cases hthin
  | cons thinHead thins ih =>
      intro thicks blacks i hthin hthick hblack
      cases thicks with
      | nil =>
          cases i <;> cases hthick
      | cons thickHead thicks =>
          cases blacks with
          | nil =>
              cases i <;> cases hblack
          | cons blackHead blacks =>
              cases i with
              | zero =>
                  cases hthin
                  cases hthick
                  cases hblack
                  rfl
              | succ i =>
                  exact ih hthin hthick hblack

theorem zipComponentRows_length_of_lengths
    {thins : List (Option Figure16.Thin)}
    {thicks : List (Option Figure16.Thick)}
    {blacks : List (Option Figure16.Black)}
    {n : Nat}
    (hthin : thins.length = n)
    (hthick : thicks.length = n)
    (hblack : blacks.length = n) :
    (zipComponentRows thins thicks blacks).length = n := by
  revert thicks blacks n
  induction thins with
  | nil =>
      intro thicks blacks n hthin hthick hblack
      cases n
      · rfl
      · simp at hthin
  | cons thin thins ih =>
      intro thicks blacks n hthin hthick hblack
      cases thicks with
      | nil =>
          cases n
          · simp at hthin
          · simp at hthick
      | cons thick thicks =>
          cases blacks with
          | nil =>
              cases n
              · simp at hthin
              · simp at hblack
          | cons black blacks =>
              cases n
              case zero =>
                simp at hthin
              case succ n =>
                change
                  (Components.ofOptions thin thick black ::
                    zipComponentRows thins thicks blacks).length =
                      Nat.succ n
                rw [List.length_cons]
                exact congrArg Nat.succ
                  (ih (Nat.succ.inj hthin) (Nat.succ.inj hthick)
                    (Nat.succ.inj hblack))

def sparseEntriesValidBool {α : Type} (entries : List (Nat × α)) : Bool :=
  entries.all (fun entry => decide (entry.1 < 92)) &&
    decide (entries.map Prod.fst).Nodup

theorem all_indices_lt_of_sparseEntriesValidBool
    {α : Type} {entries : List (Nat × α)}
    (hvalid : sparseEntriesValidBool entries = true) :
    ∀ entry ∈ entries, entry.1 < 92 := by
  rw [sparseEntriesValidBool, Bool.and_eq_true] at hvalid
  intro entry hentry
  exact of_decide_eq_true (List.all_eq_true.1 hvalid.1 entry hentry)

theorem indices_nodup_of_sparseEntriesValidBool
    {α : Type} {entries : List (Nat × α)}
    (hvalid : sparseEntriesValidBool entries = true) :
    (entries.map Prod.fst).Nodup := by
  rw [sparseEntriesValidBool, Bool.and_eq_true] at hvalid
  exact of_decide_eq_true hvalid.2

def optionFromSparseEntries {α : Type} (entries : List (Nat × α))
    (index : Nat) : Option α :=
  (entries.find? fun entry => entry.1 == index).map Prod.snd

def optionRowFromSparseEntries {α : Type}
    (entries : List (Nat × α)) : List (Option α) :=
  (List.range 92).map (optionFromSparseEntries entries)

@[simp]
theorem optionRowFromSparseEntries_length {α : Type}
    (entries : List (Nat × α)) :
    (optionRowFromSparseEntries entries).length = 92 := by
  simp [optionRowFromSparseEntries]

/--
Sparse entry form for the final Figure 13 layer transcription.

Each list names only the raw Figure 13 tile indices carrying a component in
that layer.  The finite checks rule out out-of-range and duplicate indices
before expanding to the 92-entry option rows consumed by
`CheckedSeparateLayerRows`.
-/
structure CheckedSparseSeparateLayerRows where
  thinEntries : List (Nat × Figure16.Thin)
  thinEntries_valid : sparseEntriesValidBool thinEntries = true
  thickEntries : List (Nat × Figure16.Thick)
  thickEntries_valid : sparseEntriesValidBool thickEntries = true
  blackEntries : List (Nat × Figure16.Black)
  blackEntries_valid : sparseEntriesValidBool blackEntries = true

namespace CheckedSparseSeparateLayerRows

def thins (rows : CheckedSparseSeparateLayerRows) :
    List (Option Figure16.Thin) :=
  optionRowFromSparseEntries rows.thinEntries

def thicks (rows : CheckedSparseSeparateLayerRows) :
    List (Option Figure16.Thick) :=
  optionRowFromSparseEntries rows.thickEntries

def blacks (rows : CheckedSparseSeparateLayerRows) :
    List (Option Figure16.Black) :=
  optionRowFromSparseEntries rows.blackEntries

@[simp]
theorem thins_length (rows : CheckedSparseSeparateLayerRows) :
    rows.thins.length = 92 := by
  simp [thins]

@[simp]
theorem thicks_length (rows : CheckedSparseSeparateLayerRows) :
    rows.thicks.length = 92 := by
  simp [thicks]

@[simp]
theorem blacks_length (rows : CheckedSparseSeparateLayerRows) :
    rows.blacks.length = 92 := by
  simp [blacks]

theorem thinIndices_nodup (rows : CheckedSparseSeparateLayerRows) :
    (rows.thinEntries.map Prod.fst).Nodup :=
  indices_nodup_of_sparseEntriesValidBool rows.thinEntries_valid

theorem thickIndices_nodup (rows : CheckedSparseSeparateLayerRows) :
    (rows.thickEntries.map Prod.fst).Nodup :=
  indices_nodup_of_sparseEntriesValidBool rows.thickEntries_valid

theorem blackIndices_nodup (rows : CheckedSparseSeparateLayerRows) :
    (rows.blackEntries.map Prod.fst).Nodup :=
  indices_nodup_of_sparseEntriesValidBool rows.blackEntries_valid

end CheckedSparseSeparateLayerRows

/--
Checked Figure 13 layer transcription entered as three separate 92-entry layer
lists.  This is the Lean data-entry form closest to Figure 16: first transcribe
the thin `L1` labels, then the thick `L2` labels, then the black `L3` labels.
-/
structure CheckedSeparateLayerRows where
  thins : List (Option Figure16.Thin)
  thins_length : thins.length = 92
  thicks : List (Option Figure16.Thick)
  thicks_length : thicks.length = 92
  blacks : List (Option Figure16.Black)
  blacks_length : blacks.length = 92

namespace CheckedSeparateLayerRows

def ofSparse (rows : CheckedSparseSeparateLayerRows) :
    CheckedSeparateLayerRows where
  thins := rows.thins
  thins_length := rows.thins_length
  thicks := rows.thicks
  thicks_length := rows.thicks_length
  blacks := rows.blacks
  blacks_length := rows.blacks_length

def thinAt (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    Option Figure16.Thin :=
  rows.thins.get ⟨index.val, by simp [rows.thins_length, index.isLt]⟩

def thickAt (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    Option Figure16.Thick :=
  rows.thicks.get ⟨index.val, by simp [rows.thicks_length, index.isLt]⟩

def blackAt (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    Option Figure16.Black :=
  rows.blacks.get ⟨index.val, by simp [rows.blacks_length, index.isLt]⟩

def componentAt (rows : CheckedSeparateLayerRows) :
    (layer : Layer) → Fin 92 → Option layer.Component
  | .thin, index => rows.thinAt index
  | .thick, index => rows.thickAt index
  | .black, index => rows.blackAt index

def layerRows (rows : CheckedSeparateLayerRows) : List Components :=
  zipComponentRows rows.thins rows.thicks rows.blacks

@[simp]
theorem layerRows_length (rows : CheckedSeparateLayerRows) :
    rows.layerRows.length = 92 :=
  zipComponentRows_length_of_lengths rows.thins_length rows.thicks_length
    rows.blacks_length

def layerData (rows : CheckedSeparateLayerRows) : Transcription where
  rows := rows.layerRows
  length_eq := rows.layerRows_length

@[simp]
theorem layerData_rows (rows : CheckedSeparateLayerRows) :
    rows.layerData.rows = rows.layerRows :=
  rfl

theorem thins_getElem?_thinAt
    (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    rows.thins[index.val]? = some (rows.thinAt index) := by
  unfold thinAt
  exact List.getElem?_eq_getElem (by simp [rows.thins_length, index.isLt])

theorem thicks_getElem?_thickAt
    (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    rows.thicks[index.val]? = some (rows.thickAt index) := by
  unfold thickAt
  exact List.getElem?_eq_getElem (by simp [rows.thicks_length, index.isLt])

theorem blacks_getElem?_blackAt
    (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    rows.blacks[index.val]? = some (rows.blackAt index) := by
  unfold blackAt
  exact List.getElem?_eq_getElem (by simp [rows.blacks_length, index.isLt])

theorem layerRows_getElem?_components
    (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    rows.layerRows[index.val]? =
      some (Components.ofOptions (rows.thinAt index) (rows.thickAt index)
        (rows.blackAt index)) :=
  zipComponentRows_getElem?_eq_some_of_getElem?
    (rows.thins_getElem?_thinAt index)
    (rows.thicks_getElem?_thickAt index)
    (rows.blacks_getElem?_blackAt index)

theorem layerData_componentsAt
    (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    rows.layerData.componentsAt index =
      Components.ofOptions (rows.thinAt index) (rows.thickAt index)
        (rows.blackAt index) := by
  have hcomponents := rows.layerData.rows_getElem?_componentsAt index
  rw [layerData_rows, rows.layerRows_getElem?_components] at hcomponents
  exact (Option.some.inj hcomponents).symm

@[simp]
theorem layerData_componentsAt_thin
    (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    (rows.layerData.componentsAt index).thin = rows.thinAt index := by
  rw [rows.layerData_componentsAt]
  rfl

@[simp]
theorem layerData_componentsAt_thick
    (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    (rows.layerData.componentsAt index).thick = rows.thickAt index := by
  rw [rows.layerData_componentsAt]
  rfl

@[simp]
theorem layerData_componentsAt_black
    (rows : CheckedSeparateLayerRows) (index : Fin 92) :
    (rows.layerData.componentsAt index).black = rows.blackAt index := by
  rw [rows.layerData_componentsAt]
  rfl

theorem layerData_componentAtLayerAt_thin
    {rows : CheckedSeparateLayerRows} {index : Fin 92}
    {thin : Figure16.Thin}
    (hthin : rows.thinAt index = some thin) :
    rows.layerData.componentAtLayerAt index .thin =
      some (LayerComponent.thin thin) := by
  simp [Transcription.componentAtLayerAt, Components.componentAtLayer, hthin]

theorem layerData_componentAtLayerAt_thick
    {rows : CheckedSeparateLayerRows} {index : Fin 92}
    {thick : Figure16.Thick}
    (hthick : rows.thickAt index = some thick) :
    rows.layerData.componentAtLayerAt index .thick =
      some (LayerComponent.thick thick) := by
  simp [Transcription.componentAtLayerAt, Components.componentAtLayer, hthick]

theorem layerData_componentAtLayerAt_black
    {rows : CheckedSeparateLayerRows} {index : Fin 92}
    {black : Figure16.Black}
    (hblack : rows.blackAt index = some black) :
    rows.layerData.componentAtLayerAt index .black =
      some (LayerComponent.black black) := by
  simp [Transcription.componentAtLayerAt, Components.componentAtLayer, hblack]

theorem layerData_componentAtLayerAt
    {rows : CheckedSeparateLayerRows} {layer : Layer} {index : Fin 92}
    {component : layer.Component}
    (hcomponent : rows.componentAt layer index = some component) :
    rows.layerData.componentAtLayerAt index layer =
      some (LayerComponent.ofLayer layer component) := by
  cases layer with
  | thin =>
      exact rows.layerData_componentAtLayerAt_thin hcomponent
  | thick =>
      exact rows.layerData_componentAtLayerAt_thick hcomponent
  | black =>
      exact rows.layerData_componentAtLayerAt_black hcomponent

theorem layerData_componentAtSiteLayer_thin
    {rows : CheckedSeparateLayerRows} {site : Figure18Site}
    {thin : Figure16.Thin}
    (hthin : rows.thinAt site.index = some thin) :
    rows.layerData.componentAtSiteLayer site .thin =
      some (LayerComponent.thin thin) :=
  rows.layerData_componentAtLayerAt_thin hthin

theorem layerData_componentAtSiteLayer_thick
    {rows : CheckedSeparateLayerRows} {site : Figure18Site}
    {thick : Figure16.Thick}
    (hthick : rows.thickAt site.index = some thick) :
    rows.layerData.componentAtSiteLayer site .thick =
      some (LayerComponent.thick thick) :=
  rows.layerData_componentAtLayerAt_thick hthick

theorem layerData_componentAtSiteLayer_black
    {rows : CheckedSeparateLayerRows} {site : Figure18Site}
    {black : Figure16.Black}
    (hblack : rows.blackAt site.index = some black) :
    rows.layerData.componentAtSiteLayer site .black =
      some (LayerComponent.black black) :=
  rows.layerData_componentAtLayerAt_black hblack

theorem layerData_componentAtSiteLayer
    {rows : CheckedSeparateLayerRows} {layer : Layer} {site : Figure18Site}
    {component : layer.Component}
    (hcomponent : rows.componentAt layer site.index = some component) :
    rows.layerData.componentAtSiteLayer site layer =
      some (LayerComponent.ofLayer layer component) :=
  rows.layerData_componentAtLayerAt hcomponent

def toCheckedRawData
    (rows : CheckedSeparateLayerRows)
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    CheckedRawData where
  layerRows := rows.layerRows
  layerRows_length := rows.layerRows_length
  activeSiteSpecs := activeSiteSpecs
  activeSiteSpecs_valid := activeSiteSpecs_valid
  cornerIndex := cornerIndex
  cornerQuadrant := cornerQuadrant
  cornerIndex_valid := cornerIndex_valid

@[simp]
theorem toCheckedRawData_layerRows
    (rows : CheckedSeparateLayerRows)
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (rows.toCheckedRawData activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).layerRows =
        rows.layerRows :=
  rfl

end CheckedSeparateLayerRows

/--
Checked raw Figure 18 scaffold data whose Figure 13 layer transcription is
entered sparsely.

This is the intended data-entry shape for the final concrete scaffold: the
layer rows name only occupied Figure 16 components, while the active sites and
corner are the finite Figure 18 scaffold data.
-/
structure CheckedSparseRawData where
  layerRows : CheckedSparseSeparateLayerRows
  activeSiteSpecs : List (Nat × Quadrant)
  activeSiteSpecs_valid :
    Figure18Site.natSpecsValidBool activeSiteSpecs = true
  cornerIndex : Nat
  cornerQuadrant : Quadrant
  cornerIndex_valid : decide (cornerIndex < 92) = true

namespace CheckedSparseRawData

def separateLayerRows (data : CheckedSparseRawData) :
    CheckedSeparateLayerRows :=
  CheckedSeparateLayerRows.ofSparse data.layerRows

def toCheckedRawData (data : CheckedSparseRawData) : CheckedRawData :=
  data.separateLayerRows.toCheckedRawData data.activeSiteSpecs
    data.activeSiteSpecs_valid data.cornerIndex data.cornerQuadrant
    data.cornerIndex_valid

def layerData (data : CheckedSparseRawData) : Transcription :=
  data.toCheckedRawData.layerData

def activeSiteData (data : CheckedSparseRawData) :
    Figure18Site.CheckedNatSpecs :=
  data.toCheckedRawData.activeSiteData

def cornerSite (data : CheckedSparseRawData) : Figure18Site :=
  data.toCheckedRawData.cornerSite

def toLayeredFigure18ScaffoldData (data : CheckedSparseRawData) :
    LayeredFigure18ScaffoldData :=
  data.toCheckedRawData.toLayeredFigure18ScaffoldData

@[simp]
theorem toCheckedRawData_layerRows (data : CheckedSparseRawData) :
    data.toCheckedRawData.layerRows = data.separateLayerRows.layerRows :=
  rfl

@[simp]
theorem toCheckedRawData_activeSiteSpecs (data : CheckedSparseRawData) :
    data.toCheckedRawData.activeSiteSpecs = data.activeSiteSpecs :=
  rfl

@[simp]
theorem toCheckedRawData_cornerIndex (data : CheckedSparseRawData) :
    data.toCheckedRawData.cornerIndex = data.cornerIndex :=
  rfl

@[simp]
theorem toCheckedRawData_cornerQuadrant (data : CheckedSparseRawData) :
    data.toCheckedRawData.cornerQuadrant = data.cornerQuadrant :=
  rfl

@[simp]
theorem toLayeredFigure18ScaffoldData_eq (data : CheckedSparseRawData) :
    data.toLayeredFigure18ScaffoldData =
      data.toCheckedRawData.toLayeredFigure18ScaffoldData :=
  rfl

end CheckedSparseRawData

namespace CheckedSeparateLayerRows

/--
Finite check that a component rectangle agrees with separately transcribed
Figure 13 layer rows at the corresponding Figure 18 site indices.
-/
def componentRectangleMatchesBool
    {w h : Nat} (rows : CheckedSeparateLayerRows) {layer : Layer}
    (siteData : CheckedNatSiteRectangle w h)
    (data : CheckedLayerComponentRectangle w h layer) : Bool :=
  (List.finRange w).all fun i =>
    (List.finRange h).all fun j =>
      match layer with
      | .thin =>
          decide <| rows.thinAt (siteData.toSiteRectangle i j).index =
            some (data.componentAt i j)
      | .thick =>
          decide <| rows.thickAt (siteData.toSiteRectangle i j).index =
            some (data.componentAt i j)
      | .black =>
          decide <| rows.blackAt (siteData.toSiteRectangle i j).index =
            some (data.componentAt i j)

theorem componentAt_matchesSeparateRows_of_bool
    {w h : Nat} {layer : Layer}
    {rows : CheckedSeparateLayerRows}
    {siteData : CheckedNatSiteRectangle w h}
    {data : CheckedLayerComponentRectangle w h layer}
    (hcheck : rows.componentRectangleMatchesBool siteData data = true) :
    ∀ i : Fin w, ∀ j : Fin h,
      rows.componentAt layer (siteData.toSiteRectangle i j).index =
        some (data.componentAt i j) := by
  intro i j
  unfold componentRectangleMatchesBool at hcheck
  have hiCheck := List.all_eq_true.1 hcheck i (List.mem_finRange i)
  have hjCheck := List.all_eq_true.1 hiCheck j (List.mem_finRange j)
  cases layer with
  | thin =>
      change rows.thinAt (siteData.toSiteRectangle i j).index =
        some (data.componentAt i j)
      exact of_decide_eq_true hjCheck
  | thick =>
      change rows.thickAt (siteData.toSiteRectangle i j).index =
        some (data.componentAt i j)
      exact of_decide_eq_true hjCheck
  | black =>
      change rows.blackAt (siteData.toSiteRectangle i j).index =
        some (data.componentAt i j)
      exact of_decide_eq_true hjCheck

theorem lookupBool_layerData_of_matchesSeparateRowsBool
    {w h : Nat} {layer : Layer}
    {rows : CheckedSeparateLayerRows}
    {siteData : CheckedNatSiteRectangle w h}
    {data : CheckedLayerComponentRectangle w h layer}
    (hcheck : rows.componentRectangleMatchesBool siteData data = true) :
    data.lookupBool rows.layerData siteData = true :=
  CheckedLayerComponentRectangle.lookupBool_of_lookup fun i j =>
    rows.layerData_componentAtSiteLayer
      (componentAt_matchesSeparateRows_of_bool hcheck i j)

def layerStackRectangleMatchesBool
    {w h : Nat} (rows : CheckedSeparateLayerRows)
    (data : CheckedLayerStackRectangle w h) : Bool :=
  (rows.componentRectangleMatchesBool data.sites data.thin &&
    rows.componentRectangleMatchesBool data.sites data.thick) &&
      rows.componentRectangleMatchesBool data.sites data.black

theorem thinComponentRectangleMatchesBool_of_layerStack
    {w h : Nat} {rows : CheckedSeparateLayerRows}
    {data : CheckedLayerStackRectangle w h}
    (hcheck : rows.layerStackRectangleMatchesBool data = true) :
    rows.componentRectangleMatchesBool data.sites data.thin = true := by
  rw [layerStackRectangleMatchesBool, Bool.and_eq_true,
    Bool.and_eq_true] at hcheck
  exact hcheck.1.1

theorem thickComponentRectangleMatchesBool_of_layerStack
    {w h : Nat} {rows : CheckedSeparateLayerRows}
    {data : CheckedLayerStackRectangle w h}
    (hcheck : rows.layerStackRectangleMatchesBool data = true) :
    rows.componentRectangleMatchesBool data.sites data.thick = true := by
  rw [layerStackRectangleMatchesBool, Bool.and_eq_true,
    Bool.and_eq_true] at hcheck
  exact hcheck.1.2

theorem blackComponentRectangleMatchesBool_of_layerStack
    {w h : Nat} {rows : CheckedSeparateLayerRows}
    {data : CheckedLayerStackRectangle w h}
    (hcheck : rows.layerStackRectangleMatchesBool data = true) :
    rows.componentRectangleMatchesBool data.sites data.black = true := by
  rw [layerStackRectangleMatchesBool, Bool.and_eq_true] at hcheck
  exact hcheck.2

theorem lookupBool_layerData_of_layerStackRectangleMatchesBool
    {w h : Nat} {rows : CheckedSeparateLayerRows}
    {data : CheckedLayerStackRectangle w h}
    (hcheck : rows.layerStackRectangleMatchesBool data = true) :
    data.lookupBool rows.layerData = true :=
  CheckedLayerStackRectangle.lookupBool_of_layer_lookups
    (lookupBool_layerData_of_matchesSeparateRowsBool
      (thinComponentRectangleMatchesBool_of_layerStack hcheck))
    (lookupBool_layerData_of_matchesSeparateRowsBool
      (thickComponentRectangleMatchesBool_of_layerStack hcheck))
    (lookupBool_layerData_of_matchesSeparateRowsBool
      (blackComponentRectangleMatchesBool_of_layerStack hcheck))

def toTypedLayerStackRectangleOfSeparateRows {w h : Nat}
    (rows : CheckedSeparateLayerRows) (data : CheckedLayerStackRectangle w h)
    (hmatch : rows.layerStackRectangleMatchesBool data = true)
    (hcompatible :
      data.compatibleBool rows.layerData
        (lookupBool_layerData_of_layerStackRectangleMatchesBool hmatch) =
          true) :
    TypedLayerStackRectangle rows.layerData data.siteRectangle :=
  data.toTypedLayerStackRectangleOfChecks rows.layerData
    (lookupBool_layerData_of_layerStackRectangleMatchesBool hmatch)
    hcompatible

def toIndexedActiveCornerWindowWithLayerStack
    (rows : CheckedSeparateLayerRows)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (data : CheckedLayerStackRectangle n n)
    (hsite : data.sites.matchesSiteRectangleBool
      (siteRectangleOfIndexedActiveCornerWindow window) = true)
    (hmatch : rows.layerStackRectangleMatchesBool data = true)
    (hcompatible :
      data.compatibleBool rows.layerData
        (lookupBool_layerData_of_layerStackRectangleMatchesBool hmatch) =
          true) :
    Figure18IndexedActiveCornerWindowWithLayerStack rows.layerData table x n hn where
  window := window
  layerStack := by
    have hsiteEq :
        data.siteRectangle = siteRectangleOfIndexedActiveCornerWindow window :=
      CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool hsite
    change LayerStackRectangle rows.layerData
      (siteRectangleOfIndexedActiveCornerWindow window)
    rw [← hsiteEq]
    exact (rows.toTypedLayerStackRectangleOfSeparateRows data hmatch
      hcompatible).toLayerStackRectangle

@[simp]
theorem toIndexedActiveCornerWindowWithLayerStack_window
    (rows : CheckedSeparateLayerRows)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (data : CheckedLayerStackRectangle n n)
    (hsite : data.sites.matchesSiteRectangleBool
      (siteRectangleOfIndexedActiveCornerWindow window) = true)
    (hmatch : rows.layerStackRectangleMatchesBool data = true)
    (hcompatible :
      data.compatibleBool rows.layerData
        (lookupBool_layerData_of_layerStackRectangleMatchesBool hmatch) =
          true) :
    (rows.toIndexedActiveCornerWindowWithLayerStack window data hsite hmatch
      hcompatible).window = window :=
  rfl

def toIndexedRoutedFixedCornerSquareWithLayerStack
    (rows : CheckedSeparateLayerRows)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (data : CheckedLayerStackRectangle n n)
    (hsite : data.sites.matchesSiteRectangleBool
      (siteRectangleOfIndexedRoutedFixedCornerSquare window) = true)
    (hmatch : rows.layerStackRectangleMatchesBool data = true)
    (hcompatible :
      data.compatibleBool rows.layerData
        (lookupBool_layerData_of_layerStackRectangleMatchesBool hmatch) =
          true) :
    Figure18IndexedRoutedFixedCornerSquareWithLayerStack
      rows.layerData table x n hn where
  window := window
  layerStack := by
    have hsiteEq :
        data.siteRectangle = siteRectangleOfIndexedRoutedFixedCornerSquare window :=
      CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool hsite
    change LayerStackRectangle rows.layerData
      (siteRectangleOfIndexedRoutedFixedCornerSquare window)
    rw [← hsiteEq]
    exact (rows.toTypedLayerStackRectangleOfSeparateRows data hmatch
      hcompatible).toLayerStackRectangle

@[simp]
theorem toIndexedRoutedFixedCornerSquareWithLayerStack_window
    (rows : CheckedSeparateLayerRows)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (data : CheckedLayerStackRectangle n n)
    (hsite : data.sites.matchesSiteRectangleBool
      (siteRectangleOfIndexedRoutedFixedCornerSquare window) = true)
    (hmatch : rows.layerStackRectangleMatchesBool data = true)
    (hcompatible :
      data.compatibleBool rows.layerData
        (lookupBool_layerData_of_layerStackRectangleMatchesBool hmatch) =
          true) :
    (rows.toIndexedRoutedFixedCornerSquareWithLayerStack window data hsite hmatch
      hcompatible).window = window :=
  rfl

end CheckedSeparateLayerRows

/-- Direct indexed-active layered geometric certificate for layered scaffold data. -/
structure Certificate (D : LayeredFigure18ScaffoldData) : Prop where
  certificate : LayeredFigure18Certificate D.layerData D.table

namespace Certificate

def toLayeredFigure18Instance
    {D : LayeredFigure18ScaffoldData} (certificate : D.Certificate) :
    LayeredFigure18Instance where
  layerData := D.layerData
  table := D.table
  certificate := certificate.certificate

def toFigure18Instance
    {D : LayeredFigure18ScaffoldData} (certificate : D.Certificate) :
    Figure18Instance :=
  certificate.toLayeredFigure18Instance.toFigure18Instance

theorem isScaffold
    {D : LayeredFigure18ScaffoldData} (certificate : D.Certificate) :
    IsScaffold D.scaffold := by
  change IsScaffold certificate.toLayeredFigure18Instance.presentation.toScaffold
  exact certificate.toLayeredFigure18Instance.isScaffold

end Certificate

/--
Preferred indexed-routed layered geometric certificate for layered scaffold
data.
-/
structure IndexedRoutedCertificate (D : LayeredFigure18ScaffoldData) : Prop where
  certificate : LayeredFigure18IndexedRoutedCertificate D.layerData D.table

namespace IndexedRoutedCertificate

def toLayeredFigure18IndexedRoutedInstance
    {D : LayeredFigure18ScaffoldData}
    (certificate : D.IndexedRoutedCertificate) :
    LayeredFigure18IndexedRoutedInstance where
  layerData := D.layerData
  table := D.table
  certificate := certificate.certificate

def toFigure18IndexedRoutedInstance
    {D : LayeredFigure18ScaffoldData}
    (certificate : D.IndexedRoutedCertificate) :
    Figure18IndexedRoutedInstance :=
  certificate.toLayeredFigure18IndexedRoutedInstance.toFigure18IndexedRoutedInstance

def toFigure18FlexibleInstance
    {D : LayeredFigure18ScaffoldData}
    (certificate : D.IndexedRoutedCertificate) :
    Figure18FlexibleInstance :=
  certificate.toLayeredFigure18IndexedRoutedInstance.toFigure18FlexibleInstance

theorem isScaffold
    {D : LayeredFigure18ScaffoldData}
    (certificate : D.IndexedRoutedCertificate) :
    IsScaffold D.scaffold := by
  change IsScaffold
    certificate.toLayeredFigure18IndexedRoutedInstance.presentation.toScaffold
  exact certificate.toLayeredFigure18IndexedRoutedInstance.isScaffold

end IndexedRoutedCertificate

namespace CheckedRawData

/-- Direct layered certificate attached to checked raw scaffold data. -/
abbrev Certificate (data : CheckedRawData) : Prop :=
  data.toLayeredFigure18ScaffoldData.Certificate

/-- Preferred indexed-routed certificate attached to checked raw scaffold data. -/
abbrev IndexedRoutedCertificate (data : CheckedRawData) : Prop :=
  data.toLayeredFigure18ScaffoldData.IndexedRoutedCertificate

def toLayeredFigure18Instance
    {data : CheckedRawData} (certificate : data.Certificate) :
    LayeredFigure18Instance :=
  certificate.toLayeredFigure18Instance

def toFigure18Instance
    {data : CheckedRawData} (certificate : data.Certificate) :
    Figure18Instance :=
  certificate.toFigure18Instance

theorem isScaffold
    {data : CheckedRawData} (certificate : data.Certificate) :
    IsScaffold data.toLayeredFigure18ScaffoldData.scaffold :=
  certificate.isScaffold

def toLayeredFigure18IndexedRoutedInstance
    {data : CheckedRawData}
    (certificate : data.IndexedRoutedCertificate) :
    LayeredFigure18IndexedRoutedInstance :=
  certificate.toLayeredFigure18IndexedRoutedInstance

def toFigure18IndexedRoutedInstance
    {data : CheckedRawData}
    (certificate : data.IndexedRoutedCertificate) :
    Figure18IndexedRoutedInstance :=
  certificate.toFigure18IndexedRoutedInstance

def toFigure18FlexibleInstance
    {data : CheckedRawData}
    (certificate : data.IndexedRoutedCertificate) :
    Figure18FlexibleInstance :=
  certificate.toFigure18FlexibleInstance

theorem isScaffold_indexedRouted
    {data : CheckedRawData}
    (certificate : data.IndexedRoutedCertificate) :
    IsScaffold data.toLayeredFigure18ScaffoldData.scaffold :=
  certificate.isScaffold

end CheckedRawData

namespace CheckedSparseRawData

abbrev Certificate (data : CheckedSparseRawData) : Prop :=
  data.toCheckedRawData.Certificate

abbrev IndexedRoutedCertificate (data : CheckedSparseRawData) : Prop :=
  data.toCheckedRawData.IndexedRoutedCertificate

def toLayeredFigure18Instance
    {data : CheckedSparseRawData} (certificate : data.Certificate) :
    LayeredFigure18Instance :=
  data.toCheckedRawData.toLayeredFigure18Instance certificate

def toFigure18Instance
    {data : CheckedSparseRawData} (certificate : data.Certificate) :
    Figure18Instance :=
  data.toCheckedRawData.toFigure18Instance certificate

theorem isScaffold
    {data : CheckedSparseRawData} (certificate : data.Certificate) :
    IsScaffold data.toLayeredFigure18ScaffoldData.scaffold :=
  data.toCheckedRawData.isScaffold certificate

def toLayeredFigure18IndexedRoutedInstance
    {data : CheckedSparseRawData}
    (certificate : data.IndexedRoutedCertificate) :
    LayeredFigure18IndexedRoutedInstance :=
  data.toCheckedRawData.toLayeredFigure18IndexedRoutedInstance certificate

def toFigure18IndexedRoutedInstance
    {data : CheckedSparseRawData}
    (certificate : data.IndexedRoutedCertificate) :
    Figure18IndexedRoutedInstance :=
  data.toCheckedRawData.toFigure18IndexedRoutedInstance certificate

def toFigure18FlexibleInstance
    {data : CheckedSparseRawData}
    (certificate : data.IndexedRoutedCertificate) :
    Figure18FlexibleInstance :=
  data.toCheckedRawData.toFigure18FlexibleInstance certificate

theorem isScaffold_indexedRouted
    {data : CheckedSparseRawData}
    (certificate : data.IndexedRoutedCertificate) :
    IsScaffold data.toLayeredFigure18ScaffoldData.scaffold :=
  data.toCheckedRawData.isScaffold_indexedRouted certificate

end CheckedSparseRawData

end LayeredFigure18ScaffoldData

end Figure13Layers
end OllingerRobinson
end LeanWang
