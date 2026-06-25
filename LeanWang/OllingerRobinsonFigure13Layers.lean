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

end Transcription

end Figure13Layers
end OllingerRobinson
end LeanWang
