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

def symbols (components : Components) : List Figure16.Symbol :=
  (match components.thin with
    | none => []
    | some component => [Figure16.Symbol.thin component]) ++
  (match components.thick with
    | none => []
    | some component => [Figure16.Symbol.thick component]) ++
  (match components.black with
    | none => []
    | some component => [Figure16.Symbol.black component])

/--
Figure 16 substitution rules directly selected by the components of a Figure 13
tile.  The `phi_L1(*)` rule is global background data and is kept separately
from component-indexed tile rows.
-/
def ruleSources (components : Components) : List Figure16.RuleSource :=
  (match components.thin with
    | none => []
    | some component => [Figure16.RuleSource.l2Component1 component]) ++
  (match components.thick with
    | none => []
    | some component => [Figure16.RuleSource.l2Component2 component]) ++
  (match components.black with
    | none => []
    | some component => [Figure16.RuleSource.l3 component])

def ruleBlocks (components : Components) : List Figure16.Block :=
  components.ruleSources.map Figure16.RuleSource.block

theorem mem_ruleSources_all
    {components : Components} {source : Figure16.RuleSource}
    (hsource : source ∈ components.ruleSources) :
    source ∈ Figure16.RuleSource.all := by
  rcases components with ⟨thin, thick, black⟩
  cases thin <;> cases thick <;> cases black <;>
    simp [ruleSources, Figure16.RuleSource.mem_all] at hsource ⊢

theorem exists_substitutionRule_of_mem_ruleSources
    {components : Components} {source : Figure16.RuleSource}
    (_hsource : source ∈ components.ruleSources) :
    ∃ rule : Figure16.SubstitutionRule,
      rule ∈ Figure16.substitutionRules ∧ rule.source = source ∧
        rule.block = source.block := by
  refine ⟨Figure16.SubstitutionRule.ofSource source,
    Figure16.SubstitutionRule.ofSource_mem source, rfl, rfl⟩

theorem validRectangle_of_mem_ruleSources
    {components : Components} {source : Figure16.RuleSource}
    (_hsource : source ∈ components.ruleSources) :
    ValidRectangle Figure16.Symbol.tileSet source.block.rectangle := by
  exact source.block_validRectangle_symbolTileSet

theorem mem_symbols_all
    {components : Components} {symbol : Figure16.Symbol}
    (_hsymbol : symbol ∈ components.symbols) :
    symbol ∈ Figure16.Symbol.all := by
  exact Figure16.Symbol.mem_all symbol

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
