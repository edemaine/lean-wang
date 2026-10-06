/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.FiniteRecognizability.ExtendablePairs
import Mathlib.Tactic.FinCases

/-!
# Kernel certificates for unique substitution parents

Each extendable center has one parent candidate. The final recognizability proof
uses this checked finite table through ordinary list membership.
-/

set_option maxRecDepth 30000

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace FiniteRecognizability

abbrev IndexBlock := Index × Index × Index × Index

/- A central `2 x 2` block is recognizable exactly when it occurs as the
ordered child block of one parent.  The kernel audit checks uniqueness for all
extendable central row pairs; the proof-facing tail of the file extracts that
fact for an arbitrary valid neighborhood. -/

def childIndexBlock (parent : Index) : IndexBlock :=
  (childBlock parent ⟨0, by decide⟩ ⟨0, by decide⟩,
    childBlock parent ⟨1, by decide⟩ ⟨0, by decide⟩,
    childBlock parent ⟨0, by decide⟩ ⟨1, by decide⟩,
    childBlock parent ⟨1, by decide⟩ ⟨1, by decide⟩)

def parentIndexBlocks : List (Index × IndexBlock) :=
  indices.map fun parent => (parent, childIndexBlock parent)

def centralIndexBlock (middle : List Index × List Index) : IndexBlock :=
  (rowCell middle.1 1, rowCell middle.1 2,
    rowCell middle.2 1, rowCell middle.2 2)

def centerParentCandidates (middle : List Index × List Index) : List Index :=
  (parentIndexBlocks.filter fun entry =>
    entry.2 == centralIndexBlock middle).map Prod.fst

theorem mem_centerParentCandidates_iff {middle : List Index × List Index}
    {parent : Index} :
    parent ∈ centerParentCandidates middle ↔
      childIndexBlock parent = centralIndexBlock middle := by
  simp [centerParentCandidates, parentIndexBlocks, indices]

private theorem parent_row0 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨0, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row1 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨1, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row2 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨2, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row3 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨3, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row4 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨4, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row5 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨5, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row6 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨6, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row7 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨7, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row8 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨8, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row9 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨9, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row10 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨10, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row11 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨11, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row12 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨12, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row13 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨13, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row14 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨14, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row15 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨15, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row16 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨16, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row17 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨17, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row18 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨18, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row19 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨19, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row20 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨20, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row21 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨21, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row22 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨22, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row23 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨23, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row24 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨24, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row25 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨25, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row26 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨26, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row27 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨27, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row28 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨28, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row29 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨29, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row30 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨30, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row31 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨31, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row32 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨32, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row33 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨33, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row34 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨34, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row35 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨35, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row36 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨36, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row37 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨37, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row38 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨38, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row39 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨39, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row40 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨40, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row41 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨41, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row42 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨42, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row43 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨43, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row44 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨44, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row45 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨45, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row46 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨46, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row47 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨47, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row48 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨48, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row49 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨49, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row50 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨50, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row51 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨51, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row52 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨52, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row53 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨53, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row54 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨54, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row55 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨55, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row56 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨56, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row57 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨57, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row58 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨58, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row59 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨59, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row60 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨60, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row61 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨61, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row62 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨62, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row63 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨63, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row64 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨64, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row65 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨65, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row66 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨66, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row67 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨67, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row68 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨68, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row69 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨69, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row70 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨70, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row71 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨71, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row72 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨72, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row73 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨73, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row74 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨74, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row75 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨75, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row76 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨76, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row77 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨77, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row78 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨78, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row79 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨79, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row80 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨80, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row81 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨81, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row82 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨82, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row83 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨83, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row84 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨84, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row85 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨85, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row86 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨86, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row87 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨87, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row88 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨88, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row89 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨89, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row90 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨90, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row91 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨91, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row92 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨92, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row93 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨93, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row94 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨94, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row95 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨95, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row96 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨96, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row97 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨97, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row98 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨98, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row99 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨99, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row100 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨100, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row101 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨101, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row102 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨102, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row103 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨103, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row104 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨104, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row105 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨105, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row106 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨106, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row107 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨107, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row108 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨108, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row109 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨109, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row110 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨110, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row111 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨111, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row112 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨112, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row113 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨113, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row114 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨114, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row115 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨115, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row116 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨116, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row117 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨117, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row118 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨118, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row119 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨119, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row120 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨120, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row121 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨121, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row122 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨122, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row123 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨123, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row124 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨124, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row125 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨125, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row126 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨126, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row127 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨127, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row128 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨128, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row129 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨129, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row130 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨130, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row131 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨131, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row132 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨132, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row133 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨133, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row134 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨134, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row135 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨135, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row136 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨136, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row137 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨137, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row138 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨138, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row139 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨139, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row140 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨140, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row141 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨141, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row142 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨142, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row143 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨143, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row144 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨144, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row145 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨145, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row146 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨146, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row147 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨147, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row148 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨148, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row149 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨149, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row150 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨150, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row151 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨151, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row152 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨152, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row153 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨153, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row154 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨154, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row155 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨155, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row156 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨156, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row157 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨157, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row158 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨158, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row159 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨159, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row160 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨160, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row161 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨161, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row162 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨162, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row163 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨163, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row164 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨164, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row165 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨165, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row166 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨166, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row167 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨167, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row168 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨168, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row169 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨169, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row170 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨170, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row171 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨171, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row172 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨172, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row173 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨173, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row174 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨174, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row175 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨175, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row176 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨176, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row177 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨177, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row178 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨178, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row179 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨179, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row180 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨180, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row181 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨181, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row182 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨182, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row183 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨183, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row184 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨184, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row185 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨185, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row186 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨186, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row187 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨187, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row188 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨188, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row189 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨189, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row190 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨190, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row191 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨191, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row192 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨192, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row193 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨193, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row194 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨194, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row195 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨195, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row196 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨196, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row197 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨197, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row198 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨198, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row199 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨199, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row200 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨200, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row201 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨201, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row202 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨202, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row203 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨203, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row204 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨204, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row205 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨205, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row206 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨206, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row207 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨207, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row208 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨208, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row209 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨209, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row210 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨210, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row211 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨211, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row212 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨212, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row213 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨213, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row214 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨214, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row215 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨215, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row216 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨216, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row217 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨217, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row218 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨218, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row219 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨219, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row220 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨220, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row221 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨221, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row222 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨222, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row223 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨223, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row224 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨224, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row225 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨225, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row226 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨226, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row227 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨227, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row228 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨228, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row229 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨229, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row230 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨230, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row231 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨231, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row232 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨232, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row233 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨233, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row234 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨234, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row235 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨235, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row236 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨236, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row237 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨237, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row238 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨238, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row239 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨239, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row240 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨240, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row241 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨241, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row242 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨242, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row243 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨243, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row244 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨244, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row245 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨245, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row246 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨246, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row247 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨247, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row248 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨248, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row249 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨249, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row250 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨250, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row251 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨251, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row252 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨252, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row253 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨253, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row254 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨254, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row255 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨255, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row256 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨256, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row257 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨257, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row258 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨258, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row259 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨259, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row260 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨260, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row261 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨261, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row262 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨262, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row263 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨263, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row264 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨264, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row265 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨265, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row266 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨266, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row267 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨267, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row268 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨268, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row269 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨269, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row270 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨270, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row271 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨271, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row272 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨272, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row273 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨273, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row274 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨274, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row275 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨275, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row276 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨276, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row277 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨277, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row278 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨278, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row279 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨279, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row280 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨280, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row281 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨281, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row282 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨282, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row283 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨283, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row284 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨284, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row285 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨285, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row286 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨286, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row287 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨287, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row288 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨288, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row289 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨289, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row290 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨290, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row291 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨291, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row292 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨292, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row293 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨293, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row294 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨294, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row295 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨295, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row296 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨296, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row297 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨297, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row298 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨298, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row299 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨299, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row300 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨300, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row301 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨301, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row302 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨302, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row303 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨303, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row304 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨304, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row305 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨305, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row306 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨306, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row307 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨307, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row308 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨308, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row309 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨309, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row310 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨310, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row311 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨311, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row312 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨312, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row313 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨313, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row314 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨314, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row315 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨315, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row316 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨316, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row317 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨317, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row318 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨318, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row319 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨319, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row320 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨320, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row321 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨321, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row322 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨322, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row323 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨323, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row324 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨324, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row325 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨325, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row326 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨326, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_row327 :
    (centerParentCandidates (extendableCentralRowPairs.get ⟨327, by decide +kernel⟩)).length = 1 := by
  decide +kernel

private theorem parent_at_correct (i : Fin extendableCentralRowPairs.length) :
    (centerParentCandidates (extendableCentralRowPairs.get i)).length = 1 := by
  fin_cases i
  · exact parent_row0
  · exact parent_row1
  · exact parent_row2
  · exact parent_row3
  · exact parent_row4
  · exact parent_row5
  · exact parent_row6
  · exact parent_row7
  · exact parent_row8
  · exact parent_row9
  · exact parent_row10
  · exact parent_row11
  · exact parent_row12
  · exact parent_row13
  · exact parent_row14
  · exact parent_row15
  · exact parent_row16
  · exact parent_row17
  · exact parent_row18
  · exact parent_row19
  · exact parent_row20
  · exact parent_row21
  · exact parent_row22
  · exact parent_row23
  · exact parent_row24
  · exact parent_row25
  · exact parent_row26
  · exact parent_row27
  · exact parent_row28
  · exact parent_row29
  · exact parent_row30
  · exact parent_row31
  · exact parent_row32
  · exact parent_row33
  · exact parent_row34
  · exact parent_row35
  · exact parent_row36
  · exact parent_row37
  · exact parent_row38
  · exact parent_row39
  · exact parent_row40
  · exact parent_row41
  · exact parent_row42
  · exact parent_row43
  · exact parent_row44
  · exact parent_row45
  · exact parent_row46
  · exact parent_row47
  · exact parent_row48
  · exact parent_row49
  · exact parent_row50
  · exact parent_row51
  · exact parent_row52
  · exact parent_row53
  · exact parent_row54
  · exact parent_row55
  · exact parent_row56
  · exact parent_row57
  · exact parent_row58
  · exact parent_row59
  · exact parent_row60
  · exact parent_row61
  · exact parent_row62
  · exact parent_row63
  · exact parent_row64
  · exact parent_row65
  · exact parent_row66
  · exact parent_row67
  · exact parent_row68
  · exact parent_row69
  · exact parent_row70
  · exact parent_row71
  · exact parent_row72
  · exact parent_row73
  · exact parent_row74
  · exact parent_row75
  · exact parent_row76
  · exact parent_row77
  · exact parent_row78
  · exact parent_row79
  · exact parent_row80
  · exact parent_row81
  · exact parent_row82
  · exact parent_row83
  · exact parent_row84
  · exact parent_row85
  · exact parent_row86
  · exact parent_row87
  · exact parent_row88
  · exact parent_row89
  · exact parent_row90
  · exact parent_row91
  · exact parent_row92
  · exact parent_row93
  · exact parent_row94
  · exact parent_row95
  · exact parent_row96
  · exact parent_row97
  · exact parent_row98
  · exact parent_row99
  · exact parent_row100
  · exact parent_row101
  · exact parent_row102
  · exact parent_row103
  · exact parent_row104
  · exact parent_row105
  · exact parent_row106
  · exact parent_row107
  · exact parent_row108
  · exact parent_row109
  · exact parent_row110
  · exact parent_row111
  · exact parent_row112
  · exact parent_row113
  · exact parent_row114
  · exact parent_row115
  · exact parent_row116
  · exact parent_row117
  · exact parent_row118
  · exact parent_row119
  · exact parent_row120
  · exact parent_row121
  · exact parent_row122
  · exact parent_row123
  · exact parent_row124
  · exact parent_row125
  · exact parent_row126
  · exact parent_row127
  · exact parent_row128
  · exact parent_row129
  · exact parent_row130
  · exact parent_row131
  · exact parent_row132
  · exact parent_row133
  · exact parent_row134
  · exact parent_row135
  · exact parent_row136
  · exact parent_row137
  · exact parent_row138
  · exact parent_row139
  · exact parent_row140
  · exact parent_row141
  · exact parent_row142
  · exact parent_row143
  · exact parent_row144
  · exact parent_row145
  · exact parent_row146
  · exact parent_row147
  · exact parent_row148
  · exact parent_row149
  · exact parent_row150
  · exact parent_row151
  · exact parent_row152
  · exact parent_row153
  · exact parent_row154
  · exact parent_row155
  · exact parent_row156
  · exact parent_row157
  · exact parent_row158
  · exact parent_row159
  · exact parent_row160
  · exact parent_row161
  · exact parent_row162
  · exact parent_row163
  · exact parent_row164
  · exact parent_row165
  · exact parent_row166
  · exact parent_row167
  · exact parent_row168
  · exact parent_row169
  · exact parent_row170
  · exact parent_row171
  · exact parent_row172
  · exact parent_row173
  · exact parent_row174
  · exact parent_row175
  · exact parent_row176
  · exact parent_row177
  · exact parent_row178
  · exact parent_row179
  · exact parent_row180
  · exact parent_row181
  · exact parent_row182
  · exact parent_row183
  · exact parent_row184
  · exact parent_row185
  · exact parent_row186
  · exact parent_row187
  · exact parent_row188
  · exact parent_row189
  · exact parent_row190
  · exact parent_row191
  · exact parent_row192
  · exact parent_row193
  · exact parent_row194
  · exact parent_row195
  · exact parent_row196
  · exact parent_row197
  · exact parent_row198
  · exact parent_row199
  · exact parent_row200
  · exact parent_row201
  · exact parent_row202
  · exact parent_row203
  · exact parent_row204
  · exact parent_row205
  · exact parent_row206
  · exact parent_row207
  · exact parent_row208
  · exact parent_row209
  · exact parent_row210
  · exact parent_row211
  · exact parent_row212
  · exact parent_row213
  · exact parent_row214
  · exact parent_row215
  · exact parent_row216
  · exact parent_row217
  · exact parent_row218
  · exact parent_row219
  · exact parent_row220
  · exact parent_row221
  · exact parent_row222
  · exact parent_row223
  · exact parent_row224
  · exact parent_row225
  · exact parent_row226
  · exact parent_row227
  · exact parent_row228
  · exact parent_row229
  · exact parent_row230
  · exact parent_row231
  · exact parent_row232
  · exact parent_row233
  · exact parent_row234
  · exact parent_row235
  · exact parent_row236
  · exact parent_row237
  · exact parent_row238
  · exact parent_row239
  · exact parent_row240
  · exact parent_row241
  · exact parent_row242
  · exact parent_row243
  · exact parent_row244
  · exact parent_row245
  · exact parent_row246
  · exact parent_row247
  · exact parent_row248
  · exact parent_row249
  · exact parent_row250
  · exact parent_row251
  · exact parent_row252
  · exact parent_row253
  · exact parent_row254
  · exact parent_row255
  · exact parent_row256
  · exact parent_row257
  · exact parent_row258
  · exact parent_row259
  · exact parent_row260
  · exact parent_row261
  · exact parent_row262
  · exact parent_row263
  · exact parent_row264
  · exact parent_row265
  · exact parent_row266
  · exact parent_row267
  · exact parent_row268
  · exact parent_row269
  · exact parent_row270
  · exact parent_row271
  · exact parent_row272
  · exact parent_row273
  · exact parent_row274
  · exact parent_row275
  · exact parent_row276
  · exact parent_row277
  · exact parent_row278
  · exact parent_row279
  · exact parent_row280
  · exact parent_row281
  · exact parent_row282
  · exact parent_row283
  · exact parent_row284
  · exact parent_row285
  · exact parent_row286
  · exact parent_row287
  · exact parent_row288
  · exact parent_row289
  · exact parent_row290
  · exact parent_row291
  · exact parent_row292
  · exact parent_row293
  · exact parent_row294
  · exact parent_row295
  · exact parent_row296
  · exact parent_row297
  · exact parent_row298
  · exact parent_row299
  · exact parent_row300
  · exact parent_row301
  · exact parent_row302
  · exact parent_row303
  · exact parent_row304
  · exact parent_row305
  · exact parent_row306
  · exact parent_row307
  · exact parent_row308
  · exact parent_row309
  · exact parent_row310
  · exact parent_row311
  · exact parent_row312
  · exact parent_row313
  · exact parent_row314
  · exact parent_row315
  · exact parent_row316
  · exact parent_row317
  · exact parent_row318
  · exact parent_row319
  · exact parent_row320
  · exact parent_row321
  · exact parent_row322
  · exact parent_row323
  · exact parent_row324
  · exact parent_row325
  · exact parent_row326
  · exact parent_row327

/-- Every extendable center has exactly one candidate parent. -/
theorem centerParentCandidates_length_eq_one_of_mem
    {middle : List Index × List Index} (member : middle ∈ extendableCentralRowPairs) :
    (centerParentCandidates middle).length = 1 := by
  rcases List.mem_iff_get.mp member with ⟨i, rfl⟩
  exact parent_at_correct i

end FiniteRecognizability
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
