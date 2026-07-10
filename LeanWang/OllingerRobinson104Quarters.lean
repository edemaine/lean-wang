/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PlaneRedBoards
import LeanWang.TileSubdivision

/-!
Quarter-tile presentation of the corrected 104-tile Ollinger alphabet.

Figure 18 routes payload symbols through tile quarters. This module instantiates
the generic subdivision without using the obsolete 92-tile transcription.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Quarters

abbrev QuarterIndex := Index × Quadrant

def all : List QuarterIndex :=
  (List.finRange 104).flatMap fun index =>
    Quadrant.all.map fun quadrant => (index, quadrant)

set_option linter.style.nativeDecide false in
@[simp]
theorem all_length : all.length = 416 := by
  native_decide

theorem mem_all (site : QuarterIndex) : site ∈ all := by
  rcases site with ⟨index, quadrant⟩
  simp [all, List.mem_finRange, Quadrant.mem_all]

def quarterTile (site : QuarterIndex) : WangTile :=
  TileSubdivision.subdivideTileAt (tile (components site.1)) site.2

def tileSet : TileSet := all.map quarterTile

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem tileSet_nodup : tileSet.Nodup := by
  native_decide

@[simp]
theorem tileSet_length : tileSet.length = 416 := by
  rw [tileSet, List.length_map, all_length]

theorem quarterTile_mem (site : QuarterIndex) : quarterTile site ∈ tileSet := by
  exact List.mem_map.2 ⟨site, mem_all site, rfl⟩

def allQuarterTilesDistinctBool : Bool :=
  all.all fun left =>
    all.all fun right =>
      decide (quarterTile left = quarterTile right → left = right)

/- Both the corrected parent encoding and its four subdivisions are injective. -/
set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allQuarterTilesDistinctBool_eq_true :
    allQuarterTilesDistinctBool = true := by
  native_decide

theorem quarterTile_injective : Function.Injective quarterTile := by
  intro left right heq
  have hleft := List.all_eq_true.1 allQuarterTilesDistinctBool_eq_true
    left (mem_all left)
  have hright := List.all_eq_true.1 hleft right (mem_all right)
  exact (of_decide_eq_true hright) heq

def candidates (wang : WangTile) : List QuarterIndex :=
  all.filter fun site => quarterTile site == wang

def decode (wang : WangTile) : QuarterIndex :=
  (candidates wang).headD (⟨0, by decide⟩, .southwest)

def allDecodeCorrectBool : Bool :=
  all.all fun site => decide (decode (quarterTile site) = site)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allDecodeCorrectBool_eq_true : allDecodeCorrectBool = true := by
  native_decide

@[simp]
theorem decode_quarterTile (site : QuarterIndex) :
    decode (quarterTile site) = site := by
  have hsite := List.all_eq_true.1 allDecodeCorrectBool_eq_true
    site (mem_all site)
  exact of_decide_eq_true hsite

theorem quarterTile_decode_of_mem {wang : WangTile} (hwang : wang ∈ tileSet) :
    quarterTile (decode wang) = wang := by
  rcases List.mem_map.1 hwang with ⟨site, _hsite, rfl⟩
  rw [decode_quarterTile]

def phaseEast : Quadrant → Quadrant
  | .southwest => .southeast
  | .southeast => .southwest
  | .northwest => .northeast
  | .northeast => .northwest

def phaseNorth : Quadrant → Quadrant
  | .southwest => .northwest
  | .southeast => .northeast
  | .northwest => .southwest
  | .northeast => .southeast

@[simp]
theorem phaseEast_involutive (quadrant : Quadrant) :
    phaseEast (phaseEast quadrant) = quadrant := by
  cases quadrant <;> rfl

@[simp]
theorem phaseNorth_involutive (quadrant : Quadrant) :
    phaseNorth (phaseNorth quadrant) = quadrant := by
  cases quadrant <;> rfl

theorem phaseEast_phaseNorth_comm (quadrant : Quadrant) :
    phaseEast (phaseNorth quadrant) = phaseNorth (phaseEast quadrant) := by
  cases quadrant <;> rfl

/-- Horizontal quarter-tile matching forces the east checkerboard phase. -/
theorem phase_eq_east_of_hMatches {left right : QuarterIndex}
    (hmatch : WangTile.HMatches (quarterTile left) (quarterTile right)) :
    right.2 = phaseEast left.2 := by
  have hallowed := (TileSubdivision.hMatches_subdivideTileAt_iff
    (tile (components left.1)) (tile (components right.1)) left.2 right.2).1 hmatch
  rcases left with ⟨left, leftQuadrant⟩
  rcases right with ⟨right, rightQuadrant⟩
  cases leftQuadrant <;> cases rightQuadrant <;> simp_all [phaseEast]

/-- Vertical quarter-tile matching forces the north checkerboard phase. -/
theorem phase_eq_north_of_vMatches {lower upper : QuarterIndex}
    (hmatch : WangTile.VMatches (quarterTile lower) (quarterTile upper)) :
    upper.2 = phaseNorth lower.2 := by
  have hallowed := (TileSubdivision.vMatches_subdivideTileAt_iff
    (tile (components lower.1)) (tile (components upper.1)) lower.2 upper.2).1 hmatch
  rcases lower with ⟨lower, lowerQuadrant⟩
  rcases upper with ⟨upper, upperQuadrant⟩
  cases lowerQuadrant <;> cases upperQuadrant <;> simp_all [phaseNorth]

end Quarters
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
