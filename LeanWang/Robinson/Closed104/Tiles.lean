/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104

/-!
Compositional Wang-edge encoding of the corrected 104 Ollinger tiles.

Each rendered edge carries one thin endpoint, one thick endpoint, and an
optional black endpoint. Thin and thick endpoints both record a red/green color
and one of the two boundary lanes. The resulting finite checks certify that
every Figure 16 child block is valid and that substitution preserves and
reflects matching across parent boundaries.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104

inductive WireColor where
  | red
  | green
deriving DecidableEq, Repr

inductive Lane where
  | low
  | high
deriving DecidableEq, Repr

structure WireEnd where
  lane : Lane
  color : WireColor
deriving DecidableEq, Repr

namespace WireEnd

def code (endpoint : WireEnd) : Nat :=
  (match endpoint.lane with | .low => 0 | .high => 1) +
    2 * (match endpoint.color with | .red => 0 | .green => 1)

def redLow : WireEnd := ⟨.low, .red⟩
def redHigh : WireEnd := ⟨.high, .red⟩
def greenLow : WireEnd := ⟨.low, .green⟩
def greenHigh : WireEnd := ⟨.high, .green⟩

end WireEnd

def thinNorth : Figure16.Thin → WireEnd
  | .a => .redHigh
  | .b => .greenHigh
  | .c => .redLow
  | .d => .greenLow

def thinSouth : Figure16.Thin → WireEnd
  | .a => .greenLow
  | .b => .redLow
  | .c => .greenHigh
  | .d => .redHigh

def thinEast : Figure16.Thin → WireEnd
  | .a => .redHigh
  | .b => .greenHigh
  | .c => .greenLow
  | .d => .redLow

def thinWest : Figure16.Thin → WireEnd
  | .a => .greenLow
  | .b => .redLow
  | .c => .redHigh
  | .d => .greenHigh

def thickLineVerticalEnd? : Figure16.ThickLine → Option WireEnd
  | .r0 => some .redHigh
  | .r2 => some .redLow
  | .g0 => some .greenHigh
  | .g2 => some .greenLow
  | _ => none

def thickLineHorizontalEnd? : Figure16.ThickLine → Option WireEnd
  | .r1 => some .redHigh
  | .r3 => some .redLow
  | .g1 => some .greenHigh
  | .g3 => some .greenLow
  | _ => none

private def lineSumVertical (component : Figure16.Thick) : WireEnd :=
  match component.lineSum? with
  | none => .redLow
  | some sum =>
      (thickLineVerticalEnd? sum.first).getD
        ((thickLineVerticalEnd? sum.second).getD .redLow)

private def lineSumHorizontal (component : Figure16.Thick) : WireEnd :=
  match component.lineSum? with
  | none => .redLow
  | some sum =>
      (thickLineHorizontalEnd? sum.first).getD
        ((thickLineHorizontalEnd? sum.second).getD .redLow)

def thickNorth : Figure16.Thick → WireEnd
  | .a => .greenLow
  | .b => .redHigh
  | .c => .redLow
  | .d => .greenHigh
  | component => lineSumVertical component

def thickSouth : Figure16.Thick → WireEnd
  | .a => .redHigh
  | .b => .greenLow
  | .c => .greenHigh
  | .d => .redLow
  | component => lineSumVertical component

def thickEast : Figure16.Thick → WireEnd
  | .a => .redLow
  | .b => .redHigh
  | .c => .greenLow
  | .d => .greenHigh
  | component => lineSumHorizontal component

def thickWest : Figure16.Thick → WireEnd
  | .a => .greenHigh
  | .b => .greenLow
  | .c => .redHigh
  | .d => .redLow
  | component => lineSumHorizontal component

def blackNorth : Figure16.Black → Bool
  | .a => false
  | .b => true
  | .c => true
  | .d => true
  | .e => false

def blackSouth : Figure16.Black → Bool
  | .a => true
  | .b => false
  | .c => false
  | .d => true
  | .e => false

def blackEast : Figure16.Black → Bool
  | .a => false
  | .b => false
  | .c => true
  | .d => true
  | .e => true

def blackWest : Figure16.Black → Bool
  | .a => true
  | .b => false
  | .c => true
  | .d => false
  | .e => false

/-- Numeric code for the three superimposed endpoint layers on one edge. -/
def edgeCode (thin thick : WireEnd) (black : Bool) : Nat :=
  thin.code +
    4 * thick.code +
      if black then 16 else 0

/-- Corrected Wang tile assembled from one thin/thick/black component triple. -/
def tile (components : Components) : WangTile where
  n := edgeCode (thinNorth components.1) (thickNorth components.2.1)
    (blackNorth components.2.2)
  s := edgeCode (thinSouth components.1) (thickSouth components.2.1)
    (blackSouth components.2.2)
  e := edgeCode (thinEast components.1) (thickEast components.2.1)
    (blackEast components.2.2)
  w := edgeCode (thinWest components.1) (thickWest components.2.1)
    (blackWest components.2.2)

/-- The corrected finite Wang tileset. -/
def tileSet : TileSet :=
  (alphabet.map tile).eraseDups

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
@[simp]
theorem tileSet_length : tileSet.length = 104 := by
  native_decide

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem tileSet_nodup : tileSet.Nodup := by
  native_decide

theorem tile_components_mem (index : Index) :
    tile (components index) ∈ tileSet := by
  simp only [tileSet, List.mem_eraseDups]
  apply List.mem_map.2
  exact ⟨_, List.getElem_mem _, rfl⟩

/-- Wang-tile realization of one corrected Figure 16 child block. -/
def childRectangle (parent : Index) : Rectangle 2 2 :=
  fun i j => tile (components (childBlock parent i j))

/-- Finite certificate that all 104 child blocks are valid Wang rectangles. -/
def allChildRectanglesValidBool : Bool :=
  (List.finRange 104).all fun parent =>
    validRectangleBool tileSet (childRectangle parent)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allChildRectanglesValidBool_eq_true :
    allChildRectanglesValidBool = true := by
  native_decide

theorem childRectangle_valid (parent : Index) :
    ValidRectangle tileSet (childRectangle parent) := by
  have hparent := List.all_eq_true.1 allChildRectanglesValidBool_eq_true
    parent (List.mem_finRange parent)
  exact of_decide_eq_true hparent

/-- Matching of all two child edges across a horizontal substituted boundary. -/
def ChildHMatches (left right : Index) : Prop :=
  WangTile.HMatches
      (childRectangle left ⟨1, by decide⟩ ⟨0, by decide⟩)
      (childRectangle right ⟨0, by decide⟩ ⟨0, by decide⟩) ∧
    WangTile.HMatches
      (childRectangle left ⟨1, by decide⟩ ⟨1, by decide⟩)
      (childRectangle right ⟨0, by decide⟩ ⟨1, by decide⟩)

instance (left right : Index) : Decidable (ChildHMatches left right) := by
  unfold ChildHMatches
  infer_instance

/-- Matching of all two child edges across a vertical substituted boundary. -/
def ChildVMatches (lower upper : Index) : Prop :=
  WangTile.VMatches
      (childRectangle lower ⟨0, by decide⟩ ⟨1, by decide⟩)
      (childRectangle upper ⟨0, by decide⟩ ⟨0, by decide⟩) ∧
    WangTile.VMatches
      (childRectangle lower ⟨1, by decide⟩ ⟨1, by decide⟩)
      (childRectangle upper ⟨1, by decide⟩ ⟨0, by decide⟩)

instance (lower upper : Index) : Decidable (ChildVMatches lower upper) := by
  unfold ChildVMatches
  infer_instance

/-- Finite check that horizontal matching is preserved by substitution. -/
def allHorizontalBoundariesPreservedBool : Bool :=
  (List.finRange 104).all fun left =>
    (List.finRange 104).all fun right =>
      decide (WangTile.HMatches (tile (components left)) (tile (components right)) →
        ChildHMatches left right)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allHorizontalBoundariesPreservedBool_eq_true :
    allHorizontalBoundariesPreservedBool = true := by
  native_decide

/-- Finite check that vertical matching is preserved by substitution. -/
def allVerticalBoundariesPreservedBool : Bool :=
  (List.finRange 104).all fun lower =>
    (List.finRange 104).all fun upper =>
      decide (WangTile.VMatches (tile (components lower)) (tile (components upper)) →
        ChildVMatches lower upper)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allVerticalBoundariesPreservedBool_eq_true :
    allVerticalBoundariesPreservedBool = true := by
  native_decide

theorem childHMatches_of_hMatches (left right : Index)
    (hmatch : WangTile.HMatches
      (tile (components left)) (tile (components right))) :
    ChildHMatches left right := by
  have hleft := List.all_eq_true.1 allHorizontalBoundariesPreservedBool_eq_true
    left (List.mem_finRange left)
  have hright := List.all_eq_true.1 hleft right (List.mem_finRange right)
  exact (of_decide_eq_true hright) hmatch

theorem childVMatches_of_vMatches (lower upper : Index)
    (hmatch : WangTile.VMatches
      (tile (components lower)) (tile (components upper))) :
    ChildVMatches lower upper := by
  have hlower := List.all_eq_true.1 allVerticalBoundariesPreservedBool_eq_true
    lower (List.mem_finRange lower)
  have hupper := List.all_eq_true.1 hlower upper (List.mem_finRange upper)
  exact (of_decide_eq_true hupper) hmatch

/-- Finite check that horizontal matching is reflected by substitution. -/
def allHorizontalBoundariesReflectedBool : Bool :=
  (List.finRange 104).all fun left =>
    (List.finRange 104).all fun right =>
      decide (ChildHMatches left right →
        WangTile.HMatches (tile (components left)) (tile (components right)))

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allHorizontalBoundariesReflectedBool_eq_true :
    allHorizontalBoundariesReflectedBool = true := by
  native_decide

/-- Finite check that vertical matching is reflected by substitution. -/
def allVerticalBoundariesReflectedBool : Bool :=
  (List.finRange 104).all fun lower =>
    (List.finRange 104).all fun upper =>
      decide (ChildVMatches lower upper →
        WangTile.VMatches (tile (components lower)) (tile (components upper)))

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allVerticalBoundariesReflectedBool_eq_true :
    allVerticalBoundariesReflectedBool = true := by
  native_decide

theorem hMatches_of_childHMatches (left right : Index)
    (hmatch : ChildHMatches left right) :
    WangTile.HMatches (tile (components left)) (tile (components right)) := by
  have hleft := List.all_eq_true.1 allHorizontalBoundariesReflectedBool_eq_true
    left (List.mem_finRange left)
  have hright := List.all_eq_true.1 hleft right (List.mem_finRange right)
  exact (of_decide_eq_true hright) hmatch

theorem vMatches_of_childVMatches (lower upper : Index)
    (hmatch : ChildVMatches lower upper) :
    WangTile.VMatches (tile (components lower)) (tile (components upper)) := by
  have hlower := List.all_eq_true.1 allVerticalBoundariesReflectedBool_eq_true
    lower (List.mem_finRange lower)
  have hupper := List.all_eq_true.1 hlower upper (List.mem_finRange upper)
  exact (of_decide_eq_true hupper) hmatch

end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
