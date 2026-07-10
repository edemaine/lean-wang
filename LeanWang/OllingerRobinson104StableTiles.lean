/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104
import LeanWang.OllingerRobinson104Tiles

/-!
Substitution-derived edge colors for the corrected Ollinger alphabet.

At the next depth, an exposed macro-edge is encoded by the ordered pair of its
two exposed child edges. A depth where the induced matching relations stabilize
therefore realizes exactly the intrinsic-substitution boundary condition.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104

private def sw : Fin 2 := ⟨0, by decide⟩
private def se : Fin 2 := ⟨1, by decide⟩
private def lo : Fin 2 := ⟨0, by decide⟩
private def hi : Fin 2 := ⟨1, by decide⟩

/-- Edge colors obtained after repeatedly reading exposed child boundaries. -/
def derivedTile : Nat → Index → WangTile
  | 0, index => tile (components index)
  | depth + 1, index =>
      let children := childBlock index
      { n := Nat.pair (derivedTile depth (children sw hi)).n
          (derivedTile depth (children se hi)).n
        s := Nat.pair (derivedTile depth (children sw lo)).s
          (derivedTile depth (children se lo)).s
        e := Nat.pair (derivedTile depth (children se lo)).e
          (derivedTile depth (children se hi)).e
        w := Nat.pair (derivedTile depth (children sw lo)).w
          (derivedTile depth (children sw hi)).w }

def derivedTileSet (depth : Nat) : TileSet :=
  ((List.finRange 104).map (derivedTile depth)).eraseDups

def derivedChildRectangle (depth : Nat) (parent : Index) : Rectangle 2 2 :=
  fun i j => derivedTile depth (childBlock parent i j)

def DerivedChildHMatches (depth : Nat) (left right : Index) : Prop :=
  WangTile.HMatches
      (derivedChildRectangle depth left se lo)
      (derivedChildRectangle depth right sw lo) ∧
    WangTile.HMatches
      (derivedChildRectangle depth left se hi)
      (derivedChildRectangle depth right sw hi)

def DerivedChildVMatches (depth : Nat) (lower upper : Index) : Prop :=
  WangTile.VMatches
      (derivedChildRectangle depth lower sw hi)
      (derivedChildRectangle depth upper sw lo) ∧
    WangTile.VMatches
      (derivedChildRectangle depth lower se hi)
      (derivedChildRectangle depth upper se lo)

instance (depth : Nat) (left right : Index) :
    Decidable (DerivedChildHMatches depth left right) := by
  unfold DerivedChildHMatches
  infer_instance

instance (depth : Nat) (lower upper : Index) :
    Decidable (DerivedChildVMatches depth lower upper) := by
  unfold DerivedChildVMatches
  infer_instance

/-- Does depth-`d` horizontal matching equal expanded depth-`d` matching? -/
def horizontalStableBool (depth : Nat) : Bool :=
  (List.finRange 104).all fun left =>
    (List.finRange 104).all fun right =>
      decide (WangTile.HMatches (derivedTile depth left) (derivedTile depth right) ↔
        DerivedChildHMatches depth left right)

/-- Does depth-`d` vertical matching equal expanded depth-`d` matching? -/
def verticalStableBool (depth : Nat) : Bool :=
  (List.finRange 104).all fun lower =>
    (List.finRange 104).all fun upper =>
      decide (WangTile.VMatches (derivedTile depth lower) (derivedTile depth upper) ↔
        DerivedChildVMatches depth lower upper)

/-- Are all substitution blocks internally valid at this derived depth? -/
def allDerivedChildRectanglesValidBool (depth : Nat) : Bool :=
  (List.finRange 104).all fun parent =>
    validRectangleBool (derivedTileSet depth) (derivedChildRectangle depth parent)

/-- Compact diagnostics for the first `count` derived depths. -/
def derivedDepthDiagnostics (count : Nat) : List (Nat × Nat × Bool × Bool × Bool) :=
  (List.range count).map fun depth =>
    (depth, (derivedTileSet depth).length,
      horizontalStableBool depth, verticalStableBool depth,
      allDerivedChildRectanglesValidBool depth)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem depthOneStableAndValid :
    horizontalStableBool 1 = true ∧
      verticalStableBool 1 = true ∧
      allDerivedChildRectanglesValidBool 1 = true := by
  native_decide

theorem derivedTile_mem_derivedTileSet (depth : Nat) (index : Index) :
    derivedTile depth index ∈ derivedTileSet depth := by
  simp only [derivedTileSet, List.mem_eraseDups]
  exact List.mem_map.2 ⟨index, List.mem_finRange index, rfl⟩

theorem derivedChildRectangle_valid_one (parent : Index) :
    ValidRectangle (derivedTileSet 1) (derivedChildRectangle 1 parent) := by
  have hparent := List.all_eq_true.1 depthOneStableAndValid.2.2
    parent (List.mem_finRange parent)
  exact of_decide_eq_true hparent

theorem hMatches_derived_one_iff_child
    (left right : Index) :
    WangTile.HMatches (derivedTile 1 left) (derivedTile 1 right) ↔
      DerivedChildHMatches 1 left right := by
  have hleft := List.all_eq_true.1 depthOneStableAndValid.1
    left (List.mem_finRange left)
  have hright := List.all_eq_true.1 hleft right (List.mem_finRange right)
  exact of_decide_eq_true hright

theorem vMatches_derived_one_iff_child
    (lower upper : Index) :
    WangTile.VMatches (derivedTile 1 lower) (derivedTile 1 upper) ↔
      DerivedChildVMatches 1 lower upper := by
  have hlower := List.all_eq_true.1 depthOneStableAndValid.2.1
    lower (List.mem_finRange lower)
  have hupper := List.all_eq_true.1 hlower upper (List.mem_finRange upper)
  exact of_decide_eq_true hupper

end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
