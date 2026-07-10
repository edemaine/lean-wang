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

def offset0 : Fin 2 := ⟨0, by decide⟩
def offset1 : Fin 2 := ⟨1, by decide⟩

/-- Edge colors obtained after repeatedly reading exposed child boundaries. -/
def derivedTile : Nat → Index → WangTile
  | 0, index => tile (components index)
  | depth + 1, index =>
      let children := childBlock index
      { n := Nat.pair (derivedTile depth (children offset0 offset1)).n
          (derivedTile depth (children offset1 offset1)).n
        s := Nat.pair (derivedTile depth (children offset0 offset0)).s
          (derivedTile depth (children offset1 offset0)).s
        e := Nat.pair (derivedTile depth (children offset1 offset0)).e
          (derivedTile depth (children offset1 offset1)).e
        w := Nat.pair (derivedTile depth (children offset0 offset0)).w
          (derivedTile depth (children offset0 offset1)).w }

def derivedTileSet (depth : Nat) : TileSet :=
  ((List.finRange 104).map (derivedTile depth)).eraseDups

def derivedChildRectangle (depth : Nat) (parent : Index) : Rectangle 2 2 :=
  fun i j => derivedTile depth (childBlock parent i j)

def DerivedChildHMatches (depth : Nat) (left right : Index) : Prop :=
  WangTile.HMatches
      (derivedChildRectangle depth left offset1 offset0)
      (derivedChildRectangle depth right offset0 offset0) ∧
    WangTile.HMatches
      (derivedChildRectangle depth left offset1 offset1)
      (derivedChildRectangle depth right offset0 offset1)

def DerivedChildVMatches (depth : Nat) (lower upper : Index) : Prop :=
  WangTile.VMatches
      (derivedChildRectangle depth lower offset0 offset1)
      (derivedChildRectangle depth upper offset0 offset0) ∧
    WangTile.VMatches
      (derivedChildRectangle depth lower offset1 offset1)
      (derivedChildRectangle depth upper offset1 offset0)

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

end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
