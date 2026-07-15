/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.RoutedScaffold

/-!
# Logical labels for finite routed payload cores

A concrete scaffold should not have to rebuild payload-palette membership.
It labels each constrained physical cell by a logical tile of a supplied
fixed-corner square or by one of the two wires carrying an edge of that tile.
The small compatibility relations below are independent of the tileset; their
soundness uses only the matching equations of the supplied square.
-/

namespace LeanWang
namespace RoutedCoreLabeling

/-- Data extracted from one nonempty fixed-corner square. -/
structure FixedCornerSquareData (T : TileSet) (seed : WangTile) (n : Nat) where
  positive : 0 < n
  tile : Rectangle n n
  valid : ValidRectangle T tile
  corner : tile ⟨0, positive⟩ ⟨0, positive⟩ = seed

theorem FixedCornerSquareData.nonempty
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : TileableFixedCornerSquare T seed n) :
    Nonempty (FixedCornerSquareData T seed n) := by
  rcases square with ⟨positive, tile, valid, corner⟩
  exact ⟨⟨positive, tile, valid, corner⟩⟩

/-- Logical meaning of one physical scaffold cell. Wire labels may continue
beyond the last logical crossing visible in a finite box. -/
inductive Label (n : Nat) where
  | inactive
  | tile (column row : Fin n)
  | horizontal (column row : Fin n)
  | vertical (column row : Fin n)

namespace Label

/-- The payload represented by a logical label. -/
def payload
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n) : Label n → WangTile
  | .inactive => { n := 0, s := 0, e := 0, w := 0 }
  | .tile column row => square.tile column row
  | .horizontal column row =>
      { n := 0, s := 0,
        e := (square.tile column row).e,
        w := (square.tile column row).e }
  | .vertical column row =>
      { n := (square.tile column row).n,
        s := (square.tile column row).n,
        e := 0, w := 0 }

/-- A label has the membership behavior required by its scaffold role. -/
def FitsRole : Label n → RouteRole → Prop
  | .inactive, .inactive => True
  | .tile _ _, .active => True
  | .tile column row, .corner => column.val = 0 ∧ row.val = 0
  | .horizontal _ _, .horizontal => True
  | .vertical _ _, .vertical => True
  | _, _ => False

/-- Horizontal adjacency patterns that are valid for every payload square. -/
inductive HCompatible : Label n → Label n → Prop where
  | inactive : HCompatible .inactive .inactive
  | vertical
      (firstColumn firstRow secondColumn secondRow : Fin n) :
      HCompatible (.vertical firstColumn firstRow)
        (.vertical secondColumn secondRow)
  | tile_horizontal (column row : Fin n) :
      HCompatible (.tile column row) (.horizontal column row)
  | horizontal_horizontal (column row : Fin n) :
      HCompatible (.horizontal column row) (.horizontal column row)
  | horizontal_tile (column row : Fin n) (next : column.val + 1 < n) :
      HCompatible (.horizontal column row)
        (.tile ⟨column.val + 1, next⟩ row)
  | tile_tile (column row : Fin n) (next : column.val + 1 < n) :
      HCompatible (.tile column row) (.tile ⟨column.val + 1, next⟩ row)

/-- Vertical adjacency patterns that are valid for every payload square. -/
inductive VCompatible : Label n → Label n → Prop where
  | inactive : VCompatible .inactive .inactive
  | horizontal
      (firstColumn firstRow secondColumn secondRow : Fin n) :
      VCompatible (.horizontal firstColumn firstRow)
        (.horizontal secondColumn secondRow)
  | tile_vertical (column row : Fin n) :
      VCompatible (.tile column row) (.vertical column row)
  | vertical_vertical (column row : Fin n) :
      VCompatible (.vertical column row) (.vertical column row)
  | vertical_tile (column row : Fin n) (next : row.val + 1 < n) :
      VCompatible (.vertical column row)
        (.tile column ⟨row.val + 1, next⟩)
  | tile_tile (column row : Fin n) (next : row.val + 1 < n) :
      VCompatible (.tile column row) (.tile column ⟨row.val + 1, next⟩)

theorem payload_hmatch
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n)
    {first second : Label n} (compatible : HCompatible first second) :
    WangTile.HMatches (payload square first) (payload square second) := by
  cases compatible with
  | inactive => rfl
  | vertical => rfl
  | tile_horizontal => rfl
  | horizontal_horizontal => rfl
  | horizontal_tile column row next =>
      exact square.valid.2.1 column row next
  | tile_tile column row next =>
      exact square.valid.2.1 column row next

theorem payload_vmatch
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n)
    {first second : Label n} (compatible : VCompatible first second) :
    WangTile.VMatches (payload square first) (payload square second) := by
  cases compatible with
  | inactive => rfl
  | horizontal => rfl
  | tile_vertical => rfl
  | vertical_vertical => rfl
  | vertical_tile column row next =>
      exact square.valid.2.2 column row next
  | tile_tile column row next =>
      exact square.valid.2.2 column row next

theorem payload_mem_routedPayloads
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n)
    {base : WangTile} {label : Label n}
    (fits : FitsRole label (S.role base)) :
    payload square label ∈ routedPayloads S T seed base := by
  rw [mem_routedPayloads_iff]
  cases hrole : S.role base <;> cases label <;>
    simp only [hrole] at fits ⊢ <;> simp [FitsRole] at fits
  · simpa [payload] using mk_mem_completePayloads (T := T)
      (zero_mem_payloadPalette T) (zero_mem_payloadPalette T)
      (zero_mem_payloadPalette T) (zero_mem_payloadPalette T)
  · rename_i column row
    have edge := mem_payloadPalette_e (square.valid.1 column row)
    refine ⟨?_, rfl⟩
    simpa [payload] using mk_mem_completePayloads (T := T)
      (zero_mem_payloadPalette T) (zero_mem_payloadPalette T) edge edge
  · rename_i column row
    have edge := mem_payloadPalette_n (square.valid.1 column row)
    refine ⟨?_, rfl⟩
    simpa [payload] using mk_mem_completePayloads (T := T)
      edge edge (zero_mem_payloadPalette T) (zero_mem_payloadPalette T)
  · simpa [payload] using square.valid.1 _ _
  · rename_i column row
    rcases fits with ⟨columnZero, rowZero⟩
    have columnEq : column = ⟨0, square.positive⟩ := Fin.ext columnZero
    have rowEq : row = ⟨0, square.positive⟩ := Fin.ext rowZero
    subst column
    subst row
    exact ⟨by simpa [payload] using square.valid.1 _ _, by simpa [payload] using
      square.corner⟩

end Label

/-- A finite scaffold box labeled by one logical fixed-corner square. -/
structure Labeling (S : RoutedScaffold) (r n : Nat) where
  base : BoxPattern S.tiles r
  label : Box r → Label n
  base_valid : ValidBoxTiling S.tiles r base
  fits : ∀ p : Box r, (label p).FitsRole (S.role (base p).1)
  hcompatible :
    ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
      (S.role (base p).1).isConstrained = true →
      (S.role (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1).isConstrained = true →
      Label.HCompatible (label p)
        (label ⟨(p.1.1 + 1, p.1.2), hp⟩)
  vcompatible :
    ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
      (S.role (base p).1).isConstrained = true →
      (S.role (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1).isConstrained = true →
      Label.VCompatible (label p)
        (label ⟨(p.1.1, p.1.2 + 1), hp⟩)

/-- Interpret a logical labeling as the routed payload core required by the
generic compactness construction. -/
def Labeling.toRoutedCoreBoxLayerPatch
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {r n : Nat}
    (labeling : Labeling S r n)
    (square : FixedCornerSquareData T seed n) :
    RoutedCoreBoxLayerPatch S T seed r where
  base := labeling.base
  core := fun p => (labeling.label p).payload square
  base_valid := labeling.base_valid
  core_mem := fun p => Label.payload_mem_routedPayloads square (labeling.fits p)
  core_hmatch := by
    intro p hp left right
    exact Label.payload_hmatch square
      (labeling.hcompatible p hp left right)
  core_vmatch := by
    intro p hp lower upper
    exact Label.payload_vmatch square
      (labeling.vcompatible p hp lower upper)

/-- Pure scaffold geometry sufficient to route a logical square through every
finite box.  The logical square size may depend on the requested box radius. -/
def HasRoutedCoreLabelings (S : RoutedScaffold) : Prop :=
  ∀ r : Nat, ∃ n : Nat, 0 < n ∧ Nonempty (Labeling S r n)

/-- Logical scaffold labelings construct routed cores for every tileset with
fixed-corner squares of all positive sizes. -/
theorem hasRoutedCoreBoxLayerPatches_of_labelings
    {S : RoutedScaffold} (labelings : HasRoutedCoreLabelings S) :
    HasRoutedCoreBoxLayerPatches S := by
  intro T seed squares r
  rcases labelings r with ⟨n, positive, ⟨labeling⟩⟩
  rcases FixedCornerSquareData.nonempty (squares n positive) with ⟨square⟩
  exact ⟨labeling.toRoutedCoreBoxLayerPatch square⟩

end RoutedCoreLabeling
end LeanWang
