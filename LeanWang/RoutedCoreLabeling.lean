/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.RoutedScaffold

/-!
# Logical labels for finite routed payload cores

A concrete scaffold should not have to rebuild payload-palette membership.
It labels active cells by logical tiles of a supplied fixed-corner square and
channel cells by the logical sources of their four edge colors.  A horizontal
channel equates its west and east sources, while a vertical channel equates its
south and north sources.  The other two colors remain free, as required by the
definition of `routedPayloads`.
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

/-- A symbolic source for one payload-palette color. -/
inductive EdgeLabel (n : Nat) where
  | zero
  | north (column row : Fin n)
  | south (column row : Fin n)
  | east (column row : Fin n)
  | west (column row : Fin n)

namespace EdgeLabel

/-- Interpret a symbolic edge source in a supplied logical square. -/
def color
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n) : EdgeLabel n → Nat
  | .zero => 0
  | .north column row => (square.tile column row).n
  | .south column row => (square.tile column row).s
  | .east column row => (square.tile column row).e
  | .west column row => (square.tile column row).w

/-- Every symbolic edge source denotes a member of the complete payload
palette. -/
theorem color_mem_payloadPalette
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n) (edge : EdgeLabel n) :
    edge.color square ∈ payloadPalette T := by
  cases edge with
  | zero => exact zero_mem_payloadPalette T
  | north column row =>
      exact mem_payloadPalette_n (square.valid.1 column row)
  | south column row =>
      exact mem_payloadPalette_s (square.valid.1 column row)
  | east column row =>
      exact mem_payloadPalette_e (square.valid.1 column row)
  | west column row =>
      exact mem_payloadPalette_w (square.valid.1 column row)

/-- Two symbolic sources that denote the same color in every valid logical
square.  Besides literal identity, consecutive logical tiles contribute the
two matching edge pairs. -/
inductive Compatible : EdgeLabel n → EdgeLabel n → Prop where
  | refl (edge : EdgeLabel n) : Compatible edge edge
  | horizontal (column row : Fin n) (next : column.val + 1 < n) :
      Compatible (.east column row) (.west ⟨column.val + 1, next⟩ row)
  | vertical (column row : Fin n) (next : row.val + 1 < n) :
      Compatible (.north column row) (.south column ⟨row.val + 1, next⟩)

theorem Compatible.color_eq
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n)
    {first second : EdgeLabel n} (compatible : Compatible first second) :
    first.color square = second.color square := by
  cases compatible with
  | refl => rfl
  | horizontal column row next => exact square.valid.2.1 column row next
  | vertical column row next => exact square.valid.2.2 column row next

end EdgeLabel

/-- Logical meaning of one physical scaffold cell. Channel labels expose all
four symbolic edge colors; only the axis selected by the role must transmit. -/
inductive Label (n : Nat) where
  | inactive
  | tile (column row : Fin n)
  | channel (north south east west : EdgeLabel n)

namespace Label

/-- The payload represented by a logical label. -/
def payload
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n) : Label n → WangTile
  | .inactive => { n := 0, s := 0, e := 0, w := 0 }
  | .tile column row => square.tile column row
  | .channel north south east west =>
      { n := north.color square, s := south.color square,
        e := east.color square, w := west.color square }

def north : Label n → EdgeLabel n
  | .inactive => .zero
  | .tile column row => .north column row
  | .channel north _ _ _ => north

def south : Label n → EdgeLabel n
  | .inactive => .zero
  | .tile column row => .south column row
  | .channel _ south _ _ => south

def east : Label n → EdgeLabel n
  | .inactive => .zero
  | .tile column row => .east column row
  | .channel _ _ east _ => east

def west : Label n → EdgeLabel n
  | .inactive => .zero
  | .tile column row => .west column row
  | .channel _ _ _ west => west

@[simp] theorem payload_north
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n) (label : Label n) :
    (payload square label).n = label.north.color square := by
  cases label <;> rfl

@[simp] theorem payload_south
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n) (label : Label n) :
    (payload square label).s = label.south.color square := by
  cases label <;> rfl

@[simp] theorem payload_east
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n) (label : Label n) :
    (payload square label).e = label.east.color square := by
  cases label <;> rfl

@[simp] theorem payload_west
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n) (label : Label n) :
    (payload square label).w = label.west.color square := by
  cases label <;> rfl

/-- A label has the membership behavior required by its scaffold role. -/
def FitsRole : Label n → RouteRole → Prop
  | .inactive, .inactive => True
  | .tile _ _, .active => True
  | .tile column row, .corner => column.val = 0 ∧ row.val = 0
  | .channel _ _ east west, .horizontal => west = east
  | .channel north south _ _, .vertical => south = north
  | _, _ => False

/-- Symbolic equality on the shared edge is sufficient for horizontal payload
matching. -/
def HCompatible (first second : Label n) : Prop :=
  EdgeLabel.Compatible first.east second.west

/-- Symbolic equality on the shared edge is sufficient for vertical payload
matching. -/
def VCompatible (lower upper : Label n) : Prop :=
  EdgeLabel.Compatible lower.north upper.south

theorem payload_hmatch
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n)
    {first second : Label n} (compatible : HCompatible first second) :
    WangTile.HMatches (payload square first) (payload square second) := by
  simpa only [WangTile.HMatches, payload_east, payload_west] using
    compatible.color_eq square

theorem payload_vmatch
    {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n)
    {first second : Label n} (compatible : VCompatible first second) :
    WangTile.VMatches (payload square first) (payload square second) := by
  simpa only [WangTile.VMatches, payload_north, payload_south] using
    compatible.color_eq square

theorem payload_mem_routedPayloads
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {n : Nat}
    (square : FixedCornerSquareData T seed n)
    {base : WangTile} {label : Label n}
    (fits : FitsRole label (S.role base)) :
    payload square label ∈ routedPayloads S T seed base := by
  rw [mem_routedPayloads_iff]
  cases hrole : S.role base with
  | inactive =>
      simp only [hrole] at fits ⊢
      cases label with
      | inactive =>
          simpa [payload] using mk_mem_completePayloads (T := T)
            (zero_mem_payloadPalette T) (zero_mem_payloadPalette T)
            (zero_mem_payloadPalette T) (zero_mem_payloadPalette T)
      | tile => simp [FitsRole] at fits
      | channel => simp [FitsRole] at fits
  | horizontal =>
      simp only [hrole] at fits ⊢
      cases label with
      | inactive => simp [FitsRole] at fits
      | tile => simp [FitsRole] at fits
      | channel north south east west =>
          refine ⟨?_, ?_⟩
          · simpa [payload] using mk_mem_completePayloads (T := T)
              (north.color_mem_payloadPalette square)
              (south.color_mem_payloadPalette square)
              (east.color_mem_payloadPalette square)
              (west.color_mem_payloadPalette square)
          · simpa [payload] using congrArg (EdgeLabel.color square) fits
  | vertical =>
      simp only [hrole] at fits ⊢
      cases label with
      | inactive => simp [FitsRole] at fits
      | tile => simp [FitsRole] at fits
      | channel north south east west =>
          refine ⟨?_, ?_⟩
          · simpa [payload] using mk_mem_completePayloads (T := T)
              (north.color_mem_payloadPalette square)
              (south.color_mem_payloadPalette square)
              (east.color_mem_payloadPalette square)
              (west.color_mem_payloadPalette square)
          · simpa [payload] using congrArg (EdgeLabel.color square) fits
  | active =>
      simp only [hrole] at fits ⊢
      cases label with
      | inactive => simp [FitsRole] at fits
      | tile column row => simpa [payload] using square.valid.1 column row
      | channel => simp [FitsRole] at fits
  | corner =>
      simp only [hrole] at fits ⊢
      cases label with
      | inactive => simp [FitsRole] at fits
      | tile column row =>
          simp only [FitsRole] at fits
          rcases fits with ⟨columnZero, rowZero⟩
          have columnEq : column = ⟨0, square.positive⟩ := Fin.ext columnZero
          have rowEq : row = ⟨0, square.positive⟩ := Fin.ext rowZero
          subst column
          subst row
          exact ⟨by simpa [payload] using square.valid.1 _ _,
            by simpa [payload] using square.corner⟩
      | channel => simp [FitsRole] at fits

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
