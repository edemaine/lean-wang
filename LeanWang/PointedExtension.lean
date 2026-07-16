/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic

/-!
# Pointed full-plane extensions

A seeded first-quadrant tileset can be completed to a pointed full-plane
tileset.  A finite position layer divides the plane at the distinguished tile
into four regions.  The northeast quadrant carries the original tileset, the
west and south regions carry boundary colors along straight wires, and the
southwest quadrant carries a zero filler.

The construction serves two purposes in the final reduction.  A seeded
quarter-plane tiling extends to a full-plane tiling whose origin is the
distinguished tile.  Conversely, every finite square whose southwest tile is
distinguished lies in the northeast region and therefore decodes to a seeded
square of the original tileset.
-/

namespace LeanWang
namespace PointedExtension

/-- Position of a cell relative to one distinguished coordinate axis. -/
inductive AxisClass where
  | negative
  | origin
  | positive
deriving DecidableEq, Repr

namespace AxisClass

/-- Color immediately before a class along its coordinate axis. -/
def before : AxisClass → Nat
  | .negative | .origin => 0
  | .positive => 1

/-- Color immediately after a class along its coordinate axis. -/
def after : AxisClass → Nat
  | .negative => 0
  | .origin | .positive => 1

/-- A separate code keeps the perpendicular class constant across an edge. -/
def code : AxisClass → Nat
  | .negative => 0
  | .origin => 1
  | .positive => 2

/-- Consecutive classes have matching axis colors. -/
def Step (left right : AxisClass) : Prop :=
  left.after = right.before

instance (left right : AxisClass) : Decidable (Step left right) := by
  unfold Step
  infer_instance

theorem code_injective : Function.Injective code := by
  intro first second equal
  cases first <;> cases second <;> simp [code] at equal ⊢

@[simp] theorem code_eq_code {first second : AxisClass} :
    first.code = second.code ↔ first = second :=
  code_injective.eq_iff

@[simp] theorem origin_step_iff {next : AxisClass} :
    Step .origin next ↔ next = .positive := by
  cases next <;> simp [Step, before, after]

@[simp] theorem positive_step_iff {next : AxisClass} :
    Step .positive next ↔ next = .positive := by
  cases next <;> simp [Step, before, after]

@[simp] theorem step_origin_iff {previous : AxisClass} :
    Step previous .origin ↔ previous = .negative := by
  cases previous <;> simp [Step, before, after]

@[simp] theorem step_negative_iff {previous : AxisClass} :
    Step previous .negative ↔ previous = .negative := by
  cases previous <;> simp [Step, before, after]

end AxisClass

/-- The finite Wang layer that records both coordinate-axis classes. -/
def positionTile (horizontal vertical : AxisClass) : WangTile where
  n := Nat.pair vertical.after horizontal.code
  s := Nat.pair vertical.before horizontal.code
  e := Nat.pair horizontal.after vertical.code
  w := Nat.pair horizontal.before vertical.code

@[simp] theorem positionTile_hMatches_iff
    {leftX leftY rightX rightY : AxisClass} :
    WangTile.HMatches (positionTile leftX leftY)
        (positionTile rightX rightY) ↔
      AxisClass.Step leftX rightX ∧ leftY = rightY := by
  simp [WangTile.HMatches, positionTile, AxisClass.Step,
    Nat.pair_eq_pair]

@[simp] theorem positionTile_vMatches_iff
    {lowerX lowerY upperX upperY : AxisClass} :
    WangTile.VMatches (positionTile lowerX lowerY)
        (positionTile upperX upperY) ↔
      AxisClass.Step lowerY upperY ∧ lowerX = upperX := by
  simp [WangTile.VMatches, positionTile, AxisClass.Step,
    Nat.pair_eq_pair]

/-- Payload used strictly southwest of the distinguished axes. -/
def zeroTile : WangTile :=
  { n := 0, s := 0, e := 0, w := 0 }

/-- West-half-plane padding that transmits one west boundary color. -/
def horizontalWire (tile : WangTile) : WangTile :=
  { n := 0, s := 0, e := tile.w, w := tile.w }

/-- South-half-plane padding that transmits one south boundary color. -/
def verticalWire (tile : WangTile) : WangTile :=
  { n := tile.s, s := tile.s, e := 0, w := 0 }

/-- Payloads allowed in one of the nine position regions. -/
def regionPayloads (T : TileSet) (seed : WangTile) :
    AxisClass → AxisClass → TileSet
  | .negative, .negative => [zeroTile]
  | .negative, .origin | .negative, .positive => T.map horizontalWire
  | .origin, .negative | .positive, .negative => T.map verticalWire
  | .origin, .origin => T.filter fun tile => tile = seed
  | .origin, .positive | .positive, .origin | .positive, .positive => T

/-- All three axis classes, used to enumerate the finite extension. -/
def axisClasses : List AxisClass :=
  [.negative, .origin, .positive]

theorem mem_axisClasses (axis : AxisClass) : axis ∈ axisClasses := by
  cases axis <;> simp [axisClasses]

/-- Extend every allowed region payload by its finite position layer. -/
def tiles (T : TileSet) (seed : WangTile) : TileSet :=
  axisClasses.flatMap fun horizontal =>
    axisClasses.flatMap fun vertical =>
      (regionPayloads T seed horizontal vertical).map fun payload =>
        WangTile.product (positionTile horizontal vertical) payload

/-- The original seed at the crossing of the two distinguished axes. -/
def pointedSeed (seed : WangTile) : WangTile :=
  WangTile.product (positionTile .origin .origin) seed

theorem mem_tiles_iff {T : TileSet} {seed tile : WangTile} :
    tile ∈ tiles T seed ↔
      ∃ horizontal vertical payload,
        payload ∈ regionPayloads T seed horizontal vertical ∧
          WangTile.product (positionTile horizontal vertical) payload = tile := by
  constructor
  · simp only [tiles, List.mem_flatMap, List.mem_map]
    rintro ⟨horizontal, _horizontalMem, vertical, _verticalMem,
      payload, payloadMem, rfl⟩
    exact ⟨horizontal, vertical, payload, payloadMem, rfl⟩
  · rintro ⟨horizontal, vertical, payload, payloadMem, rfl⟩
    simp only [tiles, List.mem_flatMap, List.mem_map]
    exact ⟨horizontal, mem_axisClasses horizontal,
      vertical, mem_axisClasses vertical, payload, payloadMem, rfl⟩

/-- A membership witness split into position and payload layers. -/
structure Decoded (T : TileSet) (seed tile : WangTile) where
  horizontal : AxisClass
  vertical : AxisClass
  payload : WangTile
  payload_mem : payload ∈ regionPayloads T seed horizontal vertical
  product_eq :
    WangTile.product (positionTile horizontal vertical) payload = tile

theorem nonempty_decoded_of_mem {T : TileSet} {seed tile : WangTile}
    (member : tile ∈ tiles T seed) : Nonempty (Decoded T seed tile) := by
  rcases mem_tiles_iff.1 member with
    ⟨horizontal, vertical, payload, payloadMem, productEq⟩
  exact ⟨⟨horizontal, vertical, payload, payloadMem, productEq⟩⟩

namespace Decoded

/-- Horizontal matching splits into an axis step, a fixed row class, and
payload matching. -/
theorem hMatches {T : TileSet} {seed left right : WangTile}
    (leftDecoded : Decoded T seed left)
    (rightDecoded : Decoded T seed right)
    (hmatch : WangTile.HMatches left right) :
    AxisClass.Step leftDecoded.horizontal rightDecoded.horizontal ∧
      leftDecoded.vertical = rightDecoded.vertical ∧
      WangTile.HMatches leftDecoded.payload rightDecoded.payload := by
  rw [← leftDecoded.product_eq, ← rightDecoded.product_eq,
    WangTile.HMatches_product_iff] at hmatch
  exact ⟨(positionTile_hMatches_iff.mp hmatch.1).1,
    (positionTile_hMatches_iff.mp hmatch.1).2, hmatch.2⟩

/-- Vertical matching splits into an axis step, a fixed column class, and
payload matching. -/
theorem vMatches {T : TileSet} {seed lower upper : WangTile}
    (lowerDecoded : Decoded T seed lower)
    (upperDecoded : Decoded T seed upper)
    (hmatch : WangTile.VMatches lower upper) :
    AxisClass.Step lowerDecoded.vertical upperDecoded.vertical ∧
      lowerDecoded.horizontal = upperDecoded.horizontal ∧
      WangTile.VMatches lowerDecoded.payload upperDecoded.payload := by
  rw [← lowerDecoded.product_eq, ← upperDecoded.product_eq,
    WangTile.VMatches_product_iff] at hmatch
  exact ⟨(positionTile_vMatches_iff.mp hmatch.1).1,
    (positionTile_vMatches_iff.mp hmatch.1).2, hmatch.2⟩

end Decoded

/-- Any payload in the closed northeast quadrant belongs to the source
tileset. -/
theorem mem_source_of_mem_regionPayloads
    {T : TileSet} {seed payload : WangTile}
    {horizontal vertical : AxisClass}
    (horizontalNonnegative : horizontal ≠ .negative)
    (verticalNonnegative : vertical ≠ .negative)
    (member : payload ∈ regionPayloads T seed horizontal vertical) :
    payload ∈ T := by
  cases horizontal <;> cases vertical <;>
    simp [regionPayloads] at horizontalNonnegative verticalNonnegative member ⊢
  exact member.1
  exact member
  exact member
  exact member

/-- The origin region contains only the prescribed source seed. -/
theorem eq_seed_of_mem_originPayloads
    {T : TileSet} {seed payload : WangTile}
    (member : payload ∈ regionPayloads T seed .origin .origin) :
    payload = seed := by
  exact (by simpa [regionPayloads] using member : payload ∈ T ∧ payload = seed).2

end PointedExtension
end LeanWang
