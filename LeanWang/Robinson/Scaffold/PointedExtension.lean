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

def toCode : AxisClass → Option Bool
  | .negative => none
  | .origin => some false
  | .positive => some true

def ofCode : Option Bool → AxisClass
  | none => .negative
  | some false => .origin
  | some true => .positive

def equivCode : AxisClass ≃ Option Bool where
  toFun := toCode
  invFun := ofCode
  left_inv := by intro axis; cases axis <;> rfl
  right_inv := by
    intro code
    cases code with
    | none => rfl
    | some value => cases value <;> rfl

instance instPrimcodable : Primcodable AxisClass :=
  Primcodable.ofEquiv (Option Bool) equivCode

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

theorem before_primrec : Primrec before := by
  have positive : PrimrecPred (fun axis : AxisClass => axis = .positive) :=
    Primrec.eq.comp Primrec.id (Primrec.const AxisClass.positive)
  exact (Primrec.ite positive (Primrec.const 1) (Primrec.const 0)).of_eq
    fun axis => by cases axis <;> rfl

theorem after_primrec : Primrec after := by
  have negative : PrimrecPred (fun axis : AxisClass => axis = .negative) :=
    Primrec.eq.comp Primrec.id (Primrec.const AxisClass.negative)
  exact (Primrec.ite negative (Primrec.const 0) (Primrec.const 1)).of_eq
    fun axis => by cases axis <;> rfl

theorem code_primrec : Primrec code := by
  have negative : PrimrecPred (fun axis : AxisClass => axis = .negative) :=
    Primrec.eq.comp Primrec.id (Primrec.const AxisClass.negative)
  have origin : PrimrecPred (fun axis : AxisClass => axis = .origin) :=
    Primrec.eq.comp Primrec.id (Primrec.const AxisClass.origin)
  exact (Primrec.ite negative (Primrec.const 0)
    (Primrec.ite origin (Primrec.const 1) (Primrec.const 2))).of_eq
      fun axis => by cases axis <;> rfl

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

theorem positionTile_injective :
    Function.Injective
      (fun classes : AxisClass × AxisClass =>
        positionTile classes.1 classes.2) := by
  intro first second equal
  apply Prod.ext
  · apply AxisClass.code_injective
    simpa [positionTile] using
      congrArg (fun tile : WangTile => tile.s.unpair.2) equal
  · apply AxisClass.code_injective
    simpa [positionTile] using
      congrArg (fun tile : WangTile => tile.w.unpair.2) equal

theorem positionTile_primrec :
    Primrec (fun classes : AxisClass × AxisClass =>
      positionTile classes.1 classes.2) := by
  have tuple : Primrec (fun classes : AxisClass × AxisClass =>
      (Nat.pair classes.2.after classes.1.code,
        Nat.pair classes.2.before classes.1.code,
        Nat.pair classes.1.after classes.2.code,
        Nat.pair classes.1.before classes.2.code)) :=
    Primrec.pair
    (Primrec₂.natPair.comp
      (AxisClass.after_primrec.comp Primrec.snd)
      (AxisClass.code_primrec.comp Primrec.fst))
    (Primrec.pair
      (Primrec₂.natPair.comp
        (AxisClass.before_primrec.comp Primrec.snd)
        (AxisClass.code_primrec.comp Primrec.fst))
      (Primrec.pair
        (Primrec₂.natPair.comp
          (AxisClass.after_primrec.comp Primrec.fst)
          (AxisClass.code_primrec.comp Primrec.snd))
        (Primrec₂.natPair.comp
          (AxisClass.before_primrec.comp Primrec.fst)
          (AxisClass.code_primrec.comp Primrec.snd))))
  exact (WangTile.ofTuple_primrec.comp tuple).of_eq fun _ => rfl

/-- Payload used strictly southwest of the distinguished axes. -/
def zeroTile : WangTile :=
  { n := 0, s := 0, e := 0, w := 0 }

/-- West-half-plane padding that transmits one west boundary color. -/
def horizontalWire (tile : WangTile) : WangTile :=
  { n := 0, s := 0, e := tile.w, w := tile.w }

/-- South-half-plane padding that transmits one south boundary color. -/
def verticalWire (tile : WangTile) : WangTile :=
  { n := tile.s, s := tile.s, e := 0, w := 0 }

theorem horizontalWire_primrec : Primrec horizontalWire := by
  have tuple : Primrec (fun tile : WangTile =>
      (0, 0, tile.w, tile.w)) :=
    Primrec.pair (Primrec.const 0)
    (Primrec.pair (Primrec.const 0)
      (Primrec.pair WangTile.w_primrec WangTile.w_primrec))
  exact (WangTile.ofTuple_primrec.comp tuple).of_eq fun _ => rfl

theorem verticalWire_primrec : Primrec verticalWire := by
  have tuple : Primrec (fun tile : WangTile =>
      (tile.s, tile.s, 0, 0)) :=
    Primrec.pair WangTile.s_primrec
    (Primrec.pair WangTile.s_primrec
      (Primrec.pair (Primrec.const 0) (Primrec.const 0)))
  exact (WangTile.ofTuple_primrec.comp tuple).of_eq fun _ => rfl

/-- Payloads allowed in one of the nine position regions. -/
def regionPayloads (T : TileSet) (seed : WangTile) :
    AxisClass → AxisClass → TileSet
  | .negative, .negative => [zeroTile]
  | .negative, .origin | .negative, .positive => T.map horizontalWire
  | .origin, .negative | .positive, .negative => T.map verticalWire
  | .origin, .origin => T.filter fun tile => tile = seed
  | .origin, .positive | .positive, .origin | .positive, .positive => T

theorem regionPayloads_primrec :
    Primrec (fun input : (TileSet × WangTile) × (AxisClass × AxisClass) =>
      regionPayloads input.1.1 input.1.2 input.2.1 input.2.2) := by
  let horizontal : (TileSet × WangTile) × (AxisClass × AxisClass) → AxisClass :=
    fun input => input.2.1
  let vertical : (TileSet × WangTile) × (AxisClass × AxisClass) → AxisClass :=
    fun input => input.2.2
  have hhorizontal : Primrec horizontal := Primrec.fst.comp Primrec.snd
  have hvertical : Primrec vertical := Primrec.snd.comp Primrec.snd
  have horizontalNegative : PrimrecPred (fun input => horizontal input = .negative) :=
    Primrec.eq.comp hhorizontal (Primrec.const AxisClass.negative)
  have verticalNegative : PrimrecPred (fun input => vertical input = .negative) :=
    Primrec.eq.comp hvertical (Primrec.const AxisClass.negative)
  have horizontalOrigin : PrimrecPred (fun input => horizontal input = .origin) :=
    Primrec.eq.comp hhorizontal (Primrec.const AxisClass.origin)
  have verticalOrigin : PrimrecPred (fun input => vertical input = .origin) :=
    Primrec.eq.comp hvertical (Primrec.const AxisClass.origin)
  have source : Primrec (fun input :
      (TileSet × WangTile) × (AxisClass × AxisClass) => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have horizontalWires : Primrec (fun input :
      (TileSet × WangTile) × (AxisClass × AxisClass) =>
        input.1.1.map horizontalWire) := by
    refine Primrec.list_map source ?_
    apply Primrec₂.mk
    exact horizontalWire_primrec.comp Primrec.snd
  have verticalWires : Primrec (fun input :
      (TileSet × WangTile) × (AxisClass × AxisClass) =>
        input.1.1.map verticalWire) := by
    refine Primrec.list_map source ?_
    apply Primrec₂.mk
    exact verticalWire_primrec.comp Primrec.snd
  have seedOnly : Primrec (fun input :
      (TileSet × WangTile) × (AxisClass × AxisClass) =>
        input.1.1.filter fun tile => tile = input.1.2) :=
    (PrimrecRel.listFilter
      (R := fun tile seed : WangTile => tile = seed) Primrec.eq).comp
        (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have origin : PrimrecPred (fun input =>
      horizontal input = .origin ∧ vertical input = .origin) :=
    horizontalOrigin.and verticalOrigin
  exact (Primrec.ite horizontalNegative
    (Primrec.ite verticalNegative (Primrec.const [zeroTile]) horizontalWires)
    (Primrec.ite verticalNegative verticalWires
      (Primrec.ite origin seedOnly source))).of_eq fun input => by
        rcases input with ⟨⟨T, seed⟩, horizontalClass, verticalClass⟩
        cases horizontalClass <;> cases verticalClass <;>
          simp [horizontal, vertical, regionPayloads]

/-- All three axis classes, used to enumerate the finite extension. -/
def axisClasses : List AxisClass :=
  [.negative, .origin, .positive]

theorem mem_axisClasses (axis : AxisClass) : axis ∈ axisClasses := by
  cases axis <;> simp [axisClasses]

/-- Add the position layer to every payload allowed in one region. -/
def tilesForRegion
    (input : (TileSet × WangTile) × (AxisClass × AxisClass)) : TileSet :=
  (regionPayloads input.1.1 input.1.2 input.2.1 input.2.2).map fun payload =>
    WangTile.product (positionTile input.2.1 input.2.2) payload

theorem tilesForRegion_primrec : Primrec tilesForRegion := by
  refine Primrec.list_map regionPayloads_primrec ?_
  apply Primrec₂.mk
  have position : Primrec (fun input :
      ((TileSet × WangTile) × (AxisClass × AxisClass)) × WangTile =>
        positionTile input.1.2.1 input.1.2.2) :=
    positionTile_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  exact WangTile.product_primrec.comp (Primrec.pair position Primrec.snd)

/-- Enumerate all vertical regions for one horizontal axis class. -/
def tilesForHorizontal
    (input : (TileSet × WangTile) × AxisClass) : TileSet :=
  axisClasses.flatMap fun vertical =>
    tilesForRegion (input.1, input.2, vertical)

theorem tilesForHorizontal_primrec : Primrec tilesForHorizontal := by
  refine Primrec.list_flatMap (Primrec.const axisClasses) ?_
  apply Primrec₂.mk
  exact tilesForRegion_primrec.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))

/-- Extend every allowed region payload by its finite position layer. -/
def tiles (T : TileSet) (seed : WangTile) : TileSet :=
  axisClasses.flatMap fun horizontal =>
    tilesForHorizontal ((T, seed), horizontal)

/-- The original seed at the crossing of the two distinguished axes. -/
def pointedSeed (seed : WangTile) : WangTile :=
  WangTile.product (positionTile .origin .origin) seed

theorem tiles_primrec :
    Primrec (fun input : TileSet × WangTile => tiles input.1 input.2) := by
  unfold tiles
  refine Primrec.list_flatMap (Primrec.const axisClasses) ?_
  apply Primrec₂.mk
  exact tilesForHorizontal_primrec

theorem pointedSeed_primrec : Primrec pointedSeed := by
  exact WangTile.product_primrec.comp
    (Primrec.pair (Primrec.const (positionTile .origin .origin)) Primrec.id)

/-- Computable pointed extension of a finite seeded tileset. -/
def data (input : TileSet × WangTile) : TileSet × WangTile :=
  (tiles input.1 input.2, pointedSeed input.2)

theorem data_primrec : Primrec data := by
  exact Primrec.pair tiles_primrec (pointedSeed_primrec.comp Primrec.snd)

theorem data_computable : Computable data :=
  data_primrec.to_comp

theorem mem_tiles_iff {T : TileSet} {seed tile : WangTile} :
    tile ∈ tiles T seed ↔
      ∃ horizontal vertical payload,
        payload ∈ regionPayloads T seed horizontal vertical ∧
          WangTile.product (positionTile horizontal vertical) payload = tile := by
  constructor
  · simp only [tiles, tilesForHorizontal, tilesForRegion,
      List.mem_flatMap, List.mem_map]
    rintro ⟨horizontal, _horizontalMem, vertical, _verticalMem,
      payload, payloadMem, rfl⟩
    exact ⟨horizontal, vertical, payload, payloadMem, rfl⟩
  · rintro ⟨horizontal, vertical, payload, payloadMem, rfl⟩
    simp only [tiles, tilesForHorizontal, tilesForRegion,
      List.mem_flatMap, List.mem_map]
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

private theorem AxisClass.nonnegative_of_step {left right : AxisClass}
    (step : Step left right) (nonnegative : left ≠ .negative) :
    right ≠ .negative := by
  cases left <;> cases right <;>
    simp_all [Step, before, after]

/-- A finite axis-class line starting at the origin never becomes negative. -/
private theorem axisLine_nonnegative {n : Nat} (positive : 0 < n)
    (line : Fin n → AxisClass)
    (origin : line ⟨0, positive⟩ = .origin)
    (step : ∀ (k : Nat) (hk : k + 1 < n),
      AxisClass.Step (line ⟨k, by omega⟩) (line ⟨k + 1, hk⟩)) :
    ∀ index, line index ≠ .negative := by
  intro index
  have claim : ∀ k : Nat, ∀ hk : k < n,
      line ⟨k, hk⟩ ≠ .negative := by
    intro k
    induction k with
    | zero =>
        intro hk
        have indexEq : (⟨0, hk⟩ : Fin n) = ⟨0, positive⟩ := Fin.ext rfl
        rw [indexEq, origin]
        simp
    | succ k inductionHypothesis =>
        intro hk
        have previousBound : k < n := by omega
        exact AxisClass.nonnegative_of_step (step k hk)
          (inductionHypothesis previousBound)
  exact claim index.val index.isLt

/-- Adjacent equality makes a finite line constant from its zeroth entry. -/
private theorem axisLine_eq_zero {α : Type} {n : Nat} (positive : 0 < n)
    (line : Fin n → α)
    (adjacent : ∀ (k : Nat) (hk : k + 1 < n),
      line ⟨k, by omega⟩ = line ⟨k + 1, hk⟩) :
    ∀ index, line index = line ⟨0, positive⟩ := by
  intro index
  have claim : ∀ k : Nat, ∀ hk : k < n,
      line ⟨k, hk⟩ = line ⟨0, positive⟩ := by
    intro k
    induction k with
    | zero =>
        intro hk
        congr 1
    | succ k inductionHypothesis =>
        intro hk
        have previousBound : k < n := by omega
        exact (adjacent k hk).symm.trans
          (inductionHypothesis previousBound)
  exact claim index.val index.isLt

/-- A position-class grid is nonnegative when its primary axis steps from the
origin and its perpendicular axis preserves the class. -/
private theorem axisGrid_nonnegative {n : Nat} (positive : 0 < n)
    (grid : Fin n → Fin n → AxisClass)
    (origin : grid ⟨0, positive⟩ ⟨0, positive⟩ = .origin)
    (alongStep : ∀ (k : Nat) (hk : k + 1 < n),
      AxisClass.Step (grid ⟨k, by omega⟩ ⟨0, positive⟩)
        (grid ⟨k + 1, hk⟩ ⟨0, positive⟩))
    (acrossEq : ∀ (along : Fin n) (k : Nat) (hk : k + 1 < n),
      grid along ⟨k, by omega⟩ = grid along ⟨k + 1, hk⟩) :
    ∀ along across, grid along across ≠ .negative := by
  intro along across
  rw [axisLine_eq_zero positive (line := grid along) (acrossEq along) across]
  exact axisLine_nonnegative positive
    (line := fun along => grid along ⟨0, positive⟩)
    origin alongStep along

/-- Every square rooted at the pointed tile decodes to a square rooted at the
source seed. -/
theorem source_fixedCornerSquare_of_extension
    {T : TileSet} {seed : WangTile} {n : Nat} :
    TileableFixedCornerSquare (tiles T seed) (pointedSeed seed) n →
      TileableFixedCornerSquare T seed n := by
  classical
  rintro ⟨positive, rectangle, valid, corner⟩
  let decoded (column row : Fin n) : Decoded T seed (rectangle column row) :=
    Classical.choice (nonempty_decoded_of_mem (valid.1 column row))
  let zero : Fin n := ⟨0, positive⟩
  have cornerPair :
      (positionTile (decoded zero zero).horizontal (decoded zero zero).vertical,
          (decoded zero zero).payload) =
        (positionTile .origin .origin, seed) := by
    apply WangTile.product_injective
    exact (decoded zero zero).product_eq.trans corner
  have cornerClasses :
      ((decoded zero zero).horizontal, (decoded zero zero).vertical) =
        (.origin, .origin) := by
    apply positionTile_injective
    exact congrArg Prod.fst cornerPair
  have cornerHorizontal : (decoded zero zero).horizontal = .origin :=
    congrArg (fun classes => classes.1) cornerClasses
  have cornerVertical : (decoded zero zero).vertical = .origin :=
    congrArg (fun classes => classes.2) cornerClasses
  have cornerPayload : (decoded zero zero).payload = seed :=
    congrArg Prod.snd cornerPair
  have horizontalNonnegative (column row : Fin n) :
      (decoded column row).horizontal ≠ .negative := by
    refine axisGrid_nonnegative positive
      (grid := fun column row => (decoded column row).horizontal)
      cornerHorizontal ?_ ?_ column row
    · intro k hk
      exact (Decoded.hMatches
        (decoded ⟨k, by omega⟩ zero)
        (decoded ⟨k + 1, hk⟩ zero)
        (valid.2.1 ⟨k, by omega⟩ zero hk)).1
    · intro fixed k hk
      exact (Decoded.vMatches
        (decoded fixed ⟨k, by omega⟩)
        (decoded fixed ⟨k + 1, hk⟩)
        (valid.2.2 fixed ⟨k, by omega⟩ hk)).2.1
  have verticalNonnegative (column row : Fin n) :
      (decoded column row).vertical ≠ .negative := by
    refine axisGrid_nonnegative positive
      (grid := fun row column => (decoded column row).vertical)
      cornerVertical ?_ ?_ row column
    · intro k hk
      exact (Decoded.vMatches
        (decoded zero ⟨k, by omega⟩)
        (decoded zero ⟨k + 1, hk⟩)
        (valid.2.2 zero ⟨k, by omega⟩ hk)).1
    · intro fixed k hk
      exact (Decoded.hMatches
        (decoded ⟨k, by omega⟩ fixed)
        (decoded ⟨k + 1, hk⟩ fixed)
        (valid.2.1 ⟨k, by omega⟩ fixed hk)).2.1
  let payloadRectangle : Rectangle n n :=
    fun column row => (decoded column row).payload
  refine ⟨positive, payloadRectangle, ?_, ?_⟩
  · constructor
    · intro column row
      exact mem_source_of_mem_regionPayloads
        (horizontalNonnegative column row)
        (verticalNonnegative column row)
        (decoded column row).payload_mem
    constructor
    · intro column row next
      exact (Decoded.hMatches (decoded column row)
        (decoded ⟨column.val + 1, next⟩ row)
        (valid.2.1 column row next)).2.2
    · intro column row next
      exact (Decoded.vMatches (decoded column row)
        (decoded column ⟨row.val + 1, next⟩)
        (valid.2.2 column row next)).2.2
  · exact cornerPayload

/-- Axis class of an integer coordinate relative to zero. -/
def classOfInt (coordinate : Int) : AxisClass :=
  if coordinate < 0 then .negative
  else if coordinate = 0 then .origin
  else .positive

@[simp] theorem classOfInt_zero : classOfInt 0 = .origin := by
  simp [classOfInt]

theorem classOfInt_of_negative {coordinate : Int} (negative : coordinate < 0) :
    classOfInt coordinate = .negative := by
  simp [classOfInt, negative]

theorem classOfInt_of_positive {coordinate : Int} (positive : 0 < coordinate) :
    classOfInt coordinate = .positive := by
  simp [classOfInt, not_lt_of_ge positive.le, ne_of_gt positive]

theorem classOfInt_step (coordinate : Int) :
    AxisClass.Step (classOfInt coordinate) (classOfInt (coordinate + 1)) := by
  by_cases negative : coordinate < 0
  · by_cases nextNegative : coordinate + 1 < 0
    · rw [classOfInt_of_negative negative,
        classOfInt_of_negative nextNegative]
      rfl
    · have boundary : coordinate = -1 := by omega
      subst coordinate
      rfl
  · by_cases zero : coordinate = 0
    · subst coordinate
      rfl
    · have positive : 0 < coordinate := by omega
      have nextPositive : 0 < coordinate + 1 := by omega
      rw [classOfInt_of_positive positive,
        classOfInt_of_positive nextPositive]
      rfl

/-- Payload of the explicit extension of a quarter-plane tiling. -/
def planePayload {T : TileSet} (quarter : Nat × Nat → TileIn T)
    (point : Int × Int) : WangTile :=
  if 0 ≤ point.1 then
    if 0 ≤ point.2 then
      (quarter (point.1.toNat, point.2.toNat)).1
    else
      verticalWire (quarter (point.1.toNat, 0)).1
  else if 0 ≤ point.2 then
    horizontalWire (quarter (0, point.2.toNat)).1
  else
    zeroTile

/-- Raw extension tile, before attaching its list-membership proof. -/
def planeTile {T : TileSet} (quarter : Nat × Nat → TileIn T)
    (point : Int × Int) : WangTile :=
  WangTile.product (positionTile (classOfInt point.1) (classOfInt point.2))
    (planePayload quarter point)

theorem planePayload_mem_regionPayloads
    {T : TileSet} {seed : WangTile}
    (quarter : Nat × Nat → TileIn T)
    (seeded : (quarter (0, 0)).1 = seed) (point : Int × Int) :
    planePayload quarter point ∈
      regionPayloads T seed (classOfInt point.1) (classOfInt point.2) := by
  by_cases horizontalNonnegative : 0 ≤ point.1
  · by_cases verticalNonnegative : 0 ≤ point.2
    · by_cases horizontalZero : point.1 = 0
      · by_cases verticalZero : point.2 = 0
        · have pointEq : point = (0, 0) := Prod.ext horizontalZero verticalZero
          subst point
          simpa [planePayload, regionPayloads] using
            And.intro (quarter (0, 0)).2 seeded
        · have verticalPositive : 0 < point.2 := lt_of_le_of_ne
            verticalNonnegative (Ne.symm verticalZero)
          simp [planePayload, verticalNonnegative,
            horizontalZero, classOfInt_of_positive verticalPositive,
            regionPayloads, (quarter (0, point.2.toNat)).2]
      · have horizontalPositive : 0 < point.1 := lt_of_le_of_ne
          horizontalNonnegative (Ne.symm horizontalZero)
        by_cases verticalZero : point.2 = 0
        · simp [planePayload, horizontalNonnegative,
            verticalZero, classOfInt_of_positive horizontalPositive,
            regionPayloads, (quarter (point.1.toNat, 0)).2]
        · have verticalPositive : 0 < point.2 := lt_of_le_of_ne
            verticalNonnegative (Ne.symm verticalZero)
          simp [planePayload, horizontalNonnegative, verticalNonnegative,
            classOfInt_of_positive horizontalPositive,
            classOfInt_of_positive verticalPositive, regionPayloads,
            (quarter (point.1.toNat, point.2.toNat)).2]
    · have verticalNegative : point.2 < 0 := lt_of_not_ge verticalNonnegative
      by_cases horizontalZero : point.1 = 0
      · have payloadEq : planePayload quarter point =
            verticalWire (quarter (0, 0)).1 := by
          simp [planePayload, horizontalZero, verticalNonnegative]
        rw [payloadEq, horizontalZero, classOfInt_zero,
          classOfInt_of_negative verticalNegative]
        exact List.mem_map.mpr
          ⟨(quarter (0, 0)).1, (quarter (0, 0)).2, rfl⟩
      · have horizontalPositive : 0 < point.1 := lt_of_le_of_ne
            horizontalNonnegative (Ne.symm horizontalZero)
        simp only [planePayload, horizontalNonnegative, if_pos,
          verticalNonnegative,
          classOfInt_of_positive horizontalPositive,
          classOfInt_of_negative verticalNegative, regionPayloads]
        exact List.mem_map.mpr
          ⟨(quarter (point.1.toNat, 0)).1,
            (quarter (point.1.toNat, 0)).2, rfl⟩
  · have horizontalNegative : point.1 < 0 := lt_of_not_ge horizontalNonnegative
    by_cases verticalNonnegative : 0 ≤ point.2
    · by_cases verticalZero : point.2 = 0
      · have payloadEq : planePayload quarter point =
            horizontalWire (quarter (0, 0)).1 := by
          simp [planePayload, horizontalNonnegative, verticalZero]
        rw [payloadEq, verticalZero,
          classOfInt_of_negative horizontalNegative, classOfInt_zero]
        exact List.mem_map.mpr
          ⟨(quarter (0, 0)).1, (quarter (0, 0)).2, rfl⟩
      · have verticalPositive : 0 < point.2 := lt_of_le_of_ne
            verticalNonnegative (Ne.symm verticalZero)
        simp only [planePayload, horizontalNonnegative,
          verticalNonnegative, if_pos,
          classOfInt_of_negative horizontalNegative,
          classOfInt_of_positive verticalPositive, regionPayloads]
        exact List.mem_map.mpr
          ⟨(quarter (0, point.2.toNat)).1,
            (quarter (0, point.2.toNat)).2, rfl⟩
    · have verticalNegative : point.2 < 0 := lt_of_not_ge verticalNonnegative
      simp [planePayload, horizontalNonnegative, verticalNonnegative,
        classOfInt_of_negative horizontalNegative,
        classOfInt_of_negative verticalNegative, regionPayloads]

theorem planeTile_mem_tiles
    {T : TileSet} {seed : WangTile}
    (quarter : Nat × Nat → TileIn T)
    (seeded : (quarter (0, 0)).1 = seed) (point : Int × Int) :
    planeTile quarter point ∈ tiles T seed := by
  apply mem_tiles_iff.2
  exact ⟨classOfInt point.1, classOfInt point.2, planePayload quarter point,
    planePayload_mem_regionPayloads quarter seeded point, rfl⟩

private theorem toNat_add_one {coordinate : Int} (nonnegative : 0 ≤ coordinate) :
    (coordinate + 1).toNat = coordinate.toNat + 1 := by
  omega

theorem planePayload_hMatches
    {T : TileSet} (quarter : Nat × Nat → TileIn T)
    (valid : ValidQuarterTiling T quarter) (point : Int × Int) :
    WangTile.HMatches (planePayload quarter point)
      (planePayload quarter (point.1 + 1, point.2)) := by
  by_cases verticalNonnegative : 0 ≤ point.2
  · by_cases horizontalNonnegative : 0 ≤ point.1
    · have nextNonnegative : 0 ≤ point.1 + 1 := by omega
      simpa [planePayload, horizontalNonnegative, nextNonnegative,
        verticalNonnegative, toNat_add_one horizontalNonnegative] using
          valid.1 (point.1.toNat, point.2.toNat)
    · by_cases nextNonnegative : 0 ≤ point.1 + 1
      · have boundary : point.1 + 1 = 0 := by omega
        simp [planePayload, horizontalNonnegative,
          verticalNonnegative, boundary, horizontalWire, WangTile.HMatches]
      · simp [planePayload, horizontalNonnegative, nextNonnegative,
          verticalNonnegative, horizontalWire, WangTile.HMatches]
  · by_cases horizontalNonnegative : 0 ≤ point.1
    · have nextNonnegative : 0 ≤ point.1 + 1 := by omega
      simp [planePayload, horizontalNonnegative, nextNonnegative,
        verticalNonnegative, verticalWire, WangTile.HMatches]
    · by_cases nextNonnegative : 0 ≤ point.1 + 1 <;>
        simp [planePayload, horizontalNonnegative, nextNonnegative,
          verticalNonnegative, zeroTile, verticalWire, WangTile.HMatches]

theorem planePayload_vMatches
    {T : TileSet} (quarter : Nat × Nat → TileIn T)
    (valid : ValidQuarterTiling T quarter) (point : Int × Int) :
    WangTile.VMatches (planePayload quarter point)
      (planePayload quarter (point.1, point.2 + 1)) := by
  by_cases horizontalNonnegative : 0 ≤ point.1
  · by_cases verticalNonnegative : 0 ≤ point.2
    · have nextNonnegative : 0 ≤ point.2 + 1 := by omega
      simpa [planePayload, horizontalNonnegative, verticalNonnegative,
        nextNonnegative, toNat_add_one verticalNonnegative] using
          valid.2 (point.1.toNat, point.2.toNat)
    · by_cases nextNonnegative : 0 ≤ point.2 + 1
      · have boundary : point.2 + 1 = 0 := by omega
        simp [planePayload, horizontalNonnegative, verticalNonnegative,
          boundary, verticalWire, WangTile.VMatches]
      · simp [planePayload, horizontalNonnegative, verticalNonnegative,
          nextNonnegative, verticalWire, WangTile.VMatches]
  · by_cases verticalNonnegative : 0 ≤ point.2
    · have nextNonnegative : 0 ≤ point.2 + 1 := by omega
      simp [planePayload, horizontalNonnegative, verticalNonnegative,
        nextNonnegative, horizontalWire, WangTile.VMatches]
    · by_cases nextNonnegative : 0 ≤ point.2 + 1 <;>
        simp [planePayload, horizontalNonnegative, verticalNonnegative,
          nextNonnegative, zeroTile, horizontalWire, WangTile.VMatches]

/-- A seeded source quarter-plane extends to a valid pointed full plane. -/
theorem exists_pointed_plane_of_tilesQuarterWithSeed
    {T : TileSet} {seed : WangTile} :
    TilesQuarterWithSeed T seed →
      ∃ plane : Int × Int → TileIn (tiles T seed),
        ValidPlaneTiling (tiles T seed) plane ∧
          (plane (0, 0)).1 = pointedSeed seed := by
  rintro ⟨quarter, valid, seeded⟩
  let plane : Int × Int → TileIn (tiles T seed) := fun point =>
    ⟨planeTile quarter point, planeTile_mem_tiles quarter seeded point⟩
  refine ⟨plane, ?_, ?_⟩
  · constructor
    · intro point
      change WangTile.HMatches (planeTile quarter point)
        (planeTile quarter (point.1 + 1, point.2))
      simp only [planeTile]
      rw [WangTile.HMatches_product_iff]
      exact ⟨positionTile_hMatches_iff.2
          ⟨classOfInt_step point.1, rfl⟩,
        planePayload_hMatches quarter valid point⟩
    · intro point
      change WangTile.VMatches (planeTile quarter point)
        (planeTile quarter (point.1, point.2 + 1))
      simp only [planeTile]
      rw [WangTile.VMatches_product_iff]
      exact ⟨positionTile_vMatches_iff.2
          ⟨classOfInt_step point.2, rfl⟩,
        planePayload_vMatches quarter valid point⟩
  · change WangTile.product (positionTile .origin .origin)
      (quarter (0, 0)).1 = pointedSeed seed
    rw [seeded]
    rfl

theorem tilesPlane_of_tilesQuarterWithSeed
    {T : TileSet} {seed : WangTile} :
    TilesQuarterWithSeed T seed → TilesPlane (tiles T seed) := by
  intro quarter
  rcases exists_pointed_plane_of_tilesQuarterWithSeed quarter with
    ⟨plane, valid, _pointed⟩
  exact ⟨plane, valid⟩

/-- Restrict the explicit pointed plane back to its northeast quadrant. -/
theorem extension_tilesQuarterWithSeed_of_tilesQuarterWithSeed
    {T : TileSet} {seed : WangTile} :
    TilesQuarterWithSeed T seed →
      TilesQuarterWithSeed (tiles T seed) (pointedSeed seed) := by
  intro source
  rcases exists_pointed_plane_of_tilesQuarterWithSeed source with
    ⟨plane, valid, pointed⟩
  let quarter : Nat × Nat → TileIn (tiles T seed) := fun point =>
    plane (point.1, point.2)
  refine ⟨quarter, ?_, ?_⟩
  · constructor
    · intro point
      simpa [quarter] using valid.1 ((point.1 : Int), (point.2 : Int))
    · intro point
      simpa [quarter] using valid.2 ((point.1 : Int), (point.2 : Int))
  · simpa [quarter] using pointed

/-- A seeded source quarter-plane supplies pointed extension squares of every
positive size. -/
theorem extension_fixedCornerSquares_of_tilesQuarterWithSeed
    {T : TileSet} {seed : WangTile}
    (source : TilesQuarterWithSeed T seed) :
    ∀ n : Nat, 0 < n →
      TileableFixedCornerSquare (tiles T seed) (pointedSeed seed) n :=
  fixedCornerSquare_of_tilesQuarterWithSeed
    (extension_tilesQuarterWithSeed_of_tilesQuarterWithSeed source)

end PointedExtension
end LeanWang
