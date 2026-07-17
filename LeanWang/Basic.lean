/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.Halting
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Pairing

/-!
This file contains the concrete Wang-tile objects used by the project.

The representation is deliberately computability-friendly: colors are natural
numbers and a finite tileset is a list of tiles.
-/

namespace LeanWang

/-- A Wang tile, represented by the colors on its north, south, east, and west edges. -/
structure WangTile where
  n : Nat
  s : Nat
  e : Nat
  w : Nat
deriving DecidableEq, Repr

/-- A finite Wang tileset. Duplicates are harmless and ignored by membership predicates. -/
abbrev TileSet := List WangTile

/-- View a Wang tile as the quadruple of its edge colors. -/
def WangTile.toTuple (t : WangTile) : Nat × Nat × Nat × Nat :=
  (t.n, t.s, t.e, t.w)

/-- Build a Wang tile from the quadruple of its edge colors. -/
def WangTile.ofTuple (p : Nat × Nat × Nat × Nat) : WangTile where
  n := p.1
  s := p.2.1
  e := p.2.2.1
  w := p.2.2.2

/-- Wang tiles are encoded by their four natural-number edge colors. -/
def WangTile.equivTuple : WangTile ≃ Nat × Nat × Nat × Nat where
  toFun := WangTile.toTuple
  invFun := WangTile.ofTuple
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro p
    rcases p with ⟨n, s, e, w⟩
    rfl

instance instPrimcodableWangTile : Primcodable WangTile :=
  Primcodable.ofEquiv (Nat × Nat × Nat × Nat) WangTile.equivTuple

/-- Encode a finite Wang tileset as a natural number. -/
def encodeTileSet (T : TileSet) : Nat :=
  Encodable.encode T

/--
Decode a natural number as a finite Wang tileset. Invalid codes decode to the
empty tileset; every actual tileset has a canonical code via `encodeTileSet`.
-/
def decodeTileSet (n : Nat) : TileSet :=
  (Encodable.decode (α := TileSet) n).getD []

@[simp]
theorem decodeTileSet_encodeTileSet (T : TileSet) :
    decodeTileSet (encodeTileSet T) = T := by
  simp [decodeTileSet, encodeTileSet]

theorem decodeTileSet_surjective : Function.Surjective decodeTileSet := by
  intro T
  exact ⟨encodeTileSet T, decodeTileSet_encodeTileSet T⟩

theorem encodeTileSet_computable : Computable encodeTileSet := by
  change Computable fun T : TileSet => Encodable.encode T
  exact Computable.encode

theorem decodeTileSet_computable : Computable decodeTileSet := by
  change Computable fun n : Nat => (Encodable.decode (α := TileSet) n).getD []
  exact Computable.option_getD Computable.decode (Computable.const ([] : TileSet))

/-- The type of tiles belonging to a fixed tileset. -/
abbrev TileIn (T : TileSet) :=
  { t : WangTile // t ∈ T }

namespace WangTile

/-- Horizontal compatibility: `left` may be placed immediately west of `right`. -/
def HMatches (left right : WangTile) : Prop :=
  left.e = right.w

/-- Vertical compatibility: `lower` may be placed immediately south of `upper`. -/
def VMatches (lower upper : WangTile) : Prop :=
  lower.n = upper.s

instance (left right : WangTile) : Decidable (HMatches left right) := by
  unfold HMatches
  infer_instance

instance (lower upper : WangTile) : Decidable (VMatches lower upper) := by
  unfold VMatches
  infer_instance

/-- Layer two Wang tiles by pairing the corresponding edge colors. -/
def product (base payload : WangTile) : WangTile where
  n := Nat.pair base.n payload.n
  s := Nat.pair base.s payload.s
  e := Nat.pair base.e payload.e
  w := Nat.pair base.w payload.w

/-- Recover the base layer of a product-encoded Wang tile. -/
def productBase (tile : WangTile) : WangTile where
  n := tile.n.unpair.1
  s := tile.s.unpair.1
  e := tile.e.unpair.1
  w := tile.w.unpair.1

@[simp] theorem productBase_product (base payload : WangTile) :
    productBase (product base payload) = base := by
  cases base
  cases payload
  simp [productBase, product]

theorem toTuple_primrec : Primrec WangTile.toTuple := by
  simpa [WangTile.equivTuple] using
    (Primrec.of_equiv (e := WangTile.equivTuple) : Primrec WangTile.equivTuple)

theorem ofTuple_primrec : Primrec WangTile.ofTuple := by
  simpa [WangTile.equivTuple] using
    (Primrec.of_equiv_symm (e := WangTile.equivTuple) : Primrec WangTile.equivTuple.symm)

theorem n_primrec : Primrec WangTile.n :=
  Primrec.fst.comp toTuple_primrec

theorem s_primrec : Primrec WangTile.s :=
  Primrec.fst.comp (Primrec.snd.comp toTuple_primrec)

theorem e_primrec : Primrec WangTile.e :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))

theorem w_primrec : Primrec WangTile.w :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))

theorem productBase_primrec : Primrec productBase := by
  exact ofTuple_primrec.comp
    (Primrec.pair
      (Primrec.fst.comp (Primrec.unpair.comp n_primrec))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.unpair.comp s_primrec))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.unpair.comp e_primrec))
          (Primrec.fst.comp (Primrec.unpair.comp w_primrec)))))

theorem product_primrec : Primrec (fun p : WangTile × WangTile => product p.1 p.2) := by
  let f : WangTile × WangTile → Nat × Nat × Nat × Nat := fun p =>
    (Nat.pair p.1.n p.2.n, Nat.pair p.1.s p.2.s,
      Nat.pair p.1.e p.2.e, Nat.pair p.1.w p.2.w)
  have hf : Primrec f := by
    dsimp [f]
    exact (Primrec.pair
      (Primrec₂.natPair.comp (n_primrec.comp Primrec.fst) (n_primrec.comp Primrec.snd))
      (Primrec.pair
        (Primrec₂.natPair.comp (s_primrec.comp Primrec.fst) (s_primrec.comp Primrec.snd))
        (Primrec.pair
          (Primrec₂.natPair.comp (e_primrec.comp Primrec.fst) (e_primrec.comp Primrec.snd))
          (Primrec₂.natPair.comp (w_primrec.comp Primrec.fst) (w_primrec.comp Primrec.snd)))))
  have hprod : Primrec fun p => WangTile.equivTuple.symm (f p) :=
    (Primrec.of_equiv_symm_iff (e := WangTile.equivTuple) (f := f)).2 hf
  exact hprod.of_eq fun p => by
    cases p with
    | mk base payload =>
      cases base
      cases payload
      rfl

theorem product_primrec₂ : Primrec₂ product :=
  Primrec₂.mk product_primrec

theorem product_computable : Computable (fun p : WangTile × WangTile => product p.1 p.2) :=
  product_primrec.to_comp

theorem product_computable₂ : Computable₂ product :=
  Computable₂.mk product_computable

theorem product_injective :
    Function.Injective (fun p : WangTile × WangTile => product p.1 p.2) := by
  intro p q h
  rcases p with ⟨base, payload⟩
  rcases q with ⟨base', payload'⟩
  cases base
  cases payload
  cases base'
  cases payload'
  simp [product] at h ⊢
  simp [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem HMatches_product_iff (baseLeft payloadLeft baseRight payloadRight : WangTile) :
    HMatches (product baseLeft payloadLeft) (product baseRight payloadRight) ↔
      HMatches baseLeft baseRight ∧ HMatches payloadLeft payloadRight := by
  unfold HMatches product
  rw [Nat.pair_eq_pair]

theorem VMatches_product_iff (baseLower payloadLower baseUpper payloadUpper : WangTile) :
    VMatches (product baseLower payloadLower) (product baseUpper payloadUpper) ↔
      VMatches baseLower baseUpper ∧ VMatches payloadLower payloadUpper := by
  unfold VMatches product
  rw [Nat.pair_eq_pair]

end WangTile

/-- The finite tileset obtained by layering every base tile with every payload tile. -/
def productTileSet (base payload : TileSet) : TileSet :=
  base.flatMap fun b => payload.map fun p => WangTile.product b p

theorem productTileSet_primrec :
    Primrec (fun p : TileSet × TileSet => productTileSet p.1 p.2) := by
  unfold productTileSet
  refine Primrec.list_flatMap Primrec.fst ?_
  apply Primrec₂.mk
  refine Primrec.list_map (Primrec.snd.comp Primrec.fst) ?_
  rw [← Primrec₂.uncurry]
  exact WangTile.product_primrec.comp
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem productTileSet_primrec₂ : Primrec₂ productTileSet :=
  Primrec₂.mk productTileSet_primrec

theorem productTileSet_computable :
    Computable (fun p : TileSet × TileSet => productTileSet p.1 p.2) :=
  productTileSet_primrec.to_comp

theorem productTileSet_computable₂ : Computable₂ productTileSet :=
  Computable₂.mk productTileSet_computable

theorem mem_productTileSet_iff {base payload : TileSet} {tile : WangTile} :
    tile ∈ productTileSet base payload ↔
      ∃ b ∈ base, ∃ p ∈ payload, WangTile.product b p = tile := by
  simp [productTileSet]

theorem product_mem_productTileSet {base payload : TileSet}
    {b p : WangTile} (hb : b ∈ base) (hp : p ∈ payload) :
    WangTile.product b p ∈ productTileSet base payload := by
  rw [mem_productTileSet_iff]
  exact ⟨b, hb, p, hp, rfl⟩

theorem product_eq_iff {base payload base' payload' : WangTile} :
    WangTile.product base payload = WangTile.product base' payload' ↔
      base = base' ∧ payload = payload' := by
  constructor
  · intro h
    have hp : (base, payload) = (base', payload') :=
      WangTile.product_injective h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem productTileSet_nonempty_left {base payload : TileSet}
    {tile : WangTile} (htile : tile ∈ productTileSet base payload) :
    ∃ b : WangTile, b ∈ base := by
  rcases mem_productTileSet_iff.1 htile with ⟨b, hb, _p, _hp, _htile⟩
  exact ⟨b, hb⟩

/-- A complete tiling of the integer plane by a finite tileset. -/
def ValidPlaneTiling (T : TileSet) (x : Int × Int → TileIn T) : Prop :=
  (∀ p : Int × Int, WangTile.HMatches (x p).1 (x (p.1 + 1, p.2)).1) ∧
    (∀ p : Int × Int, WangTile.VMatches (x p).1 (x (p.1, p.2 + 1)).1)

/-- A tileset tiles the whole plane. -/
def TilesPlane (T : TileSet) : Prop :=
  ∃ x : Int × Int → TileIn T, ValidPlaneTiling T x

theorem validPlaneTiling_congr {T U : TileSet}
    (hmem : ∀ tile : WangTile, tile ∈ T ↔ tile ∈ U)
    {x : Int × Int → TileIn T} :
    ValidPlaneTiling T x →
      ValidPlaneTiling U (fun p => (⟨(x p).1, (hmem (x p).1).1 (x p).2⟩ : TileIn U)) := by
  intro hvalid
  exact hvalid

theorem tilesPlane_congr {T U : TileSet}
    (hmem : ∀ tile : WangTile, tile ∈ T ↔ tile ∈ U) :
    TilesPlane T ↔ TilesPlane U := by
  constructor
  · rintro ⟨x, hvalid⟩
    exact ⟨fun p => ⟨(x p).1, (hmem (x p).1).1 (x p).2⟩,
      validPlaneTiling_congr hmem hvalid⟩
  · rintro ⟨x, hvalid⟩
    exact ⟨fun p => ⟨(x p).1, (hmem (x p).1).2 (x p).2⟩,
      validPlaneTiling_congr (fun tile => (hmem tile).symm) hvalid⟩

theorem tilesPlane_left_of_tilesPlane_productTileSet {base payload : TileSet}
    (h : TilesPlane (productTileSet base payload)) :
    TilesPlane base := by
  classical
  rcases h with ⟨x, hx⟩
  have hdecode : ∀ p : Int × Int,
      ∃ b : TileIn base, ∃ q : TileIn payload,
        WangTile.product b.1 q.1 = (x p).1 := by
    intro p
    rcases mem_productTileSet_iff.1 (x p).2 with ⟨b, hb, q, hq, htile⟩
    exact ⟨⟨b, hb⟩, ⟨q, hq⟩, htile⟩
  let baseAt : Int × Int → TileIn base := fun p => Classical.choose (hdecode p)
  let payloadAt : Int × Int → TileIn payload := fun p =>
    Classical.choose (Classical.choose_spec (hdecode p))
  have hproduct : ∀ p : Int × Int,
      WangTile.product (baseAt p).1 (payloadAt p).1 = (x p).1 := by
    intro p
    exact Classical.choose_spec (Classical.choose_spec (hdecode p))
  refine ⟨baseAt, ?_⟩
  constructor
  · intro p
    have hmatch : WangTile.HMatches
        (WangTile.product (baseAt p).1 (payloadAt p).1)
        (WangTile.product (baseAt (p.1 + 1, p.2)).1
          (payloadAt (p.1 + 1, p.2)).1) := by
      simpa [hproduct p, hproduct (p.1 + 1, p.2)] using hx.1 p
    exact (WangTile.HMatches_product_iff
      (baseAt p).1 (payloadAt p).1
      (baseAt (p.1 + 1, p.2)).1 (payloadAt (p.1 + 1, p.2)).1).1 hmatch |>.1
  · intro p
    have hmatch : WangTile.VMatches
        (WangTile.product (baseAt p).1 (payloadAt p).1)
        (WangTile.product (baseAt (p.1, p.2 + 1)).1
          (payloadAt (p.1, p.2 + 1)).1) := by
      simpa [hproduct p, hproduct (p.1, p.2 + 1)] using hx.2 p
    exact (WangTile.VMatches_product_iff
      (baseAt p).1 (payloadAt p).1
      (baseAt (p.1, p.2 + 1)).1 (payloadAt (p.1, p.2 + 1)).1).1 hmatch |>.1

theorem tilesPlane_right_of_tilesPlane_productTileSet {base payload : TileSet}
    (h : TilesPlane (productTileSet base payload)) :
    TilesPlane payload := by
  classical
  rcases h with ⟨x, hx⟩
  have hdecode : ∀ p : Int × Int,
      ∃ b : TileIn base, ∃ q : TileIn payload,
        WangTile.product b.1 q.1 = (x p).1 := by
    intro p
    rcases mem_productTileSet_iff.1 (x p).2 with ⟨b, hb, q, hq, htile⟩
    exact ⟨⟨b, hb⟩, ⟨q, hq⟩, htile⟩
  let baseAt : Int × Int → TileIn base := fun p => Classical.choose (hdecode p)
  let payloadAt : Int × Int → TileIn payload := fun p =>
    Classical.choose (Classical.choose_spec (hdecode p))
  have hproduct : ∀ p : Int × Int,
      WangTile.product (baseAt p).1 (payloadAt p).1 = (x p).1 := by
    intro p
    exact Classical.choose_spec (Classical.choose_spec (hdecode p))
  refine ⟨payloadAt, ?_⟩
  constructor
  · intro p
    have hmatch : WangTile.HMatches
        (WangTile.product (baseAt p).1 (payloadAt p).1)
        (WangTile.product (baseAt (p.1 + 1, p.2)).1
          (payloadAt (p.1 + 1, p.2)).1) := by
      simpa [hproduct p, hproduct (p.1 + 1, p.2)] using hx.1 p
    exact (WangTile.HMatches_product_iff
      (baseAt p).1 (payloadAt p).1
      (baseAt (p.1 + 1, p.2)).1 (payloadAt (p.1 + 1, p.2)).1).1 hmatch |>.2
  · intro p
    have hmatch : WangTile.VMatches
        (WangTile.product (baseAt p).1 (payloadAt p).1)
        (WangTile.product (baseAt (p.1, p.2 + 1)).1
          (payloadAt (p.1, p.2 + 1)).1) := by
      simpa [hproduct p, hproduct (p.1, p.2 + 1)] using hx.2 p
    exact (WangTile.VMatches_product_iff
      (baseAt p).1 (payloadAt p).1
      (baseAt (p.1, p.2 + 1)).1 (payloadAt (p.1, p.2 + 1)).1).1 hmatch |>.2

theorem tilesPlane_productTileSet_of_tilesPlane {base payload : TileSet}
    (hbase : TilesPlane base) (hpayload : TilesPlane payload) :
    TilesPlane (productTileSet base payload) := by
  rcases hbase with ⟨baseAt, hbaseValid⟩
  rcases hpayload with ⟨payloadAt, hpayloadValid⟩
  let x : Int × Int → TileIn (productTileSet base payload) := fun p =>
    ⟨WangTile.product (baseAt p).1 (payloadAt p).1,
      product_mem_productTileSet (baseAt p).2 (payloadAt p).2⟩
  refine ⟨x, ?_⟩
  constructor
  · intro p
    rw [show (x p).1 = WangTile.product (baseAt p).1 (payloadAt p).1 by rfl,
      show (x (p.1 + 1, p.2)).1 =
        WangTile.product (baseAt (p.1 + 1, p.2)).1
          (payloadAt (p.1 + 1, p.2)).1 by rfl,
      WangTile.HMatches_product_iff]
    exact ⟨hbaseValid.1 p, hpayloadValid.1 p⟩
  · intro p
    rw [show (x p).1 = WangTile.product (baseAt p).1 (payloadAt p).1 by rfl,
      show (x (p.1, p.2 + 1)).1 =
        WangTile.product (baseAt (p.1, p.2 + 1)).1
          (payloadAt (p.1, p.2 + 1)).1 by rfl,
      WangTile.VMatches_product_iff]
    exact ⟨hbaseValid.2 p, hpayloadValid.2 p⟩

theorem tilesPlane_productTileSet_iff (base payload : TileSet) :
    TilesPlane (productTileSet base payload) ↔ TilesPlane base ∧ TilesPlane payload := by
  constructor
  · intro h
    exact ⟨tilesPlane_left_of_tilesPlane_productTileSet h,
      tilesPlane_right_of_tilesPlane_productTileSet h⟩
  · rintro ⟨hbase, hpayload⟩
    exact tilesPlane_productTileSet_of_tilesPlane hbase hpayload

/-- The centered integer box `[-r, r] × [-r, r]`. -/
def InBox (r : Nat) (p : Int × Int) : Prop :=
  -(r : Int) ≤ p.1 ∧ p.1 ≤ (r : Int) ∧
    -(r : Int) ≤ p.2 ∧ p.2 ≤ (r : Int)

/-- Coordinates in the centered integer box `[-r, r] × [-r, r]`. -/
abbrev Box (r : Nat) :=
  { p : Int × Int // InBox r p }

/-- A finite centered box assignment. -/
abbrev BoxPattern (T : TileSet) (r : Nat) :=
  Box r → TileIn T

/-- Validity of a centered finite box tiling. -/
def ValidBoxTiling (T : TileSet) (r : Nat) (x : BoxPattern T r) : Prop :=
  (∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
    WangTile.HMatches (x p).1 (x ⟨(p.1.1 + 1, p.1.2), hp⟩).1) ∧
    (∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
      WangTile.VMatches (x p).1 (x ⟨(p.1.1, p.1.2 + 1), hp⟩).1)

/-- A tileset tiles the centered integer box `[-r, r] × [-r, r]`. -/
def TileableBox (T : TileSet) (r : Nat) : Prop :=
  ∃ x : BoxPattern T r, ValidBoxTiling T r x

/-- A complete tiling of the first quadrant `Nat × Nat`. -/
def ValidQuarterTiling (T : TileSet) (x : Nat × Nat → TileIn T) : Prop :=
  (∀ p : Nat × Nat, WangTile.HMatches (x p).1 (x (p.1 + 1, p.2)).1) ∧
    (∀ p : Nat × Nat, WangTile.VMatches (x p).1 (x (p.1, p.2 + 1)).1)

/-- A tileset tiles the first quadrant with a prescribed tile at the origin. -/
def TilesQuarterWithSeed (T : TileSet) (seed : WangTile) : Prop :=
  ∃ x : Nat × Nat → TileIn T, ValidQuarterTiling T x ∧ (x (0, 0)).1 = seed

theorem validQuarterTiling_congr {T U : TileSet}
    (hmem : ∀ tile : WangTile, tile ∈ T ↔ tile ∈ U)
    {x : Nat × Nat → TileIn T} :
    ValidQuarterTiling T x →
      ValidQuarterTiling U (fun p => (⟨(x p).1, (hmem (x p).1).1 (x p).2⟩ : TileIn U)) := by
  intro hvalid
  exact hvalid

theorem tilesQuarterWithSeed_congr {T U : TileSet} {seed : WangTile}
    (hmem : ∀ tile : WangTile, tile ∈ T ↔ tile ∈ U) :
    TilesQuarterWithSeed T seed ↔ TilesQuarterWithSeed U seed := by
  constructor
  · rintro ⟨x, hvalid, hseed⟩
    exact ⟨fun p => ⟨(x p).1, (hmem (x p).1).1 (x p).2⟩,
      validQuarterTiling_congr hmem hvalid, hseed⟩
  · rintro ⟨x, hvalid, hseed⟩
    exact ⟨fun p => ⟨(x p).1, (hmem (x p).1).2 (x p).2⟩,
      validQuarterTiling_congr (fun tile => (hmem tile).symm) hvalid, hseed⟩

/-- A finite rectangle assignment with width `w` and height `h`. -/
abbrev Rectangle (w h : Nat) :=
  Fin w → Fin h → WangTile

/-- Row-major indexing of a finite rectangle stored as a flat list. -/
def rectIndex (w : Nat) (i j : Nat) : Nat :=
  j * w + i

/-- Read cell `(i, j)` from a row-major rectangle pattern. -/
def getRectCell? (xs : List WangTile) (w i j : Nat) : Option WangTile :=
  xs[rectIndex w i j]?

/-- The one-color tile used as an irrelevant default outside a flat rectangle. -/
def monochromeTile : WangTile where
  n := 0
  s := 0
  e := 0
  w := 0

/-- Read cell `(i, j)` from a row-major rectangle, using an irrelevant default out of range. -/
def flatTile (xs : List WangTile) (w i j : Nat) : WangTile :=
  xs.getD (rectIndex w i j) monochromeTile

/-- Semantic specification of a valid row-major `w × h` rectangle list. -/
def FlatValidRectangle (T : TileSet) (w h : Nat) (xs : List WangTile) : Prop :=
  xs.length = w * h ∧
    ∀ i : Nat, i < w → ∀ j : Nat, j < h →
      flatTile xs w i j ∈ T ∧
        (∀ _hi : i + 1 < w,
          WangTile.HMatches (flatTile xs w i j) (flatTile xs w (i + 1) j)) ∧
        (∀ _hj : j + 1 < h,
          WangTile.VMatches (flatTile xs w i j) (flatTile xs w i (j + 1)))

instance (T : TileSet) (w h : Nat) (xs : List WangTile) :
    Decidable (FlatValidRectangle T w h xs) := by
  unfold FlatValidRectangle
  infer_instance

/-- All words of length `n` over a finite alphabet. -/
def words (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => List.flatMap (fun tail =>
      alphabet.map fun head => head :: tail
    ) (words alphabet n)

/--
Executable checker for the semantic row-major rectangle specification.
-/
def validRectListBool (T : TileSet) (w h : Nat) (xs : List WangTile) : Bool :=
  decide (FlatValidRectangle T w h xs)

/-- Exhaustive finite search for a valid `w × h` rectangle over `T`. -/
def tileableRectangleBool (T : TileSet) (w h : Nat) : Bool :=
  (words T (w * h)).any fun xs => validRectListBool T w h xs

/-- Exhaustive finite search for a valid `n × n` square over `T`. -/
def tileableSquareBool (T : TileSet) (n : Nat) : Bool :=
  tileableRectangleBool T n n

example : tileableSquareBool [monochromeTile] 2 = true := by
  decide

/-- Validity of a finite rectangular Wang tiling. -/
def ValidRectangle (T : TileSet) {w h : Nat} (x : Rectangle w h) : Prop :=
  (∀ i : Fin w, ∀ j : Fin h, x i j ∈ T) ∧
    (∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
      WangTile.HMatches (x i j) (x ⟨i.val + 1, hi⟩ j)) ∧
      (∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
        WangTile.VMatches (x i j) (x i ⟨j.val + 1, hj⟩))

instance decidableValidRectangle (T : TileSet) {w h : Nat} (x : Rectangle w h) :
    Decidable (ValidRectangle T x) := by
  unfold ValidRectangle
  infer_instance

/-- Boolean checker for finite rectangular Wang tilings. -/
def validRectangleBool (T : TileSet) {w h : Nat} (x : Rectangle w h) : Bool :=
  decide (ValidRectangle T x)

@[simp]
theorem validRectangleBool_eq_true (T : TileSet) {w h : Nat} (x : Rectangle w h) :
    validRectangleBool T x = true ↔ ValidRectangle T x := by
  simp [validRectangleBool]

/-- Restrict a finite rectangle to its southwest `w × h` subrectangle. -/
def Rectangle.crop {W H : Nat} (x : Rectangle W H)
    {w h : Nat} (hw : w ≤ W) (hh : h ≤ H) :
    Rectangle w h :=
  fun i j => x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hw⟩
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt hh⟩

theorem validRectangle_crop {T : TileSet}
    {W H w h : Nat} {x : Rectangle W H}
    (hx : ValidRectangle T x) (hw : w ≤ W) (hh : h ≤ H) :
    ValidRectangle T (Rectangle.crop x hw hh) := by
  constructor
  · intro i j
    exact hx.1 ⟨i.val, Nat.lt_of_lt_of_le i.isLt hw⟩
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt hh⟩
  constructor
  · intro i j hi
    exact hx.2.1 ⟨i.val, Nat.lt_of_lt_of_le i.isLt hw⟩
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt hh⟩
      (Nat.lt_of_lt_of_le hi hw)
  · intro i j hj
    exact hx.2.2 ⟨i.val, Nat.lt_of_lt_of_le i.isLt hw⟩
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt hh⟩
      (Nat.lt_of_lt_of_le hj hh)

theorem validRectangle_product_of_validRectangle {base payload : TileSet}
    {w h : Nat} {baseRect payloadRect : Rectangle w h}
    (hbase : ValidRectangle base baseRect)
    (hpayload : ValidRectangle payload payloadRect) :
    ValidRectangle (productTileSet base payload)
      (fun i j => WangTile.product (baseRect i j) (payloadRect i j)) := by
  constructor
  · intro i j
    exact product_mem_productTileSet (hbase.1 i j) (hpayload.1 i j)
  constructor
  · intro i j hi
    rw [WangTile.HMatches_product_iff]
    exact ⟨hbase.2.1 i j hi, hpayload.2.1 i j hi⟩
  · intro i j hj
    rw [WangTile.VMatches_product_iff]
    exact ⟨hbase.2.2 i j hj, hpayload.2.2 i j hj⟩

theorem validRectangle_left_of_validRectangle_productTileSet {base payload : TileSet}
    {w h : Nat} {rect : Rectangle w h}
    (hrect : ValidRectangle (productTileSet base payload) rect) :
    ∃ baseRect : Rectangle w h, ValidRectangle base baseRect := by
  classical
  have hdecode : ∀ i : Fin w, ∀ j : Fin h,
      ∃ b : TileIn base, ∃ q : TileIn payload,
        WangTile.product b.1 q.1 = rect i j := by
    intro i j
    rcases mem_productTileSet_iff.1 (hrect.1 i j) with ⟨b, hb, q, hq, htile⟩
    exact ⟨⟨b, hb⟩, ⟨q, hq⟩, htile⟩
  let baseAt : Fin w → Fin h → TileIn base := fun i j => Classical.choose (hdecode i j)
  let payloadAt : Fin w → Fin h → TileIn payload := fun i j =>
    Classical.choose (Classical.choose_spec (hdecode i j))
  have hproduct : ∀ i : Fin w, ∀ j : Fin h,
      WangTile.product (baseAt i j).1 (payloadAt i j).1 = rect i j := by
    intro i j
    exact Classical.choose_spec (Classical.choose_spec (hdecode i j))
  refine ⟨fun i j => (baseAt i j).1, ?_⟩
  constructor
  · intro i j
    exact (baseAt i j).2
  constructor
  · intro i j hi
    have hmatch : WangTile.HMatches
        (WangTile.product (baseAt i j).1 (payloadAt i j).1)
        (WangTile.product (baseAt ⟨i.val + 1, hi⟩ j).1
          (payloadAt ⟨i.val + 1, hi⟩ j).1) := by
      simpa [hproduct i j, hproduct ⟨i.val + 1, hi⟩ j] using hrect.2.1 i j hi
    exact (WangTile.HMatches_product_iff
      (baseAt i j).1 (payloadAt i j).1
      (baseAt ⟨i.val + 1, hi⟩ j).1 (payloadAt ⟨i.val + 1, hi⟩ j).1).1 hmatch |>.1
  · intro i j hj
    have hmatch : WangTile.VMatches
        (WangTile.product (baseAt i j).1 (payloadAt i j).1)
        (WangTile.product (baseAt i ⟨j.val + 1, hj⟩).1
          (payloadAt i ⟨j.val + 1, hj⟩).1) := by
      simpa [hproduct i j, hproduct i ⟨j.val + 1, hj⟩] using hrect.2.2 i j hj
    exact (WangTile.VMatches_product_iff
      (baseAt i j).1 (payloadAt i j).1
      (baseAt i ⟨j.val + 1, hj⟩).1 (payloadAt i ⟨j.val + 1, hj⟩).1).1 hmatch |>.1

theorem validRectangle_right_of_validRectangle_productTileSet {base payload : TileSet}
    {w h : Nat} {rect : Rectangle w h}
    (hrect : ValidRectangle (productTileSet base payload) rect) :
    ∃ payloadRect : Rectangle w h, ValidRectangle payload payloadRect := by
  classical
  have hdecode : ∀ i : Fin w, ∀ j : Fin h,
      ∃ b : TileIn base, ∃ q : TileIn payload,
        WangTile.product b.1 q.1 = rect i j := by
    intro i j
    rcases mem_productTileSet_iff.1 (hrect.1 i j) with ⟨b, hb, q, hq, htile⟩
    exact ⟨⟨b, hb⟩, ⟨q, hq⟩, htile⟩
  let baseAt : Fin w → Fin h → TileIn base := fun i j => Classical.choose (hdecode i j)
  let payloadAt : Fin w → Fin h → TileIn payload := fun i j =>
    Classical.choose (Classical.choose_spec (hdecode i j))
  have hproduct : ∀ i : Fin w, ∀ j : Fin h,
      WangTile.product (baseAt i j).1 (payloadAt i j).1 = rect i j := by
    intro i j
    exact Classical.choose_spec (Classical.choose_spec (hdecode i j))
  refine ⟨fun i j => (payloadAt i j).1, ?_⟩
  constructor
  · intro i j
    exact (payloadAt i j).2
  constructor
  · intro i j hi
    have hmatch : WangTile.HMatches
        (WangTile.product (baseAt i j).1 (payloadAt i j).1)
        (WangTile.product (baseAt ⟨i.val + 1, hi⟩ j).1
          (payloadAt ⟨i.val + 1, hi⟩ j).1) := by
      simpa [hproduct i j, hproduct ⟨i.val + 1, hi⟩ j] using hrect.2.1 i j hi
    exact (WangTile.HMatches_product_iff
      (baseAt i j).1 (payloadAt i j).1
      (baseAt ⟨i.val + 1, hi⟩ j).1 (payloadAt ⟨i.val + 1, hi⟩ j).1).1 hmatch |>.2
  · intro i j hj
    have hmatch : WangTile.VMatches
        (WangTile.product (baseAt i j).1 (payloadAt i j).1)
        (WangTile.product (baseAt i ⟨j.val + 1, hj⟩).1
          (payloadAt i ⟨j.val + 1, hj⟩).1) := by
      simpa [hproduct i j, hproduct i ⟨j.val + 1, hj⟩] using hrect.2.2 i j hj
    exact (WangTile.VMatches_product_iff
      (baseAt i j).1 (payloadAt i j).1
      (baseAt i ⟨j.val + 1, hj⟩).1 (payloadAt i ⟨j.val + 1, hj⟩).1).1 hmatch |>.2

/-- A tileset tiles a finite `w × h` rectangle. -/
def TileableRectangle (T : TileSet) (w h : Nat) : Prop :=
  ∃ x : Rectangle w h, ValidRectangle T x

/-- A tileset tiles a finite `n × n` square. -/
def TileableSquare (T : TileSet) (n : Nat) : Prop :=
  TileableRectangle T n n

theorem tileableRectangle_crop {T : TileSet}
    {W H w h : Nat} (hw : w ≤ W) (hh : h ≤ H) :
    TileableRectangle T W H → TileableRectangle T w h := by
  rintro ⟨x, hx⟩
  exact ⟨Rectangle.crop x hw hh, validRectangle_crop hx hw hh⟩

theorem tileableSquare_crop {T : TileSet} {m n : Nat}
    (h : m ≤ n) : TileableSquare T n → TileableSquare T m :=
  tileableRectangle_crop h h

theorem tileableRectangle_product_of_tileableRectangle {base payload : TileSet}
    {w h : Nat} :
    TileableRectangle base w h →
      TileableRectangle payload w h →
      TileableRectangle (productTileSet base payload) w h := by
  rintro ⟨baseRect, hbase⟩ ⟨payloadRect, hpayload⟩
  exact ⟨fun i j => WangTile.product (baseRect i j) (payloadRect i j),
    validRectangle_product_of_validRectangle hbase hpayload⟩

theorem tileableSquare_product_of_tileableSquare {base payload : TileSet}
    {n : Nat} :
    TileableSquare base n →
      TileableSquare payload n →
      TileableSquare (productTileSet base payload) n := by
  exact tileableRectangle_product_of_tileableRectangle

theorem tileableRectangle_left_of_tileableRectangle_productTileSet {base payload : TileSet}
    {w h : Nat} :
    TileableRectangle (productTileSet base payload) w h → TileableRectangle base w h := by
  rintro ⟨rect, hrect⟩
  exact validRectangle_left_of_validRectangle_productTileSet hrect

theorem tileableRectangle_right_of_tileableRectangle_productTileSet {base payload : TileSet}
    {w h : Nat} :
    TileableRectangle (productTileSet base payload) w h → TileableRectangle payload w h := by
  rintro ⟨rect, hrect⟩
  exact validRectangle_right_of_validRectangle_productTileSet hrect

theorem tileableSquare_left_of_tileableSquare_productTileSet {base payload : TileSet}
    {n : Nat} :
    TileableSquare (productTileSet base payload) n → TileableSquare base n :=
  tileableRectangle_left_of_tileableRectangle_productTileSet

theorem tileableSquare_right_of_tileableSquare_productTileSet {base payload : TileSet}
    {n : Nat} :
    TileableSquare (productTileSet base payload) n → TileableSquare payload n :=
  tileableRectangle_right_of_tileableRectangle_productTileSet

/--
A tileset tiles a nonempty `n × n` square with a prescribed tile in the lower-left
corner. The `0 < n` witness avoids manufacturing a corner in the empty square.
-/
def TileableFixedCornerSquare (T : TileSet) (seed : WangTile) (n : Nat) : Prop :=
  ∃ hn : 0 < n, ∃ x : Rectangle n n,
    ValidRectangle T x ∧ x ⟨0, hn⟩ ⟨0, hn⟩ = seed

/-- Restrict a fixed-corner square to a smaller nonempty southwest square. -/
theorem tileableFixedCornerSquare_crop
    {T : TileSet} {seed : WangTile} {m n : Nat}
    (hm : 0 < m) (hmn : m ≤ n) :
    TileableFixedCornerSquare T seed n →
      TileableFixedCornerSquare T seed m := by
  rintro ⟨_, rectangle, valid, corner⟩
  refine ⟨hm, Rectangle.crop rectangle hmn hmn,
    validRectangle_crop valid hmn hmn, ?_⟩
  exact corner

theorem tileableFixedCornerSquare_product_of_tileableFixedCornerSquare
    {base payload : TileSet} {baseSeed payloadSeed : WangTile} {n : Nat} :
    TileableFixedCornerSquare base baseSeed n →
      TileableFixedCornerSquare payload payloadSeed n →
      TileableFixedCornerSquare (productTileSet base payload)
        (WangTile.product baseSeed payloadSeed) n := by
  rintro ⟨hn, baseRect, hbaseValid, hbaseSeed⟩
    ⟨_hn, payloadRect, hpayloadValid, hpayloadSeed⟩
  refine ⟨hn, fun i j => WangTile.product (baseRect i j) (payloadRect i j), ?_, ?_⟩
  · exact validRectangle_product_of_validRectangle hbaseValid hpayloadValid
  · simp [hbaseSeed, hpayloadSeed]

theorem tileableFixedCornerSquare_left_of_tileableFixedCornerSquare_productTileSet
    {base payload : TileSet} {baseSeed payloadSeed : WangTile} {n : Nat} :
    TileableFixedCornerSquare (productTileSet base payload)
        (WangTile.product baseSeed payloadSeed) n →
      TileableFixedCornerSquare base baseSeed n := by
  classical
  rintro ⟨hn, rect, hrect, hseed⟩
  have hdecode : ∀ i : Fin n, ∀ j : Fin n,
      ∃ b : TileIn base, ∃ q : TileIn payload,
        WangTile.product b.1 q.1 = rect i j := by
    intro i j
    rcases mem_productTileSet_iff.1 (hrect.1 i j) with ⟨b, hb, q, hq, htile⟩
    exact ⟨⟨b, hb⟩, ⟨q, hq⟩, htile⟩
  let baseAt : Fin n → Fin n → TileIn base := fun i j => Classical.choose (hdecode i j)
  let payloadAt : Fin n → Fin n → TileIn payload := fun i j =>
    Classical.choose (Classical.choose_spec (hdecode i j))
  have hproduct : ∀ i : Fin n, ∀ j : Fin n,
      WangTile.product (baseAt i j).1 (payloadAt i j).1 = rect i j := by
    intro i j
    exact Classical.choose_spec (Classical.choose_spec (hdecode i j))
  refine ⟨hn, fun i j => (baseAt i j).1, ?_, ?_⟩
  · constructor
    · intro i j
      exact (baseAt i j).2
    constructor
    · intro i j hi
      have hmatch : WangTile.HMatches
          (WangTile.product (baseAt i j).1 (payloadAt i j).1)
          (WangTile.product (baseAt ⟨i.val + 1, hi⟩ j).1
            (payloadAt ⟨i.val + 1, hi⟩ j).1) := by
        simpa [hproduct i j, hproduct ⟨i.val + 1, hi⟩ j] using hrect.2.1 i j hi
      exact (WangTile.HMatches_product_iff
        (baseAt i j).1 (payloadAt i j).1
        (baseAt ⟨i.val + 1, hi⟩ j).1 (payloadAt ⟨i.val + 1, hi⟩ j).1).1 hmatch |>.1
    · intro i j hj
      have hmatch : WangTile.VMatches
          (WangTile.product (baseAt i j).1 (payloadAt i j).1)
          (WangTile.product (baseAt i ⟨j.val + 1, hj⟩).1
            (payloadAt i ⟨j.val + 1, hj⟩).1) := by
        simpa [hproduct i j, hproduct i ⟨j.val + 1, hj⟩] using hrect.2.2 i j hj
      exact (WangTile.VMatches_product_iff
        (baseAt i j).1 (payloadAt i j).1
        (baseAt i ⟨j.val + 1, hj⟩).1 (payloadAt i ⟨j.val + 1, hj⟩).1).1 hmatch |>.1
  · have hcorner :
        WangTile.product (baseAt ⟨0, hn⟩ ⟨0, hn⟩).1
            (payloadAt ⟨0, hn⟩ ⟨0, hn⟩).1 =
          WangTile.product baseSeed payloadSeed := by
      simpa [hproduct ⟨0, hn⟩ ⟨0, hn⟩] using hseed
    exact (product_eq_iff.1 hcorner).1

theorem tileableFixedCornerSquare_right_of_tileableFixedCornerSquare_productTileSet
    {base payload : TileSet} {baseSeed payloadSeed : WangTile} {n : Nat} :
    TileableFixedCornerSquare (productTileSet base payload)
        (WangTile.product baseSeed payloadSeed) n →
      TileableFixedCornerSquare payload payloadSeed n := by
  classical
  rintro ⟨hn, rect, hrect, hseed⟩
  have hdecode : ∀ i : Fin n, ∀ j : Fin n,
      ∃ b : TileIn base, ∃ q : TileIn payload,
        WangTile.product b.1 q.1 = rect i j := by
    intro i j
    rcases mem_productTileSet_iff.1 (hrect.1 i j) with ⟨b, hb, q, hq, htile⟩
    exact ⟨⟨b, hb⟩, ⟨q, hq⟩, htile⟩
  let baseAt : Fin n → Fin n → TileIn base := fun i j => Classical.choose (hdecode i j)
  let payloadAt : Fin n → Fin n → TileIn payload := fun i j =>
    Classical.choose (Classical.choose_spec (hdecode i j))
  have hproduct : ∀ i : Fin n, ∀ j : Fin n,
      WangTile.product (baseAt i j).1 (payloadAt i j).1 = rect i j := by
    intro i j
    exact Classical.choose_spec (Classical.choose_spec (hdecode i j))
  refine ⟨hn, fun i j => (payloadAt i j).1, ?_, ?_⟩
  · constructor
    · intro i j
      exact (payloadAt i j).2
    constructor
    · intro i j hi
      have hmatch : WangTile.HMatches
          (WangTile.product (baseAt i j).1 (payloadAt i j).1)
          (WangTile.product (baseAt ⟨i.val + 1, hi⟩ j).1
            (payloadAt ⟨i.val + 1, hi⟩ j).1) := by
        simpa [hproduct i j, hproduct ⟨i.val + 1, hi⟩ j] using hrect.2.1 i j hi
      exact (WangTile.HMatches_product_iff
        (baseAt i j).1 (payloadAt i j).1
        (baseAt ⟨i.val + 1, hi⟩ j).1 (payloadAt ⟨i.val + 1, hi⟩ j).1).1 hmatch |>.2
    · intro i j hj
      have hmatch : WangTile.VMatches
          (WangTile.product (baseAt i j).1 (payloadAt i j).1)
          (WangTile.product (baseAt i ⟨j.val + 1, hj⟩).1
            (payloadAt i ⟨j.val + 1, hj⟩).1) := by
        simpa [hproduct i j, hproduct i ⟨j.val + 1, hj⟩] using hrect.2.2 i j hj
      exact (WangTile.VMatches_product_iff
        (baseAt i j).1 (payloadAt i j).1
        (baseAt i ⟨j.val + 1, hj⟩).1 (payloadAt i ⟨j.val + 1, hj⟩).1).1 hmatch |>.2
  · have hcorner :
        WangTile.product (baseAt ⟨0, hn⟩ ⟨0, hn⟩).1
            (payloadAt ⟨0, hn⟩ ⟨0, hn⟩).1 =
          WangTile.product baseSeed payloadSeed := by
      simpa [hproduct ⟨0, hn⟩ ⟨0, hn⟩] using hseed
    exact (product_eq_iff.1 hcorner).2

/-- If a plane tiling exists, every finite square is tileable by restriction. -/
theorem tileableSquare_of_tilesPlane {T : TileSet} :
    TilesPlane T → ∀ n : Nat, TileableSquare T n := by
  intro hT n
  rcases hT with ⟨x, hxH, hxV⟩
  refine ⟨fun i j => (x (Int.ofNat i.val, Int.ofNat j.val)).1, ?_⟩
  constructor
  · intro i j
    exact (x (Int.ofNat i.val, Int.ofNat j.val)).2
  constructor
  · intro i j hi
    exact hxH (Int.ofNat i.val, Int.ofNat j.val)
  · intro i j hj
    exact hxV (Int.ofNat i.val, Int.ofNat j.val)

/-- If a plane tiling exists, every centered finite box is tileable by restriction. -/
theorem tileableBox_of_tilesPlane {T : TileSet} :
    TilesPlane T → ∀ r : Nat, TileableBox T r := by
  intro hT r
  rcases hT with ⟨x, hxH, hxV⟩
  refine ⟨fun p => x p.1, ?_⟩
  constructor
  · intro p hp
    exact hxH p.1
  · intro p hp
    exact hxV p.1

/-- A seeded quarter-plane tiling restricts to every nonempty seeded square. -/
theorem fixedCornerSquare_of_tilesQuarterWithSeed {T : TileSet} {seed : WangTile} :
    TilesQuarterWithSeed T seed →
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n := by
  intro hT n hn
  rcases hT with ⟨x, hx, hseed⟩
  rcases hx with ⟨hxH, hxV⟩
  refine ⟨hn, fun i j => (x (i.val, j.val)).1, ?_, ?_⟩
  · constructor
    · intro i j
      exact (x (i.val, j.val)).2
    constructor
    · intro i j hi
      exact hxH (i.val, j.val)
    · intro i j hj
      exact hxV (i.val, j.val)
  · exact hseed

end LeanWang
