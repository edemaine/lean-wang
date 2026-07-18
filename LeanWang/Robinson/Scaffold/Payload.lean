/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Compactness

/-!
# Complete payload palettes

Finite complete palettes let unconstrained scaffold cells absorb any edge
color used by the payload tileset. The routed scaffold construction imports
this module for the palette and its computability proof.
-/

noncomputable section

namespace LeanWang

/-- The four edge colors appearing on a tile. -/
def tileColors (t : WangTile) : List Nat :=
  [t.n, t.s, t.e, t.w]

/-- Edge colors available to inactive payload cells for an instance tileset. -/
def payloadPalette (T : TileSet) : List Nat :=
  0 :: T.flatMap tileColors

/-- Parameters for payload tiles with fixed north color. -/
structure PayloadNParams where
  colors : List Nat
  n : Nat

namespace PayloadNParams

def toTuple (p : PayloadNParams) : List Nat × Nat :=
  (p.colors, p.n)

def ofTuple (p : List Nat × Nat) : PayloadNParams where
  colors := p.1
  n := p.2

def equivTuple : PayloadNParams ≃ List Nat × Nat where
  toFun := toTuple
  invFun := ofTuple
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro p
    rcases p with ⟨colors, n⟩
    rfl

instance instPrimcodable : Primcodable PayloadNParams :=
  Primcodable.ofEquiv (List Nat × Nat) equivTuple

theorem toTuple_primrec : Primrec toTuple := by
  simpa [equivTuple] using
    (Primrec.of_equiv (e := equivTuple) : Primrec equivTuple)

theorem ofTuple_primrec : Primrec ofTuple := by
  simpa [equivTuple] using
    (Primrec.of_equiv_symm (e := equivTuple) : Primrec equivTuple.symm)

theorem colors_primrec : Primrec PayloadNParams.colors :=
  Primrec.fst.comp toTuple_primrec

theorem n_primrec : Primrec PayloadNParams.n :=
  Primrec.snd.comp toTuple_primrec

end PayloadNParams

/-- Parameters for payload tiles with fixed north and south colors. -/
structure PayloadNSParams where
  colors : List Nat
  n : Nat
  s : Nat

namespace PayloadNSParams

def toTuple (p : PayloadNSParams) : List Nat × Nat × Nat :=
  (p.colors, p.n, p.s)

def ofTuple (p : List Nat × Nat × Nat) : PayloadNSParams where
  colors := p.1
  n := p.2.1
  s := p.2.2

def equivTuple : PayloadNSParams ≃ List Nat × Nat × Nat where
  toFun := toTuple
  invFun := ofTuple
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro p
    rcases p with ⟨colors, n, s⟩
    rfl

instance instPrimcodable : Primcodable PayloadNSParams :=
  Primcodable.ofEquiv (List Nat × Nat × Nat) equivTuple

theorem toTuple_primrec : Primrec toTuple := by
  simpa [equivTuple] using
    (Primrec.of_equiv (e := equivTuple) : Primrec equivTuple)

theorem ofTuple_primrec : Primrec ofTuple := by
  simpa [equivTuple] using
    (Primrec.of_equiv_symm (e := equivTuple) : Primrec equivTuple.symm)

theorem colors_primrec : Primrec PayloadNSParams.colors :=
  Primrec.fst.comp toTuple_primrec

theorem n_primrec : Primrec PayloadNSParams.n :=
  Primrec.fst.comp (Primrec.snd.comp toTuple_primrec)

theorem s_primrec : Primrec PayloadNSParams.s :=
  Primrec.snd.comp (Primrec.snd.comp toTuple_primrec)

end PayloadNSParams

/-- Parameters for payload tiles with fixed north, south, and east colors. -/
structure PayloadNSEParams where
  colors : List Nat
  n : Nat
  s : Nat
  e : Nat

namespace PayloadNSEParams

def toTuple (p : PayloadNSEParams) : List Nat × Nat × Nat × Nat :=
  (p.colors, p.n, p.s, p.e)

def ofTuple (p : List Nat × Nat × Nat × Nat) : PayloadNSEParams where
  colors := p.1
  n := p.2.1
  s := p.2.2.1
  e := p.2.2.2

def equivTuple : PayloadNSEParams ≃ List Nat × Nat × Nat × Nat where
  toFun := toTuple
  invFun := ofTuple
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro p
    rcases p with ⟨colors, n, s, e⟩
    rfl

instance instPrimcodable : Primcodable PayloadNSEParams :=
  Primcodable.ofEquiv (List Nat × Nat × Nat × Nat) equivTuple

theorem toTuple_primrec : Primrec toTuple := by
  simpa [equivTuple] using
    (Primrec.of_equiv (e := equivTuple) : Primrec equivTuple)

theorem ofTuple_primrec : Primrec ofTuple := by
  simpa [equivTuple] using
    (Primrec.of_equiv_symm (e := equivTuple) : Primrec equivTuple.symm)

theorem colors_primrec : Primrec PayloadNSEParams.colors :=
  Primrec.fst.comp toTuple_primrec

theorem n_primrec : Primrec PayloadNSEParams.n :=
  Primrec.fst.comp (Primrec.snd.comp toTuple_primrec)

theorem s_primrec : Primrec PayloadNSEParams.s :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))

theorem e_primrec : Primrec PayloadNSEParams.e :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))

end PayloadNSEParams

/-- Payload tiles with fixed north, south, and east colors and west in `colors`. -/
def payloadsWithNSEParams (p : PayloadNSEParams) : TileSet :=
  p.colors.map fun w => { n := p.n, s := p.s, e := p.e, w := w }

/-- Payload tiles with fixed north and south colors and remaining colors in `colors`. -/
def payloadsWithNSParams (p : PayloadNSParams) : TileSet :=
  p.colors.flatMap fun e =>
    payloadsWithNSEParams { colors := p.colors, n := p.n, s := p.s, e := e }

/-- Payload tiles with fixed north color and remaining colors in `colors`. -/
def payloadsWithNParams (p : PayloadNParams) : TileSet :=
  p.colors.flatMap fun s =>
    payloadsWithNSParams { colors := p.colors, n := p.n, s := s }

/-- Payload tiles with fixed north, south, and east colors and west in `colors`. -/
def payloadsWithNSE (colors : List Nat) (n s e : Nat) : TileSet :=
  payloadsWithNSEParams { colors := colors, n := n, s := s, e := e }

/-- Payload tiles with fixed north and south colors and remaining colors in `colors`. -/
def payloadsWithNS (colors : List Nat) (n s : Nat) : TileSet :=
  payloadsWithNSParams { colors := colors, n := n, s := s }

/-- Payload tiles with fixed north color and remaining colors in `colors`. -/
def payloadsWithN (colors : List Nat) (n : Nat) : TileSet :=
  payloadsWithNParams { colors := colors, n := n }

/--
All payload tiles whose edge colors come from a finite color palette.

Inactive scaffold cells use this complete palette, so they can absorb arbitrary
instance-tile edge colors while still keeping the combined tileset finite.
-/
def completePayloadsFromColors (colors : List Nat) : TileSet :=
  colors.flatMap fun n => payloadsWithN colors n

/-- The inactive-cell payload palette induced by an instance tileset. -/
def completePayloads (T : TileSet) : TileSet :=
  completePayloadsFromColors (payloadPalette T)

theorem mem_tileColors_n (t : WangTile) : t.n ∈ tileColors t := by
  simp [tileColors]

theorem mem_tileColors_s (t : WangTile) : t.s ∈ tileColors t := by
  simp [tileColors]

theorem mem_tileColors_e (t : WangTile) : t.e ∈ tileColors t := by
  simp [tileColors]

theorem mem_tileColors_w (t : WangTile) : t.w ∈ tileColors t := by
  simp [tileColors]

theorem zero_mem_payloadPalette (T : TileSet) : 0 ∈ payloadPalette T := by
  simp [payloadPalette]

theorem mem_payloadPalette_of_mem_tileColors {T : TileSet} {t : WangTile}
    {c : Nat} (ht : t ∈ T) (hc : c ∈ tileColors t) :
    c ∈ payloadPalette T := by
  unfold payloadPalette
  simp only [List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨t, ht, hc⟩

theorem mem_payloadPalette_n {T : TileSet} {t : WangTile} (ht : t ∈ T) :
    t.n ∈ payloadPalette T :=
  mem_payloadPalette_of_mem_tileColors ht (mem_tileColors_n t)

theorem mem_payloadPalette_s {T : TileSet} {t : WangTile} (ht : t ∈ T) :
    t.s ∈ payloadPalette T :=
  mem_payloadPalette_of_mem_tileColors ht (mem_tileColors_s t)

theorem mem_payloadPalette_e {T : TileSet} {t : WangTile} (ht : t ∈ T) :
    t.e ∈ payloadPalette T :=
  mem_payloadPalette_of_mem_tileColors ht (mem_tileColors_e t)

theorem mem_payloadPalette_w {T : TileSet} {t : WangTile} (ht : t ∈ T) :
    t.w ∈ payloadPalette T :=
  mem_payloadPalette_of_mem_tileColors ht (mem_tileColors_w t)

theorem mk_mem_payloadsWithNSEParams {p : PayloadNSEParams} {w : Nat}
    (hw : w ∈ p.colors) :
    ({ n := p.n, s := p.s, e := p.e, w := w } : WangTile) ∈
      payloadsWithNSEParams p := by
  unfold payloadsWithNSEParams
  exact List.mem_map.2 ⟨w, hw, rfl⟩

theorem mk_mem_payloadsWithNSParams {p : PayloadNSParams} {e w : Nat}
    (he : e ∈ p.colors) (hw : w ∈ p.colors) :
    ({ n := p.n, s := p.s, e := e, w := w } : WangTile) ∈
      payloadsWithNSParams p := by
  unfold payloadsWithNSParams
  rw [List.mem_flatMap]
  exact ⟨e, he, mk_mem_payloadsWithNSEParams (p :=
    { colors := p.colors, n := p.n, s := p.s, e := e }) hw⟩

theorem mk_mem_payloadsWithNParams {p : PayloadNParams} {s e w : Nat}
    (hs : s ∈ p.colors) (he : e ∈ p.colors) (hw : w ∈ p.colors) :
    ({ n := p.n, s := s, e := e, w := w } : WangTile) ∈
      payloadsWithNParams p := by
  unfold payloadsWithNParams
  rw [List.mem_flatMap]
  exact ⟨s, hs, mk_mem_payloadsWithNSParams (p :=
    { colors := p.colors, n := p.n, s := s }) he hw⟩

theorem mk_mem_completePayloadsFromColors {colors : List Nat}
    {n s e w : Nat}
    (hn : n ∈ colors) (hs : s ∈ colors)
    (he : e ∈ colors) (hw : w ∈ colors) :
    ({ n := n, s := s, e := e, w := w } : WangTile) ∈
      completePayloadsFromColors colors := by
  unfold completePayloadsFromColors
  rw [List.mem_flatMap]
  exact ⟨n, hn, mk_mem_payloadsWithNParams
    (p := { colors := colors, n := n }) hs he hw⟩

theorem mk_mem_completePayloads {T : TileSet}
    {n s e w : Nat}
    (hn : n ∈ payloadPalette T) (hs : s ∈ payloadPalette T)
    (he : e ∈ payloadPalette T) (hw : w ∈ payloadPalette T) :
    ({ n := n, s := s, e := e, w := w } : WangTile) ∈
      completePayloads T := by
  unfold completePayloads
  exact mk_mem_completePayloadsFromColors hn hs he hw

theorem mem_completePayloads_of_mem {T : TileSet} {t : WangTile}
    (ht : t ∈ T) : t ∈ completePayloads T := by
  cases t
  exact mk_mem_completePayloads
    (mem_payloadPalette_n ht)
    (mem_payloadPalette_s ht)
    (mem_payloadPalette_e ht)
    (mem_payloadPalette_w ht)

/--
Any valid rectangle over the instance tileset is also valid over the inactive
payload palette.  The edge constraints are unchanged; only tile membership is
weakened from `T` to `completePayloads T`.
-/
theorem validRectangle_completePayloads_of_validRectangle {T : TileSet}
    {w h : Nat} {x : Rectangle w h}
    (hx : ValidRectangle T x) : ValidRectangle (completePayloads T) x := by
  constructor
  · intro i j
    exact mem_completePayloads_of_mem (hx.1 i j)
  · exact hx.2

theorem tileableRectangle_completePayloads_of_tileableRectangle {T : TileSet}
    {w h : Nat} :
    TileableRectangle T w h → TileableRectangle (completePayloads T) w h := by
  rintro ⟨x, hx⟩
  exact ⟨x, validRectangle_completePayloads_of_validRectangle hx⟩

theorem tileableSquare_completePayloads_of_tileableSquare {T : TileSet}
    {n : Nat} :
    TileableSquare T n → TileableSquare (completePayloads T) n :=
  tileableRectangle_completePayloads_of_tileableRectangle

theorem tileableFixedCornerSquare_completePayloads_of_tileableFixedCornerSquare
    {T : TileSet} {seed : WangTile} {n : Nat} :
    TileableFixedCornerSquare T seed n →
      TileableFixedCornerSquare (completePayloads T) seed n := by
  rintro ⟨hn, x, hx, hseed⟩
  exact ⟨hn, x, validRectangle_completePayloads_of_validRectangle hx, hseed⟩

/--
Box-pattern analogue of `validRectangle_completePayloads_of_validRectangle`.
This is useful for finite scaffold patches, whose backward direction is stated
on centered boxes rather than origin-based rectangles.
-/
theorem validBoxTiling_completePayloads_of_validBoxTiling {T : TileSet}
    {r : Nat} {x : BoxPattern T r} :
    ValidBoxTiling T r x →
      ValidBoxTiling (completePayloads T) r
        (fun p => ⟨(x p).1, mem_completePayloads_of_mem (x p).2⟩) := by
  intro hx
  constructor
  · intro p hp
    exact hx.1 p hp
  · intro p hp
    exact hx.2 p hp

theorem tileableBox_completePayloads_of_tileableBox {T : TileSet} {r : Nat} :
    TileableBox T r → TileableBox (completePayloads T) r := by
  rintro ⟨x, hx⟩
  exact ⟨fun p => ⟨(x p).1, mem_completePayloads_of_mem (x p).2⟩,
    validBoxTiling_completePayloads_of_validBoxTiling hx⟩

theorem monochromeTile_mem_completePayloads (T : TileSet) :
    monochromeTile ∈ completePayloads T := by
  change ({ n := 0, s := 0, e := 0, w := 0 } : WangTile) ∈ completePayloads T
  exact mk_mem_completePayloads
    (zero_mem_payloadPalette T)
    (zero_mem_payloadPalette T)
    (zero_mem_payloadPalette T)
    (zero_mem_payloadPalette T)

/-- Inactive payload tile whose west edge absorbs a specified palette color. -/
def inactivePayloadWithWest (c : Nat) : WangTile where
  n := 0
  s := 0
  e := 0
  w := c

/-- Inactive payload tile whose east edge absorbs a specified palette color. -/
def inactivePayloadWithEast (c : Nat) : WangTile where
  n := 0
  s := 0
  e := c
  w := 0

/-- Inactive payload tile whose south edge absorbs a specified palette color. -/
def inactivePayloadWithSouth (c : Nat) : WangTile where
  n := 0
  s := c
  e := 0
  w := 0

/-- Inactive payload tile whose north edge absorbs a specified palette color. -/
def inactivePayloadWithNorth (c : Nat) : WangTile where
  n := c
  s := 0
  e := 0
  w := 0

theorem inactivePayloadWithWest_mem_completePayloads {T : TileSet} {c : Nat}
    (hc : c ∈ payloadPalette T) :
    inactivePayloadWithWest c ∈ completePayloads T := by
  change ({ n := 0, s := 0, e := 0, w := c } : WangTile) ∈ completePayloads T
  exact mk_mem_completePayloads
    (zero_mem_payloadPalette T)
    (zero_mem_payloadPalette T)
    (zero_mem_payloadPalette T)
    hc

theorem inactivePayloadWithEast_mem_completePayloads {T : TileSet} {c : Nat}
    (hc : c ∈ payloadPalette T) :
    inactivePayloadWithEast c ∈ completePayloads T := by
  change ({ n := 0, s := 0, e := c, w := 0 } : WangTile) ∈ completePayloads T
  exact mk_mem_completePayloads
    (zero_mem_payloadPalette T)
    (zero_mem_payloadPalette T)
    hc
    (zero_mem_payloadPalette T)

theorem inactivePayloadWithSouth_mem_completePayloads {T : TileSet} {c : Nat}
    (hc : c ∈ payloadPalette T) :
    inactivePayloadWithSouth c ∈ completePayloads T := by
  change ({ n := 0, s := c, e := 0, w := 0 } : WangTile) ∈ completePayloads T
  exact mk_mem_completePayloads
    (zero_mem_payloadPalette T)
    hc
    (zero_mem_payloadPalette T)
    (zero_mem_payloadPalette T)

theorem inactivePayloadWithNorth_mem_completePayloads {T : TileSet} {c : Nat}
    (hc : c ∈ payloadPalette T) :
    inactivePayloadWithNorth c ∈ completePayloads T := by
  change ({ n := c, s := 0, e := 0, w := 0 } : WangTile) ∈ completePayloads T
  exact mk_mem_completePayloads
    hc
    (zero_mem_payloadPalette T)
    (zero_mem_payloadPalette T)
    (zero_mem_payloadPalette T)

theorem hMatches_inactivePayloadWithWest (t : WangTile) :
    WangTile.HMatches t (inactivePayloadWithWest t.e) := by
  rfl

theorem hMatches_inactivePayloadWithEast (t : WangTile) :
    WangTile.HMatches (inactivePayloadWithEast t.w) t := by
  rfl

theorem vMatches_inactivePayloadWithSouth (t : WangTile) :
    WangTile.VMatches t (inactivePayloadWithSouth t.n) := by
  rfl

theorem vMatches_inactivePayloadWithNorth (t : WangTile) :
    WangTile.VMatches (inactivePayloadWithNorth t.s) t := by
  rfl

theorem inactivePayloadWithWest_mem_completePayloads_of_mem
    {T : TileSet} {t : WangTile} (ht : t ∈ T) :
    inactivePayloadWithWest t.e ∈ completePayloads T :=
  inactivePayloadWithWest_mem_completePayloads (mem_payloadPalette_e ht)

theorem inactivePayloadWithEast_mem_completePayloads_of_mem
    {T : TileSet} {t : WangTile} (ht : t ∈ T) :
    inactivePayloadWithEast t.w ∈ completePayloads T :=
  inactivePayloadWithEast_mem_completePayloads (mem_payloadPalette_w ht)

theorem inactivePayloadWithSouth_mem_completePayloads_of_mem
    {T : TileSet} {t : WangTile} (ht : t ∈ T) :
    inactivePayloadWithSouth t.n ∈ completePayloads T :=
  inactivePayloadWithSouth_mem_completePayloads (mem_payloadPalette_n ht)

theorem inactivePayloadWithNorth_mem_completePayloads_of_mem
    {T : TileSet} {t : WangTile} (ht : t ∈ T) :
    inactivePayloadWithNorth t.s ∈ completePayloads T :=
  inactivePayloadWithNorth_mem_completePayloads (mem_payloadPalette_s ht)

theorem tileColors_primrec : Primrec tileColors := by
  unfold tileColors
  exact Primrec.list_cons.comp WangTile.n_primrec
    (Primrec.list_cons.comp WangTile.s_primrec
      (Primrec.list_cons.comp WangTile.e_primrec
        (Primrec.list_cons.comp WangTile.w_primrec (Primrec.const []))))

theorem payloadPalette_primrec : Primrec payloadPalette := by
  unfold payloadPalette
  exact Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_flatMap Primrec.id
      (Primrec₂.mk (tileColors_primrec.comp Primrec.snd)))

theorem payloadsWithNSEParams_primrec : Primrec payloadsWithNSEParams := by
  unfold payloadsWithNSEParams
  refine Primrec.list_map PayloadNSEParams.colors_primrec ?_
  have hn : Primrec₂ (fun (p : PayloadNSEParams) (_w : Nat) => p.n) :=
    PayloadNSEParams.n_primrec.comp₂ Primrec₂.left
  have hs : Primrec₂ (fun (p : PayloadNSEParams) (_w : Nat) => p.s) :=
    PayloadNSEParams.s_primrec.comp₂ Primrec₂.left
  have he : Primrec₂ (fun (p : PayloadNSEParams) (_w : Nat) => p.e) :=
    PayloadNSEParams.e_primrec.comp₂ Primrec₂.left
  have hw : Primrec₂ (fun (_p : PayloadNSEParams) (w : Nat) => w) :=
    Primrec₂.right
  have htuple : Primrec₂ (fun (p : PayloadNSEParams) (w : Nat) =>
      (p.n, p.s, p.e, w)) :=
    Primrec₂.pair.comp₂ hn (Primrec₂.pair.comp₂ hs (Primrec₂.pair.comp₂ he hw))
  exact WangTile.ofTuple_primrec.comp₂ htuple

theorem payloadNSEParamsOfNS_primrec₂ :
    Primrec₂ (fun (p : PayloadNSParams) (e : Nat) =>
      ({ colors := p.colors, n := p.n, s := p.s, e := e } : PayloadNSEParams)) := by
  have hcolors : Primrec₂ (fun (p : PayloadNSParams) (_e : Nat) => p.colors) :=
    PayloadNSParams.colors_primrec.comp₂ Primrec₂.left
  have hn : Primrec₂ (fun (p : PayloadNSParams) (_e : Nat) => p.n) :=
    PayloadNSParams.n_primrec.comp₂ Primrec₂.left
  have hs : Primrec₂ (fun (p : PayloadNSParams) (_e : Nat) => p.s) :=
    PayloadNSParams.s_primrec.comp₂ Primrec₂.left
  have he : Primrec₂ (fun (_p : PayloadNSParams) (e : Nat) => e) :=
    Primrec₂.right
  have htuple : Primrec₂ (fun (p : PayloadNSParams) (e : Nat) =>
      (p.colors, p.n, p.s, e)) :=
    Primrec₂.pair.comp₂ hcolors (Primrec₂.pair.comp₂ hn (Primrec₂.pair.comp₂ hs he))
  exact PayloadNSEParams.ofTuple_primrec.comp₂ htuple

theorem payloadsWithNSParams_primrec : Primrec payloadsWithNSParams := by
  unfold payloadsWithNSParams
  refine Primrec.list_flatMap PayloadNSParams.colors_primrec ?_
  exact payloadsWithNSEParams_primrec.comp₂ payloadNSEParamsOfNS_primrec₂

theorem payloadNSParamsOfN_primrec₂ :
    Primrec₂ (fun (p : PayloadNParams) (s : Nat) =>
      ({ colors := p.colors, n := p.n, s := s } : PayloadNSParams)) := by
  have hcolors : Primrec₂ (fun (p : PayloadNParams) (_s : Nat) => p.colors) :=
    PayloadNParams.colors_primrec.comp₂ Primrec₂.left
  have hn : Primrec₂ (fun (p : PayloadNParams) (_s : Nat) => p.n) :=
    PayloadNParams.n_primrec.comp₂ Primrec₂.left
  have hs : Primrec₂ (fun (_p : PayloadNParams) (s : Nat) => s) :=
    Primrec₂.right
  have htuple : Primrec₂ (fun (p : PayloadNParams) (s : Nat) =>
      (p.colors, p.n, s)) :=
    Primrec₂.pair.comp₂ hcolors (Primrec₂.pair.comp₂ hn hs)
  exact PayloadNSParams.ofTuple_primrec.comp₂ htuple

theorem payloadsWithNParams_primrec : Primrec payloadsWithNParams := by
  unfold payloadsWithNParams
  refine Primrec.list_flatMap PayloadNParams.colors_primrec ?_
  exact payloadsWithNSParams_primrec.comp₂ payloadNSParamsOfN_primrec₂

theorem payloadNParamsOfColors_primrec₂ :
    Primrec₂ (fun (colors : List Nat) (n : Nat) =>
      ({ colors := colors, n := n } : PayloadNParams)) := by
  have htuple : Primrec₂ (fun (colors : List Nat) (n : Nat) => (colors, n)) :=
    Primrec₂.pair
  exact PayloadNParams.ofTuple_primrec.comp₂ htuple

theorem completePayloadsFromColors_primrec : Primrec completePayloadsFromColors := by
  unfold completePayloadsFromColors
  refine Primrec.list_flatMap Primrec.id ?_
  exact payloadsWithNParams_primrec.comp₂ payloadNParamsOfColors_primrec₂

theorem completePayloads_primrec : Primrec completePayloads :=
  completePayloadsFromColors_primrec.comp payloadPalette_primrec

namespace PayloadCompletion

/-- Fill one unconstrained cell with the colors of its constrained neighbors. -/
def inactiveAround {r : Nat} (isActive : Box r → Bool)
    (activePayload : Box r → WangTile) (p : Box r) : WangTile where
  n :=
    if hp : InBox r (p.1.1, p.1.2 + 1) then
      let q : Box r := ⟨(p.1.1, p.1.2 + 1), hp⟩
      if isActive q = true then (activePayload q).s else 0
    else 0
  s :=
    if hp : InBox r (p.1.1, p.1.2 - 1) then
      let q : Box r := ⟨(p.1.1, p.1.2 - 1), hp⟩
      if isActive q = true then (activePayload q).n else 0
    else 0
  e :=
    if hp : InBox r (p.1.1 + 1, p.1.2) then
      let q : Box r := ⟨(p.1.1 + 1, p.1.2), hp⟩
      if isActive q = true then (activePayload q).w else 0
    else 0
  w :=
    if hp : InBox r (p.1.1 - 1, p.1.2) then
      let q : Box r := ⟨(p.1.1 - 1, p.1.2), hp⟩
      if isActive q = true then (activePayload q).e else 0
    else 0

/-- Keep constrained payloads and complete every other cell locally. -/
def complete {r : Nat} (isActive : Box r → Bool)
    (activePayload : Box r → WangTile) (p : Box r) : WangTile :=
  if isActive p = true then activePayload p
  else inactiveAround isActive activePayload p

theorem complete_hmatch {r : Nat}
    {isActive : Box r → Bool} {activePayload : Box r → WangTile}
    (hactive :
      ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
        isActive p = true →
          isActive ⟨(p.1.1 + 1, p.1.2), hp⟩ = true →
            WangTile.HMatches (activePayload p)
              (activePayload ⟨(p.1.1 + 1, p.1.2), hp⟩))
    (p : Box r) (hp : InBox r (p.1.1 + 1, p.1.2)) :
    WangTile.HMatches
      (complete isActive activePayload p)
      (complete isActive activePayload
        ⟨(p.1.1 + 1, p.1.2), hp⟩) := by
  let q : Box r := ⟨(p.1.1 + 1, p.1.2), hp⟩
  by_cases hpActive : isActive p = true
  · by_cases hqActive : isActive q = true
    · simpa [complete, q, hpActive, hqActive] using
        hactive p hp hpActive hqActive
    · simp [WangTile.HMatches, complete, inactiveAround,
        q, hpActive, hqActive, p.2]
  · by_cases hqActive : isActive q = true
    · simp [WangTile.HMatches, complete, inactiveAround,
        q, hpActive, hqActive, hp]
    · simp [WangTile.HMatches, complete, inactiveAround,
        q, hpActive, hqActive, hp, p.2]

theorem complete_vmatch {r : Nat}
    {isActive : Box r → Bool} {activePayload : Box r → WangTile}
    (hactive :
      ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
        isActive p = true →
          isActive ⟨(p.1.1, p.1.2 + 1), hp⟩ = true →
            WangTile.VMatches (activePayload p)
              (activePayload ⟨(p.1.1, p.1.2 + 1), hp⟩))
    (p : Box r) (hp : InBox r (p.1.1, p.1.2 + 1)) :
    WangTile.VMatches
      (complete isActive activePayload p)
      (complete isActive activePayload
        ⟨(p.1.1, p.1.2 + 1), hp⟩) := by
  let q : Box r := ⟨(p.1.1, p.1.2 + 1), hp⟩
  by_cases hpActive : isActive p = true
  · by_cases hqActive : isActive q = true
    · simpa [complete, q, hpActive, hqActive] using
        hactive p hp hpActive hqActive
    · simp [WangTile.VMatches, complete, inactiveAround,
        q, hpActive, hqActive, p.2]
  · by_cases hqActive : isActive q = true
    · simp [WangTile.VMatches, complete, inactiveAround,
        q, hpActive, hqActive, hp]
    · simp [WangTile.VMatches, complete, inactiveAround,
        q, hpActive, hqActive, hp, p.2]

end PayloadCompletion

end LeanWang

end
