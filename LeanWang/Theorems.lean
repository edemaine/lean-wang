/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Compactness
import LeanWang.Machine
import LeanWang.MachineTiles

/-!
Main theorem surface for the Wang-tile undecidability proof.

This file collects the generic tiling theorems used by the reduction:
machine-tile correctness, fixed-corner-square compactness, and the abstract
scaffold construction. The fixed universal-machine specialization is kept in
`UniversalTM0Reduction`.
-/

noncomputable section

namespace LeanWang

/-- Correctness of the machine-to-Wang-tile fixed domino construction. -/
theorem machineTiles_correct (M : Machine) :
    TilesQuarterWithSeed (machineTiles M) (machineSeed M) ↔ ¬ Machine.HaltsEmpty M := by
  constructor
  · intro htiles hhalts
    rcases hhalts with ⟨n, hhalt⟩
    exact not_tilesQuarterWithSeed_machineTiles_of_halts_at n hhalt htiles
  · intro hnonhalts
    exact tilesQuarterWithSeed_machineTiles_of_not_halts hnonhalts

/-- Correctness of the table-program fixed-domino construction. -/
theorem tableProgramFixedDomino_correct (P : TableProgram) :
    TilesQuarterWithSeed (tableProgramFixedDomino P).1 (tableProgramFixedDomino P).2 ↔
      ¬ Machine.HaltsEmpty P.toMachine := by
  unfold tableProgramFixedDomino tableProgramTiles tableProgramSeed
  exact machineTiles_correct P.toMachine

/-- Data for a scaffold tileset used to force arbitrarily large free squares. -/
structure Scaffold where
  tiles : TileSet
  active : WangTile → Bool
  corner : WangTile
  active_primrec : Primrec active

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

/--
Payload symbols carried by a scaffold tile. Active scaffold cells carry the
instance tileset, with the marked corner restricted to the requested seed.
Inactive scaffold cells carry every tile over the instance edge-color palette,
so they do not force the instance tileset outside the free regions but can still
match active-cell boundary colors.
-/
def scaffoldPayloads (S : Scaffold) (T : TileSet) (seed b : WangTile) : TileSet :=
  if S.active b then
    if b = S.corner then T.filter fun p => p = seed else T
  else
    completePayloads T

/-- Combine a scaffold with a fixed-corner square instance. -/
def combineWithScaffold (S : Scaffold) (T : TileSet) (seed : WangTile) : TileSet :=
  S.tiles.flatMap fun b =>
    (scaffoldPayloads S T seed b).map fun p => WangTile.product b p

theorem mem_combineWithScaffold_iff {S : Scaffold} {T : TileSet}
    {seed tile : WangTile} :
    tile ∈ combineWithScaffold S T seed ↔
      ∃ b ∈ S.tiles, ∃ p : WangTile,
        (S.active b = true → p ∈ T ∧ (b = S.corner → p = seed)) ∧
          (S.active b = false → p ∈ completePayloads T) ∧
          WangTile.product b p = tile := by
  constructor
  · intro htile
    rw [combineWithScaffold, List.mem_flatMap] at htile
    rcases htile with ⟨b, hb, hpayload⟩
    by_cases hactive : S.active b = true
    · rw [scaffoldPayloads, if_pos hactive] at hpayload
      by_cases hcorner : b = S.corner
      · rw [if_pos hcorner, List.mem_map] at hpayload
        rcases hpayload with ⟨p, hp, htile⟩
        refine ⟨b, hb, p, ?_⟩
        have hmem : S.active b = true → p ∈ T ∧ (b = S.corner → p = seed) := by
          intro _hactive
          exact ⟨(List.mem_filter.1 hp).1,
            by intro _; exact of_decide_eq_true (List.mem_filter.1 hp).2⟩
        have hinactive : S.active b = false → p ∈ completePayloads T := by
          intro hfalse
          rw [hactive] at hfalse
          nomatch hfalse
        exact And.intro hmem (And.intro hinactive htile)
      · rw [if_neg hcorner, List.mem_map] at hpayload
        rcases hpayload with ⟨p, hp, htile⟩
        refine ⟨b, hb, p, ?_⟩
        have hmem : S.active b = true → p ∈ T ∧ (b = S.corner → p = seed) := by
          intro _hactive
          exact ⟨hp, by intro hbcorner; exact False.elim (hcorner hbcorner)⟩
        have hinactive : S.active b = false → p ∈ completePayloads T := by
          intro hfalse
          rw [hactive] at hfalse
          nomatch hfalse
        exact And.intro hmem (And.intro hinactive htile)
    · have hfalse : S.active b = false := by
        cases h : S.active b
        · rfl
        · exact False.elim (hactive h)
      rw [scaffoldPayloads, if_neg hactive, List.mem_map] at hpayload
      rcases hpayload with ⟨p, hp, htile⟩
      refine ⟨b, hb, p, ?_⟩
      have hmem : S.active b = true → p ∈ T ∧ (b = S.corner → p = seed) := by
        intro htrue
        rw [hfalse] at htrue
        nomatch htrue
      have hinactive : S.active b = false → p ∈ completePayloads T := by
        intro _
        exact hp
      exact And.intro hmem (And.intro hinactive htile)
  · rintro ⟨b, hb, p, hactiveMem, hinactive, htile⟩
    rw [combineWithScaffold, List.mem_flatMap]
    refine ⟨b, hb, ?_⟩
    by_cases hactive : S.active b = true
    · rw [scaffoldPayloads, if_pos hactive]
      by_cases hcorner : b = S.corner
      · rw [if_pos hcorner, List.mem_map]
        exact ⟨p, List.mem_filter.2 ⟨(hactiveMem hactive).1,
          decide_eq_true ((hactiveMem hactive).2 hcorner)⟩, htile⟩
      · rw [if_neg hcorner, List.mem_map]
        exact ⟨p, (hactiveMem hactive).1, htile⟩
    · rw [scaffoldPayloads, if_neg hactive, List.mem_map]
      exact ⟨p, hinactive (by
        cases h : S.active b
        · rfl
        · exact False.elim (hactive h)), htile⟩

/--
A finite centered-box patch over the scaffold/product tileset, stated in the
base/payload language used by the Robinson board construction.
-/
structure CombinedBoxPatch (S : Scaffold) (T : TileSet) (seed : WangTile)
    (r : Nat) where
  base : Box r → WangTile
  payload : Box r → WangTile
  base_mem : ∀ p : Box r, base p ∈ S.tiles
  active_payload : ∀ p : Box r, S.active (base p) = true →
    payload p ∈ T ∧ (base p = S.corner → payload p = seed)
  inactive_payload : ∀ p : Box r, S.active (base p) = false →
    payload p ∈ completePayloads T
  hmatch : ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
    WangTile.HMatches
      (WangTile.product (base p) (payload p))
      (WangTile.product (base ⟨(p.1.1 + 1, p.1.2), hp⟩)
        (payload ⟨(p.1.1 + 1, p.1.2), hp⟩))
  vmatch : ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
    WangTile.VMatches
      (WangTile.product (base p) (payload p))
      (WangTile.product (base ⟨(p.1.1, p.1.2 + 1), hp⟩)
        (payload ⟨(p.1.1, p.1.2 + 1), hp⟩))

namespace CombinedBoxPatch

theorem product_mem {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r : Nat} (patch : CombinedBoxPatch S T seed r) (p : Box r) :
    WangTile.product (patch.base p) (patch.payload p) ∈
      combineWithScaffold S T seed := by
  rw [mem_combineWithScaffold_iff]
  exact ⟨patch.base p, patch.base_mem p, patch.payload p,
    patch.active_payload p, patch.inactive_payload p, rfl⟩

/-- View a combined box patch as an ordinary finite box pattern. -/
def toBoxPattern {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r : Nat} (patch : CombinedBoxPatch S T seed r) :
    BoxPattern (combineWithScaffold S T seed) r :=
  fun p =>
    ⟨WangTile.product (patch.base p) (patch.payload p),
      patch.product_mem p⟩

theorem validBoxTiling_toBoxPattern {S : Scaffold} {T : TileSet}
    {seed : WangTile} {r : Nat} (patch : CombinedBoxPatch S T seed r) :
    ValidBoxTiling (combineWithScaffold S T seed) r patch.toBoxPattern := by
  constructor
  · intro p hp
    exact patch.hmatch p hp
  · intro p hp
    exact patch.vmatch p hp

theorem tileableBox {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r : Nat} (patch : CombinedBoxPatch S T seed r) :
    TileableBox (combineWithScaffold S T seed) r :=
  ⟨patch.toBoxPattern, patch.validBoxTiling_toBoxPattern⟩
end CombinedBoxPatch

/--
Layered form of a finite combined box patch.

This is closer to how the Robinson proof constructs finite patches: first give
a valid scaffold/base box, then give payload labels satisfying the active-cell
membership restrictions and payload edge matches.  Product edge matches are
derived mechanically from the base and payload matches.
-/
structure CombinedBoxLayerPatch (S : Scaffold) (T : TileSet) (seed : WangTile)
    (r : Nat) where
  base : BoxPattern S.tiles r
  payload : Box r → WangTile
  base_valid : ValidBoxTiling S.tiles r base
  active_payload : ∀ p : Box r, S.active (base p).1 = true →
    payload p ∈ T ∧ ((base p).1 = S.corner → payload p = seed)
  inactive_payload : ∀ p : Box r, S.active (base p).1 = false →
    payload p ∈ completePayloads T
  payload_hmatch : ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
    WangTile.HMatches (payload p)
      (payload ⟨(p.1.1 + 1, p.1.2), hp⟩)
  payload_vmatch : ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
    WangTile.VMatches (payload p)
      (payload ⟨(p.1.1, p.1.2 + 1), hp⟩)

namespace CombinedBoxLayerPatch

/-- Forget the separated base/payload proof into the product-patch form. -/
def toCombinedBoxPatch {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r : Nat} (patch : CombinedBoxLayerPatch S T seed r) :
    CombinedBoxPatch S T seed r where
  base := fun p => (patch.base p).1
  payload := patch.payload
  base_mem := fun p => (patch.base p).2
  active_payload := patch.active_payload
  inactive_payload := patch.inactive_payload
  hmatch := by
    intro p hp
    exact (WangTile.HMatches_product_iff
      (patch.base p).1 (patch.payload p)
      (patch.base ⟨(p.1.1 + 1, p.1.2), hp⟩).1
      (patch.payload ⟨(p.1.1 + 1, p.1.2), hp⟩)).2
        ⟨patch.base_valid.1 p hp, patch.payload_hmatch p hp⟩
  vmatch := by
    intro p hp
    exact (WangTile.VMatches_product_iff
      (patch.base p).1 (patch.payload p)
      (patch.base ⟨(p.1.1, p.1.2 + 1), hp⟩).1
      (patch.payload ⟨(p.1.1, p.1.2 + 1), hp⟩)).2
        ⟨patch.base_valid.2 p hp, patch.payload_vmatch p hp⟩

theorem tileableBox {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r : Nat} (patch : CombinedBoxLayerPatch S T seed r) :
    TileableBox (combineWithScaffold S T seed) r :=
  patch.toCombinedBoxPatch.tileableBox

/--
Inactive payload tile that absorbs the payload colors of any active neighboring
box cells and uses color `0` on sides without an active neighbor.
-/
def inactivePayloadAround {r : Nat} (isActive : Box r → Bool)
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

def payloadWithInactiveAround {r : Nat} (isActive : Box r → Bool)
    (activePayload : Box r → WangTile) (p : Box r) : WangTile :=
  if isActive p = true then activePayload p
  else inactivePayloadAround isActive activePayload p

theorem inactivePayloadAround_mem_completePayloads {T : TileSet} {r : Nat}
    {isActive : Box r → Bool} {activePayload : Box r → WangTile}
    (hmem : ∀ p : Box r, isActive p = true → activePayload p ∈ T)
    (p : Box r) :
    inactivePayloadAround isActive activePayload p ∈ completePayloads T := by
  refine mk_mem_completePayloads ?_ ?_ ?_ ?_
  · split
    · rename_i hp
      by_cases hactive :
          isActive ⟨(p.1.1, p.1.2 + 1), hp⟩ = true
      · simp [hactive, mem_payloadPalette_s (hmem _ hactive)]
      · simp [hactive, zero_mem_payloadPalette]
    · simp [zero_mem_payloadPalette]
  · split
    · rename_i hp
      by_cases hactive :
          isActive ⟨(p.1.1, p.1.2 - 1), hp⟩ = true
      · simp [hactive, mem_payloadPalette_n (hmem _ hactive)]
      · simp [hactive, zero_mem_payloadPalette]
    · simp [zero_mem_payloadPalette]
  · split
    · rename_i hp
      by_cases hactive :
          isActive ⟨(p.1.1 + 1, p.1.2), hp⟩ = true
      · simp [hactive, mem_payloadPalette_w (hmem _ hactive)]
      · simp [hactive, zero_mem_payloadPalette]
    · simp [zero_mem_payloadPalette]
  · split
    · rename_i hp
      by_cases hactive :
          isActive ⟨(p.1.1 - 1, p.1.2), hp⟩ = true
      · simp [hactive, mem_payloadPalette_e (hmem _ hactive)]
      · simp [hactive, zero_mem_payloadPalette]
    · simp [zero_mem_payloadPalette]

theorem payloadWithInactiveAround_hmatch {r : Nat}
    {isActive : Box r → Bool} {activePayload : Box r → WangTile}
    (hactive :
      ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
        isActive p = true →
          isActive ⟨(p.1.1 + 1, p.1.2), hp⟩ = true →
            WangTile.HMatches (activePayload p)
              (activePayload ⟨(p.1.1 + 1, p.1.2), hp⟩))
    (p : Box r) (hp : InBox r (p.1.1 + 1, p.1.2)) :
    WangTile.HMatches
      (payloadWithInactiveAround isActive activePayload p)
      (payloadWithInactiveAround isActive activePayload
        ⟨(p.1.1 + 1, p.1.2), hp⟩) := by
  let q : Box r := ⟨(p.1.1 + 1, p.1.2), hp⟩
  by_cases hpActive : isActive p = true
  · by_cases hqActive : isActive q = true
    · simpa [payloadWithInactiveAround, q, hpActive, hqActive] using
        hactive p hp hpActive hqActive
    · simp [WangTile.HMatches, payloadWithInactiveAround,
        inactivePayloadAround, q, hpActive, hqActive, p.2]
  · by_cases hqActive : isActive q = true
    · simp [WangTile.HMatches, payloadWithInactiveAround,
        inactivePayloadAround, q, hpActive, hqActive, hp]
    · simp [WangTile.HMatches, payloadWithInactiveAround,
        inactivePayloadAround, q, hpActive, hqActive, hp, p.2]

theorem payloadWithInactiveAround_vmatch {r : Nat}
    {isActive : Box r → Bool} {activePayload : Box r → WangTile}
    (hactive :
      ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
        isActive p = true →
          isActive ⟨(p.1.1, p.1.2 + 1), hp⟩ = true →
            WangTile.VMatches (activePayload p)
              (activePayload ⟨(p.1.1, p.1.2 + 1), hp⟩))
    (p : Box r) (hp : InBox r (p.1.1, p.1.2 + 1)) :
    WangTile.VMatches
      (payloadWithInactiveAround isActive activePayload p)
      (payloadWithInactiveAround isActive activePayload
        ⟨(p.1.1, p.1.2 + 1), hp⟩) := by
  let q : Box r := ⟨(p.1.1, p.1.2 + 1), hp⟩
  by_cases hpActive : isActive p = true
  · by_cases hqActive : isActive q = true
    · simpa [payloadWithInactiveAround, q, hpActive, hqActive] using
        hactive p hp hpActive hqActive
    · simp [WangTile.VMatches, payloadWithInactiveAround,
        inactivePayloadAround, q, hpActive, hqActive, p.2]
  · by_cases hqActive : isActive q = true
    · simp [WangTile.VMatches, payloadWithInactiveAround,
        inactivePayloadAround, q, hpActive, hqActive, hp]
    · simp [WangTile.VMatches, payloadWithInactiveAround,
        inactivePayloadAround, q, hpActive, hqActive, hp, p.2]

/--
Assemble a layer patch from a base scaffold box and payloads prescribed only
on active cells.  Inactive cells are filled automatically by the complete
payload palette so that they absorb neighboring active payload colors.
-/
def ofActivePayloads {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r : Nat}
    (base : BoxPattern S.tiles r)
    (base_valid : ValidBoxTiling S.tiles r base)
    (activePayload : Box r → WangTile)
    (active_payload : ∀ p : Box r, S.active (base p).1 = true →
      activePayload p ∈ T ∧ ((base p).1 = S.corner → activePayload p = seed))
    (active_hmatch :
      ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
        S.active (base p).1 = true →
          S.active (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1 = true →
            WangTile.HMatches (activePayload p)
              (activePayload ⟨(p.1.1 + 1, p.1.2), hp⟩))
    (active_vmatch :
      ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
        S.active (base p).1 = true →
          S.active (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1 = true →
            WangTile.VMatches (activePayload p)
              (activePayload ⟨(p.1.1, p.1.2 + 1), hp⟩)) :
    CombinedBoxLayerPatch S T seed r where
  base := base
  payload :=
    payloadWithInactiveAround (fun p => S.active (base p).1) activePayload
  base_valid := base_valid
  active_payload := by
    intro p hactive
    simpa [payloadWithInactiveAround, hactive] using active_payload p hactive
  inactive_payload := by
    intro p hinactive
    have hmem :
        ∀ q : Box r, S.active (base q).1 = true → activePayload q ∈ T := by
      intro q hq
      exact (active_payload q hq).1
    rw [payloadWithInactiveAround, if_neg]
    · exact inactivePayloadAround_mem_completePayloads hmem p
    · simp [hinactive]
  payload_hmatch := by
    intro p hp
    exact payloadWithInactiveAround_hmatch active_hmatch p hp
  payload_vmatch := by
    intro p hp
    exact payloadWithInactiveAround_vmatch active_vmatch p hp

/--
Version of `ofActivePayloads` where active box cells read their payloads from a
single fixed-corner square.  The geometric proof only has to provide the index
map from active scaffold cells into that square and prove the induced active
adjacencies.
-/
def ofActivePayloadRectangle {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r n : Nat} (hn : 0 < n)
    (base : BoxPattern S.tiles r)
    (base_valid : ValidBoxTiling S.tiles r base)
    (payloadRect : Rectangle n n)
    (payload_valid : ValidRectangle T payloadRect)
    (payload_seed : payloadRect ⟨0, hn⟩ ⟨0, hn⟩ = seed)
    (index : Box r → Fin n × Fin n)
    (corner_index :
      ∀ p : Box r, S.active (base p).1 = true →
        (base p).1 = S.corner →
          index p = (⟨0, hn⟩, ⟨0, hn⟩))
    (active_hmatch :
      ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
        S.active (base p).1 = true →
          S.active (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1 = true →
            WangTile.HMatches
              (payloadRect (index p).1 (index p).2)
              (payloadRect
                (index ⟨(p.1.1 + 1, p.1.2), hp⟩).1
                (index ⟨(p.1.1 + 1, p.1.2), hp⟩).2))
    (active_vmatch :
      ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
        S.active (base p).1 = true →
          S.active (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1 = true →
            WangTile.VMatches
              (payloadRect (index p).1 (index p).2)
              (payloadRect
                (index ⟨(p.1.1, p.1.2 + 1), hp⟩).1
                (index ⟨(p.1.1, p.1.2 + 1), hp⟩).2)) :
    CombinedBoxLayerPatch S T seed r :=
  ofActivePayloads base base_valid
    (fun p => payloadRect (index p).1 (index p).2)
    (by
      intro p hactive
      constructor
      · exact payload_valid.1 (index p).1 (index p).2
      · intro hcorner
        rw [corner_index p hactive hcorner]
        exact payload_seed)
    active_hmatch
    active_vmatch

/--
`TileableFixedCornerSquare` wrapper around `ofActivePayloadRectangle`.
-/
def ofActivePayloadFixedCornerSquare
    {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r n : Nat}
    (base : BoxPattern S.tiles r)
    (base_valid : ValidBoxTiling S.tiles r base)
    (square : TileableFixedCornerSquare T seed n)
    (index : Box r → Fin n × Fin n)
    (corner_index :
      ∀ p : Box r, S.active (base p).1 = true →
        (base p).1 = S.corner →
          index p =
            (⟨0, square.choose⟩, ⟨0, square.choose⟩))
    (active_hmatch :
      ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
        S.active (base p).1 = true →
          S.active (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1 = true →
            WangTile.HMatches
              (square.choose_spec.choose (index p).1 (index p).2)
              (square.choose_spec.choose
                (index ⟨(p.1.1 + 1, p.1.2), hp⟩).1
                (index ⟨(p.1.1 + 1, p.1.2), hp⟩).2))
    (active_vmatch :
      ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
        S.active (base p).1 = true →
          S.active (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1 = true →
            WangTile.VMatches
              (square.choose_spec.choose (index p).1 (index p).2)
              (square.choose_spec.choose
                (index ⟨(p.1.1, p.1.2 + 1), hp⟩).1
                (index ⟨(p.1.1, p.1.2 + 1), hp⟩).2)) :
    CombinedBoxLayerPatch S T seed r :=
  ofActivePayloadRectangle square.choose base base_valid
    square.choose_spec.choose
    square.choose_spec.choose_spec.1
    square.choose_spec.choose_spec.2
    index corner_index active_hmatch active_vmatch

/--
Build a layer patch over a scaffold box that is entirely inactive.  Active-cell
payload obligations are contradictory, and inactive payload membership is
supplied by the complete payload box.
-/
def ofInactivePayloadBox {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r : Nat}
    (base : BoxPattern S.tiles r)
    (base_valid : ValidBoxTiling S.tiles r base)
    (base_inactive : ∀ p : Box r, S.active (base p).1 = false)
    (payload : BoxPattern (completePayloads T) r)
    (payload_valid : ValidBoxTiling (completePayloads T) r payload) :
    CombinedBoxLayerPatch S T seed r where
  base := base
  payload := fun p => (payload p).1
  base_valid := base_valid
  active_payload := by
    intro p hactive
    have hcontra : False := by
      simp [base_inactive p] at hactive
    exact False.elim hcontra
  inactive_payload := by
    intro p _hinactive
    exact (payload p).2
  payload_hmatch := by
    intro p hp
    exact payload_valid.1 p hp
  payload_vmatch := by
    intro p hp
    exact payload_valid.2 p hp

/--
Variant of `ofInactivePayloadBox` whose payload box is still stated over the
instance tileset.  It is automatically lifted to the complete inactive payload
palette.
-/
def ofInactiveBox {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r : Nat}
    (base : BoxPattern S.tiles r)
    (base_valid : ValidBoxTiling S.tiles r base)
    (base_inactive : ∀ p : Box r, S.active (base p).1 = false)
    (payload : BoxPattern T r)
    (payload_valid : ValidBoxTiling T r payload) :
    CombinedBoxLayerPatch S T seed r :=
  ofInactivePayloadBox base base_valid base_inactive
    (fun p => ⟨(payload p).1, mem_completePayloads_of_mem (payload p).2⟩)
    (validBoxTiling_completePayloads_of_validBoxTiling payload_valid)

end CombinedBoxLayerPatch

/-- The translate of the centered integer box `[-r, r] × [-r, r]`. -/
def InTranslatedBox (r : Nat) (origin p : Int × Int) : Prop :=
  InBox r (p.1 - origin.1, p.2 - origin.2)

/-- Coordinates in an arbitrary translate of a centered integer box. -/
abbrev TranslatedBox (r : Nat) (origin : Int × Int) :=
  { p : Int × Int // InTranslatedBox r origin p }

/-- A finite assignment on an arbitrary translated box. -/
abbrev TranslatedBoxPattern (T : TileSet) (r : Nat) (origin : Int × Int) :=
  TranslatedBox r origin → TileIn T

/-- Restrict a plane tiling to one translated finite box. -/
def translatedBoxPatternOfPlane {T : TileSet} {r : Nat}
    (origin : Int × Int) (x : Int × Int → TileIn T) :
    TranslatedBoxPattern T r origin :=
  fun p => x p.1

/-- Validity of a finite translated box tiling. -/
def ValidTranslatedBoxTiling
    (T : TileSet) (r : Nat) (origin : Int × Int)
    (x : TranslatedBoxPattern T r origin) : Prop :=
  (∀ p : TranslatedBox r origin,
    ∀ hp : InTranslatedBox r origin (p.1.1 + 1, p.1.2),
      WangTile.HMatches (x p).1 (x ⟨(p.1.1 + 1, p.1.2), hp⟩).1) ∧
    (∀ p : TranslatedBox r origin,
      ∀ hp : InTranslatedBox r origin (p.1.1, p.1.2 + 1),
        WangTile.VMatches (x p).1 (x ⟨(p.1.1, p.1.2 + 1), hp⟩).1)

/-- A translated finite box inherited from a valid plane tiling is valid. -/
theorem validTranslatedBoxTiling_of_validPlaneTiling
    {T : TileSet} {r : Nat} {origin : Int × Int}
    {x : Int × Int → TileIn T}
    (hx : ValidPlaneTiling T x) :
    ValidTranslatedBoxTiling T r origin
      (translatedBoxPatternOfPlane origin x) := by
  constructor
  · intro p hp
    exact hx.1 p.1
  · intro p hp
    exact hx.2 p.1

/-- View a centered box pattern as a translated box pattern at origin `(0, 0)`. -/
def translatedBoxPatternOfBox {T : TileSet} {r : Nat}
    (x : BoxPattern T r) :
    TranslatedBoxPattern T r (0, 0) :=
  fun p => x ⟨p.1, by simpa [InTranslatedBox] using p.2⟩

/-- A valid centered box is a valid translated box at origin `(0, 0)`. -/
theorem validTranslatedBoxTiling_of_validBoxTiling
    {T : TileSet} {r : Nat} {x : BoxPattern T r}
    (hx : ValidBoxTiling T r x) :
    ValidTranslatedBoxTiling T r (0, 0)
      (translatedBoxPatternOfBox x) := by
  constructor
  · intro p hp
    simpa [translatedBoxPatternOfBox] using
      hx.1 ⟨p.1, by simpa [InTranslatedBox] using p.2⟩
        (by simpa [InTranslatedBox] using hp)
  · intro p hp
    simpa [translatedBoxPatternOfBox] using
      hx.2 ⟨p.1, by simpa [InTranslatedBox] using p.2⟩
        (by simpa [InTranslatedBox] using hp)

/--
Positive-radius centered finite boxes supply the translated valid-box interface
used by the Robinson-board scaffold route.
-/
theorem positiveTranslatedValidBoxes_of_tileableBoxes
    {T : TileSet}
    (hboxes : ∀ r : Nat, 0 < r → TileableBox T r) :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        ∃ base : TranslatedBoxPattern T r origin,
          ValidTranslatedBoxTiling T r origin base := by
  intro r hr
  rcases hboxes r hr with ⟨base, base_valid⟩
  exact ⟨(0, 0), translatedBoxPatternOfBox base,
    validTranslatedBoxTiling_of_validBoxTiling base_valid⟩

/-- Embed the centered box into its translate by `origin`. -/
def translatedBoxPoint {r : Nat} (origin : Int × Int) (p : Box r) :
    TranslatedBox r origin :=
  ⟨(origin.1 + p.1.1, origin.2 + p.1.2), by
    simpa [InTranslatedBox, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using p.2⟩

/--
Finite geometric witness for one arbitrary translate of a scaffold box.

Robinson boards naturally live at board-dependent coordinates.  This form lets
the construction stay in those coordinates and later recenter the witness for
the generic scaffold reduction.
-/
structure TranslatedActiveCornerIndexedBox
    (S : Scaffold) (r : Nat) (origin : Int × Int) where
  n : Nat
  hn : 0 < n
  base : TranslatedBoxPattern S.tiles r origin
  base_valid : ValidTranslatedBoxTiling S.tiles r origin base
  index : TranslatedBox r origin → Fin n × Fin n
  corner_index :
    ∀ p : TranslatedBox r origin, S.active (base p).1 = true →
      (base p).1 = S.corner →
        index p = (⟨0, hn⟩, ⟨0, hn⟩)
  active_hsucc :
    ∀ p : TranslatedBox r origin,
      ∀ hp : InTranslatedBox r origin (p.1.1 + 1, p.1.2),
        S.active (base p).1 = true →
          S.active (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1 = true →
            ∃ hi : (index p).1.val + 1 < n,
              index ⟨(p.1.1 + 1, p.1.2), hp⟩ =
                (⟨(index p).1.val + 1, hi⟩, (index p).2)
  active_vsucc :
    ∀ p : TranslatedBox r origin,
      ∀ hp : InTranslatedBox r origin (p.1.1, p.1.2 + 1),
        S.active (base p).1 = true →
          S.active (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1 = true →
            ∃ hj : (index p).2.val + 1 < n,
              index ⟨(p.1.1, p.1.2 + 1), hp⟩ =
                ((index p).1, ⟨(index p).2.val + 1, hj⟩)

namespace TranslatedActiveCornerIndexedBox

/--
Build a translated indexed box by restricting a valid scaffold plane tiling.

This is the form used by Robinson Section 7 board witnesses: the geometric
argument supplies a global scaffold tiling or board patch, plus an index map on
the free row/column product inside the selected translated box.
-/
def ofPlane {S : Scaffold} {r : Nat} {origin : Int × Int}
    (n : Nat) (hn : 0 < n)
    (x : Int × Int → TileIn S.tiles)
    (hx : ValidPlaneTiling S.tiles x)
    (index : TranslatedBox r origin → Fin n × Fin n)
    (corner_index :
      ∀ p : TranslatedBox r origin,
        S.active (x p.1).1 = true →
          (x p.1).1 = S.corner →
            index p = (⟨0, hn⟩, ⟨0, hn⟩))
    (active_hsucc :
      ∀ p : TranslatedBox r origin,
        ∀ hp : InTranslatedBox r origin (p.1.1 + 1, p.1.2),
          S.active (x p.1).1 = true →
            S.active (x (p.1.1 + 1, p.1.2)).1 = true →
              ∃ hi : (index p).1.val + 1 < n,
                index ⟨(p.1.1 + 1, p.1.2), hp⟩ =
                  (⟨(index p).1.val + 1, hi⟩, (index p).2))
    (active_vsucc :
      ∀ p : TranslatedBox r origin,
        ∀ hp : InTranslatedBox r origin (p.1.1, p.1.2 + 1),
          S.active (x p.1).1 = true →
            S.active (x (p.1.1, p.1.2 + 1)).1 = true →
              ∃ hj : (index p).2.val + 1 < n,
                index ⟨(p.1.1, p.1.2 + 1), hp⟩ =
                  ((index p).1, ⟨(index p).2.val + 1, hj⟩)) :
    TranslatedActiveCornerIndexedBox S r origin where
  n := n
  hn := hn
  base := translatedBoxPatternOfPlane origin x
  base_valid := validTranslatedBoxTiling_of_validPlaneTiling hx
  index := index
  corner_index := corner_index
  active_hsucc := active_hsucc
  active_vsucc := active_vsucc

/--
Build a translated indexed box when active scaffold cells are isolated inside
the translated box.

This is tailored to the Robinson-board route: once the concrete Figure 18/L2
data proves that no two selected active/corner sites can be adjacent in the
ambient scaffold, all successor obligations for the payload index become
vacuous.
-/
def ofNoAdjacentActive {S : Scaffold} {r : Nat} {origin : Int × Int}
    (base : TranslatedBoxPattern S.tiles r origin)
    (base_valid : ValidTranslatedBoxTiling S.tiles r origin base)
    (no_active_hsucc :
      ∀ p : TranslatedBox r origin,
        ∀ hp : InTranslatedBox r origin (p.1.1 + 1, p.1.2),
          S.active (base p).1 = true →
            S.active (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1 = true →
              False)
    (no_active_vsucc :
      ∀ p : TranslatedBox r origin,
        ∀ hp : InTranslatedBox r origin (p.1.1, p.1.2 + 1),
          S.active (base p).1 = true →
            S.active (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1 = true →
              False) :
    TranslatedActiveCornerIndexedBox S r origin where
  n := 1
  hn := by decide
  base := base
  base_valid := base_valid
  index := fun _ => (⟨0, by decide⟩, ⟨0, by decide⟩)
  corner_index := by
    intro p hactive hcorner
    rfl
  active_hsucc := by
    intro p hp hpActive hqActive
    exact False.elim (no_active_hsucc p hp hpActive hqActive)
  active_vsucc := by
    intro p hp hpActive hqActive
    exact False.elim (no_active_vsucc p hp hpActive hqActive)

theorem nonempty_of_noAdjacentActive {S : Scaffold} {r : Nat}
    {origin : Int × Int}
    {base : TranslatedBoxPattern S.tiles r origin}
    (base_valid : ValidTranslatedBoxTiling S.tiles r origin base)
    (no_active_hsucc :
      ∀ p : TranslatedBox r origin,
        ∀ hp : InTranslatedBox r origin (p.1.1 + 1, p.1.2),
          S.active (base p).1 = true →
            S.active (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1 = true →
              False)
    (no_active_vsucc :
      ∀ p : TranslatedBox r origin,
        ∀ hp : InTranslatedBox r origin (p.1.1, p.1.2 + 1),
          S.active (base p).1 = true →
            S.active (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1 = true →
              False) :
    Nonempty (TranslatedActiveCornerIndexedBox S r origin) :=
  ⟨ofNoAdjacentActive base base_valid no_active_hsucc no_active_vsucc⟩

/--
Positive-radius translated indexed boxes follow from positive-radius translated
boxes whose active cells are isolated.
-/
theorem positive_nonempty_of_noAdjacentActive
    {S : Scaffold}
    (hboxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern S.tiles r origin,
            ValidTranslatedBoxTiling S.tiles r origin base ∧
              (∀ p : TranslatedBox r origin,
                ∀ hp : InTranslatedBox r origin (p.1.1 + 1, p.1.2),
                  S.active (base p).1 = true →
                    S.active
                      (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1 = true →
                      False) ∧
              (∀ p : TranslatedBox r origin,
                ∀ hp : InTranslatedBox r origin (p.1.1, p.1.2 + 1),
                  S.active (base p).1 = true →
                    S.active
                      (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1 = true →
                      False)) :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox S r origin) := by
  intro r hr
  rcases hboxes r hr with
    ⟨origin, base, base_valid, no_active_hsucc, no_active_vsucc⟩
  exact ⟨origin,
    nonempty_of_noAdjacentActive base_valid
      no_active_hsucc no_active_vsucc⟩

theorem east_mem_centered {r : Nat} {origin : Int × Int}
    (p : Box r) (hp : InBox r (p.1.1 + 1, p.1.2)) :
    InTranslatedBox r origin
      ((translatedBoxPoint origin p).1.1 + 1,
        (translatedBoxPoint origin p).1.2) := by
  change InBox r
    (((origin.1 + p.1.1) + 1) - origin.1, (origin.2 + p.1.2) - origin.2)
  have hcoord :
      (((origin.1 + p.1.1) + 1) - origin.1, (origin.2 + p.1.2) - origin.2) =
        (p.1.1 + 1, p.1.2) := by
    apply Prod.ext <;> omega
  exact hcoord.symm ▸ hp

theorem north_mem_centered {r : Nat} {origin : Int × Int}
    (p : Box r) (hp : InBox r (p.1.1, p.1.2 + 1)) :
    InTranslatedBox r origin
      ((translatedBoxPoint origin p).1.1,
        (translatedBoxPoint origin p).1.2 + 1) := by
  change InBox r
    ((origin.1 + p.1.1) - origin.1, ((origin.2 + p.1.2) + 1) - origin.2)
  have hcoord :
      ((origin.1 + p.1.1) - origin.1, ((origin.2 + p.1.2) + 1) - origin.2) =
        (p.1.1, p.1.2 + 1) := by
    apply Prod.ext <;> omega
  exact hcoord.symm ▸ hp

theorem east_point_eq {r : Nat} {origin : Int × Int}
    (p : Box r) (hp : InBox r (p.1.1 + 1, p.1.2)) :
    (⟨((translatedBoxPoint origin p).1.1 + 1,
        (translatedBoxPoint origin p).1.2),
        east_mem_centered p hp⟩ : TranslatedBox r origin) =
      translatedBoxPoint origin ⟨(p.1.1 + 1, p.1.2), hp⟩ := by
  apply Subtype.ext
  simp [translatedBoxPoint]
  omega

theorem north_point_eq {r : Nat} {origin : Int × Int}
    (p : Box r) (hp : InBox r (p.1.1, p.1.2 + 1)) :
    (⟨((translatedBoxPoint origin p).1.1,
        (translatedBoxPoint origin p).1.2 + 1),
        north_mem_centered p hp⟩ : TranslatedBox r origin) =
      translatedBoxPoint origin ⟨(p.1.1, p.1.2 + 1), hp⟩ := by
  apply Subtype.ext
  simp [translatedBoxPoint]
  omega

end TranslatedActiveCornerIndexedBox

/--
Finite geometric witness for one centered box of a scaffold.

The witness gives a valid scaffold box together with an index map from active
cells into a nonempty fixed-corner square.  Adjacent active cells must map to
adjacent payload-square cells in the corresponding direction, so payload edge
matches are inherited from the supplied fixed-corner square.
-/
structure ActiveCornerIndexedBox (S : Scaffold) (r : Nat) where
  n : Nat
  hn : 0 < n
  base : BoxPattern S.tiles r
  base_valid : ValidBoxTiling S.tiles r base
  index : Box r → Fin n × Fin n
  corner_index :
    ∀ p : Box r, S.active (base p).1 = true →
      (base p).1 = S.corner →
        index p = (⟨0, hn⟩, ⟨0, hn⟩)
  active_hsucc :
    ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
      S.active (base p).1 = true →
        S.active (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1 = true →
          ∃ hi : (index p).1.val + 1 < n,
            index ⟨(p.1.1 + 1, p.1.2), hp⟩ =
              (⟨(index p).1.val + 1, hi⟩, (index p).2)
  active_vsucc :
    ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
      S.active (base p).1 = true →
        S.active (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1 = true →
          ∃ hj : (index p).2.val + 1 < n,
            index ⟨(p.1.1, p.1.2 + 1), hp⟩ =
              ((index p).1, ⟨(index p).2.val + 1, hj⟩)

namespace ActiveCornerIndexedBox

/--
Fill the indexed active cells of a finite scaffold box from a fixed-corner
payload square, then use the automatic inactive-payload absorber around them.
-/
def toCombinedBoxLayerPatch {S : Scaffold} {T : TileSet} {seed : WangTile}
    {r : Nat} (box : ActiveCornerIndexedBox S r)
    (square : TileableFixedCornerSquare T seed box.n) :
    CombinedBoxLayerPatch S T seed r :=
  CombinedBoxLayerPatch.ofActivePayloadFixedCornerSquare
    box.base box.base_valid square box.index
    box.corner_index
    (by
      intro p hp hpActive hqActive
      rcases box.active_hsucc p hp hpActive hqActive with ⟨hi, hindex⟩
      have hmatch :=
        square.choose_spec.choose_spec.1.2.1
          (box.index p).1 (box.index p).2 hi
      simpa [hindex] using hmatch)
    (by
      intro p hp hpActive hqActive
      rcases box.active_vsucc p hp hpActive hqActive with ⟨hj, hindex⟩
      have hmatch :=
        square.choose_spec.choose_spec.1.2.2
          (box.index p).1 (box.index p).2 hj
      simpa [hindex] using hmatch)

/-- The radius-zero indexed box whose only scaffold cell is the corner tile. -/
def singletonCorner {S : Scaffold} (hmem : S.corner ∈ S.tiles) :
    ActiveCornerIndexedBox S 0 where
  n := 1
  hn := by decide
  base := fun _ => ⟨S.corner, hmem⟩
  base_valid := by
    constructor
    · intro p hp
      exfalso
      have hp0 := p.2
      unfold InBox at hp hp0
      have hge : (0 : Int) ≤ (p : Int × Int).1 := by simpa using hp0.1
      have hle : (p : Int × Int).1 + 1 ≤ 0 := by simpa using hp.2.1
      linarith
    · intro p hp
      exfalso
      have hp0 := p.2
      unfold InBox at hp hp0
      have hge : (0 : Int) ≤ (p : Int × Int).2 := by simpa using hp0.2.2.1
      have hle : (p : Int × Int).2 + 1 ≤ 0 := by simpa using hp.2.2.2
      linarith
  index := fun _ => (⟨0, by decide⟩, ⟨0, by decide⟩)
  corner_index := by
    intro p hactive hcorner
    rfl
  active_hsucc := by
    intro p hp hpActive hqActive
    exfalso
    have hp0 := p.2
    unfold InBox at hp hp0
    have hge : (0 : Int) ≤ (p : Int × Int).1 := by simpa using hp0.1
    have hle : (p : Int × Int).1 + 1 ≤ 0 := by simpa using hp.2.1
    linarith
  active_vsucc := by
    intro p hp hpActive hqActive
    exfalso
    have hp0 := p.2
    unfold InBox at hp hp0
    have hge : (0 : Int) ≤ (p : Int × Int).2 := by simpa using hp0.2.2.1
    have hle : (p : Int × Int).2 + 1 ≤ 0 := by simpa using hp.2.2.2
    linarith

theorem nonempty_zero_of_corner_mem {S : Scaffold}
    (hmem : S.corner ∈ S.tiles) :
    Nonempty (ActiveCornerIndexedBox S 0) :=
  ⟨singletonCorner hmem⟩

/--
To build indexed boxes at every radius, it is enough to build them at positive
radii and know that the scaffold corner tile is part of the scaffold tileset.
-/
theorem nonempty_all_of_pos_and_corner_mem {S : Scaffold}
    (hmem : S.corner ∈ S.tiles)
    (hpos : ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox S r)) :
    ∀ r : Nat, Nonempty (ActiveCornerIndexedBox S r)
  | 0 => nonempty_zero_of_corner_mem hmem
  | r + 1 => hpos (r + 1) (Nat.succ_pos r)

end ActiveCornerIndexedBox

namespace TranslatedActiveCornerIndexedBox

/-- Recenter an arbitrary-origin indexed scaffold box at the origin. -/
def toActiveCornerIndexedBox {S : Scaffold} {r : Nat} {origin : Int × Int}
    (box : TranslatedActiveCornerIndexedBox S r origin) :
    ActiveCornerIndexedBox S r where
  n := box.n
  hn := box.hn
  base := fun p => box.base (translatedBoxPoint origin p)
  base_valid := by
    constructor
    · intro p hp
      have hq := east_point_eq (origin := origin) p hp
      simpa [hq] using
        box.base_valid.1 (translatedBoxPoint origin p)
          (east_mem_centered (origin := origin) p hp)
    · intro p hp
      have hq := north_point_eq (origin := origin) p hp
      simpa [hq] using
        box.base_valid.2 (translatedBoxPoint origin p)
          (north_mem_centered (origin := origin) p hp)
  index := fun p => box.index (translatedBoxPoint origin p)
  corner_index := by
    intro p hactive hcorner
    exact box.corner_index (translatedBoxPoint origin p) hactive hcorner
  active_hsucc := by
    intro p hp hpActive hqActive
    have hq := east_point_eq (origin := origin) p hp
    rcases box.active_hsucc (translatedBoxPoint origin p)
        (east_mem_centered (origin := origin) p hp) hpActive
        (by simpa [hq] using hqActive) with
      ⟨hi, hindex⟩
    exact ⟨hi, by simpa [hq] using hindex⟩
  active_vsucc := by
    intro p hp hpActive hqActive
    have hq := north_point_eq (origin := origin) p hp
    rcases box.active_vsucc (translatedBoxPoint origin p)
        (north_mem_centered (origin := origin) p hp) hpActive
        (by simpa [hq] using hqActive) with
      ⟨hj, hindex⟩
    exact ⟨hj, by simpa [hq] using hindex⟩

theorem nonempty_centered_of_translated {S : Scaffold} {r : Nat}
    {origin : Int × Int}
    (hbox : Nonempty (TranslatedActiveCornerIndexedBox S r origin)) :
    Nonempty (ActiveCornerIndexedBox S r) := by
  rcases hbox with ⟨box⟩
  exact ⟨box.toActiveCornerIndexedBox⟩

theorem nonempty_centered_pos_of_translated_pos {S : Scaffold}
    (hboxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox S r origin)) :
    ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox S r) := by
  intro r hr
  rcases hboxes r hr with ⟨origin, hbox⟩
  exact nonempty_centered_of_translated (origin := origin) hbox

end TranslatedActiveCornerIndexedBox

theorem payload_mem_of_product_corner_mem_combineWithScaffold {S : Scaffold}
    {T : TileSet} {seed payload : WangTile}
    (hactive : S.active S.corner = true)
    (htile : WangTile.product S.corner payload ∈ combineWithScaffold S T seed) :
    payload ∈ T := by
  rcases mem_combineWithScaffold_iff.1 htile with ⟨b, _hb, p, hactiveMem, _hinactive, hproduct⟩
  have hparts : b = S.corner ∧ p = payload := product_eq_iff.1 hproduct
  simpa [hparts.2] using (hactiveMem (by simpa [hparts.1] using hactive)).1

theorem payload_eq_seed_of_product_corner_mem_combineWithScaffold {S : Scaffold}
    {T : TileSet} {seed payload : WangTile}
    (hactive : S.active S.corner = true)
    (htile : WangTile.product S.corner payload ∈ combineWithScaffold S T seed) :
    payload = seed := by
  rcases mem_combineWithScaffold_iff.1 htile with ⟨b, _hb, p, hactiveMem, _hinactive, hproduct⟩
  have hparts : b = S.corner ∧ p = payload := product_eq_iff.1 hproduct
  exact hparts.2.symm.trans ((hactiveMem (by simpa [hparts.1] using hactive)).2 hparts.1)

theorem payload_mem_of_active_product_mem_combineWithScaffold {S : Scaffold}
    {T : TileSet} {seed base payload : WangTile}
    (hactive : S.active base = true)
    (htile : WangTile.product base payload ∈ combineWithScaffold S T seed) :
    payload ∈ T := by
  rcases mem_combineWithScaffold_iff.1 htile with ⟨b, _hb, p, hactiveMem, _hinactive, hproduct⟩
  have hparts : b = base ∧ p = payload := product_eq_iff.1 hproduct
  simpa [hparts.2] using (hactiveMem (by simpa [hparts.1] using hactive)).1

theorem payload_eq_seed_of_active_corner_product_mem_combineWithScaffold {S : Scaffold}
    {T : TileSet} {seed base payload : WangTile}
    (hactive : S.active base = true) (hcorner : base = S.corner)
    (htile : WangTile.product base payload ∈ combineWithScaffold S T seed) :
    payload = seed := by
  rcases mem_combineWithScaffold_iff.1 htile with ⟨b, _hb, p, hactiveMem, _hinactive, hproduct⟩
  have hparts : b = base ∧ p = payload := product_eq_iff.1 hproduct
  exact hparts.2.symm.trans
    ((hactiveMem (by simpa [hparts.1] using hactive)).2 (hparts.1.trans hcorner))

theorem tilesPlane_scaffold_of_tilesPlane_combineWithScaffold {S : Scaffold}
    {T : TileSet} {seed : WangTile}
    (h : TilesPlane (combineWithScaffold S T seed)) :
    TilesPlane S.tiles := by
  classical
  rcases h with ⟨x, hx⟩
  have hdecode : ∀ p : Int × Int,
      ∃ b : TileIn S.tiles, ∃ payload : WangTile,
        WangTile.product b.1 payload = (x p).1 := by
    intro p
    rcases mem_combineWithScaffold_iff.1 (x p).2 with
      ⟨b, hb, payload, _hactiveMem, _hinactive, htile⟩
    exact ⟨⟨b, hb⟩, payload, htile⟩
  let baseAt : Int × Int → TileIn S.tiles := fun p => Classical.choose (hdecode p)
  let payloadAt : Int × Int → WangTile := fun p =>
    Classical.choose (Classical.choose_spec (hdecode p))
  have hproduct : ∀ p : Int × Int,
      WangTile.product (baseAt p).1 (payloadAt p) = (x p).1 := by
    intro p
    exact Classical.choose_spec (Classical.choose_spec (hdecode p))
  refine ⟨baseAt, ?_⟩
  constructor
  · intro p
    have hmatch : WangTile.HMatches
        (WangTile.product (baseAt p).1 (payloadAt p))
        (WangTile.product (baseAt (p.1 + 1, p.2)).1 (payloadAt (p.1 + 1, p.2))) := by
      simpa [hproduct p, hproduct (p.1 + 1, p.2)] using hx.1 p
    exact (WangTile.HMatches_product_iff
      (baseAt p).1 (payloadAt p)
      (baseAt (p.1 + 1, p.2)).1 (payloadAt (p.1 + 1, p.2))).1 hmatch |>.1
  · intro p
    have hmatch : WangTile.VMatches
        (WangTile.product (baseAt p).1 (payloadAt p))
        (WangTile.product (baseAt (p.1, p.2 + 1)).1 (payloadAt (p.1, p.2 + 1))) := by
      simpa [hproduct p, hproduct (p.1, p.2 + 1)] using hx.2 p
    exact (WangTile.VMatches_product_iff
      (baseAt p).1 (payloadAt p)
      (baseAt (p.1, p.2 + 1)).1 (payloadAt (p.1, p.2 + 1))).1 hmatch |>.1

/-- Decoded layers of a finite rectangle over a scaffold-combined tileset. -/
def ValidCombinedRectangleLayers (S : Scaffold) (T : TileSet) (seed : WangTile)
    {w h : Nat} (rect baseRect payloadRect : Rectangle w h) : Prop :=
  ValidRectangle S.tiles baseRect ∧
    (∀ i : Fin w, ∀ j : Fin h,
      WangTile.product (baseRect i j) (payloadRect i j) = rect i j) ∧
    (∀ i : Fin w, ∀ j : Fin h,
      S.active (baseRect i j) = true →
        payloadRect i j ∈ T ∧ (baseRect i j = S.corner → payloadRect i j = seed)) ∧
    (∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
      WangTile.HMatches (payloadRect i j) (payloadRect ⟨i.val + 1, hi⟩ j)) ∧
    (∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
      WangTile.VMatches (payloadRect i j) (payloadRect i ⟨j.val + 1, hj⟩))

theorem exists_validCombinedRectangleLayers_of_validRectangle_combineWithScaffold
    {S : Scaffold} {T : TileSet} {seed : WangTile}
    {w h : Nat} {rect : Rectangle w h}
    (hrect : ValidRectangle (combineWithScaffold S T seed) rect) :
    ∃ baseRect payloadRect : Rectangle w h,
      ValidCombinedRectangleLayers S T seed rect baseRect payloadRect := by
  classical
  have hdecode : ∀ i : Fin w, ∀ j : Fin h,
      ∃ b : TileIn S.tiles, ∃ payload : WangTile,
        (S.active b.1 = true →
          payload ∈ T ∧ (b.1 = S.corner → payload = seed)) ∧
          WangTile.product b.1 payload = rect i j := by
    intro i j
    rcases mem_combineWithScaffold_iff.1 (hrect.1 i j) with
      ⟨b, hb, payload, hactiveMem, _hinactive, htile⟩
    exact ⟨⟨b, hb⟩, payload, hactiveMem, htile⟩
  let baseAt : Fin w → Fin h → TileIn S.tiles := fun i j => Classical.choose (hdecode i j)
  let payloadAt : Rectangle w h := fun i j =>
    Classical.choose (Classical.choose_spec (hdecode i j))
  have hactiveMem : ∀ i : Fin w, ∀ j : Fin h,
      S.active (baseAt i j).1 = true →
        payloadAt i j ∈ T ∧ ((baseAt i j).1 = S.corner → payloadAt i j = seed) := by
    intro i j
    exact (Classical.choose_spec (Classical.choose_spec (hdecode i j))).1
  have hproduct : ∀ i : Fin w, ∀ j : Fin h,
      WangTile.product (baseAt i j).1 (payloadAt i j) = rect i j := by
    intro i j
    exact (Classical.choose_spec (Classical.choose_spec (hdecode i j))).2
  refine ⟨fun i j => (baseAt i j).1, payloadAt, ?_⟩
  unfold ValidCombinedRectangleLayers
  constructor
  · constructor
    · intro i j
      exact (baseAt i j).2
    constructor
    · intro i j hi
      have hmatch : WangTile.HMatches
          (WangTile.product (baseAt i j).1 (payloadAt i j))
          (WangTile.product (baseAt ⟨i.val + 1, hi⟩ j).1
            (payloadAt ⟨i.val + 1, hi⟩ j)) := by
        simpa [hproduct i j, hproduct ⟨i.val + 1, hi⟩ j] using hrect.2.1 i j hi
      exact (WangTile.HMatches_product_iff
        (baseAt i j).1 (payloadAt i j)
        (baseAt ⟨i.val + 1, hi⟩ j).1 (payloadAt ⟨i.val + 1, hi⟩ j)).1 hmatch |>.1
    · intro i j hj
      have hmatch : WangTile.VMatches
          (WangTile.product (baseAt i j).1 (payloadAt i j))
          (WangTile.product (baseAt i ⟨j.val + 1, hj⟩).1
            (payloadAt i ⟨j.val + 1, hj⟩)) := by
        simpa [hproduct i j, hproduct i ⟨j.val + 1, hj⟩] using hrect.2.2 i j hj
      exact (WangTile.VMatches_product_iff
        (baseAt i j).1 (payloadAt i j)
        (baseAt i ⟨j.val + 1, hj⟩).1 (payloadAt i ⟨j.val + 1, hj⟩)).1 hmatch |>.1
  constructor
  · intro i j
    exact hproduct i j
  constructor
  · intro i j
    exact hactiveMem i j
  constructor
  · intro i j hi
    have hmatch : WangTile.HMatches
        (WangTile.product (baseAt i j).1 (payloadAt i j))
        (WangTile.product (baseAt ⟨i.val + 1, hi⟩ j).1
          (payloadAt ⟨i.val + 1, hi⟩ j)) := by
      simpa [hproduct i j, hproduct ⟨i.val + 1, hi⟩ j] using hrect.2.1 i j hi
    exact (WangTile.HMatches_product_iff
      (baseAt i j).1 (payloadAt i j)
      (baseAt ⟨i.val + 1, hi⟩ j).1 (payloadAt ⟨i.val + 1, hi⟩ j)).1 hmatch |>.2
  · intro i j hj
    have hmatch : WangTile.VMatches
        (WangTile.product (baseAt i j).1 (payloadAt i j))
        (WangTile.product (baseAt i ⟨j.val + 1, hj⟩).1
          (payloadAt i ⟨j.val + 1, hj⟩)) := by
      simpa [hproduct i j, hproduct i ⟨j.val + 1, hj⟩] using hrect.2.2 i j hj
    exact (WangTile.VMatches_product_iff
      (baseAt i j).1 (payloadAt i j)
      (baseAt i ⟨j.val + 1, hj⟩).1 (payloadAt i ⟨j.val + 1, hj⟩)).1 hmatch |>.2

theorem validRectangle_payload_of_validCombinedRectangleLayers_of_active
    {S : Scaffold} {T : TileSet} {seed : WangTile}
    {w h : Nat} {rect baseRect payloadRect : Rectangle w h}
    (hlayers : ValidCombinedRectangleLayers S T seed rect baseRect payloadRect)
    (hactive : ∀ i : Fin w, ∀ j : Fin h, S.active (baseRect i j) = true) :
    ValidRectangle T payloadRect := by
  constructor
  · intro i j
    exact (hlayers.2.2.1 i j (hactive i j)).1
  constructor
  · intro i j hi
    exact hlayers.2.2.2.1 i j hi
  · intro i j hj
    exact hlayers.2.2.2.2 i j hj

theorem tileableFixedCornerSquare_payload_of_validCombinedRectangleLayers_of_active_corner
    {S : Scaffold} {T : TileSet} {seed : WangTile}
    {n : Nat} {rect baseRect payloadRect : Rectangle n n}
    (hn : 0 < n)
    (hlayers : ValidCombinedRectangleLayers S T seed rect baseRect payloadRect)
    (hactive : ∀ i : Fin n, ∀ j : Fin n, S.active (baseRect i j) = true)
    (hcorner : baseRect ⟨0, hn⟩ ⟨0, hn⟩ = S.corner) :
    TileableFixedCornerSquare T seed n := by
  refine ⟨hn, payloadRect, ?_, ?_⟩
  · exact validRectangle_payload_of_validCombinedRectangleLayers_of_active hlayers hactive
  · exact (hlayers.2.2.1 ⟨0, hn⟩ ⟨0, hn⟩ (hactive ⟨0, hn⟩ ⟨0, hn⟩)).2 hcorner

def PlaneTilingHasActiveCornerBaseWindows (S : Scaffold) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold S T seed)),
    ValidPlaneTiling (combineWithScaffold S T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ origin : Int × Int, ∃ baseRect : Rectangle n n,
          (∀ i : Fin n, ∀ j : Fin n, S.active (baseRect i j) = true) ∧
            baseRect ⟨0, hn⟩ ⟨0, hn⟩ = S.corner ∧
            ∀ i : Fin n, ∀ j : Fin n, ∃ payload : WangTile,
              WangTile.product (baseRect i j) payload =
                (x (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val)).1

def PlaneTilingForcesActiveCornerWindows (S : Scaffold) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold S T seed)),
    ValidPlaneTiling (combineWithScaffold S T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ rect baseRect payloadRect : Rectangle n n,
          ValidCombinedRectangleLayers S T seed rect baseRect payloadRect ∧
            (∀ i : Fin n, ∀ j : Fin n, S.active (baseRect i j) = true) ∧
            baseRect ⟨0, hn⟩ ⟨0, hn⟩ = S.corner

theorem planeTilingForcesActiveCornerWindows_of_hasActiveCornerBaseWindows
    {S : Scaffold} (hS : PlaneTilingHasActiveCornerBaseWindows S) :
    PlaneTilingForcesActiveCornerWindows S := by
  intro T seed x hx n hn
  rcases hS x hx n hn with ⟨origin, forcedBase, hforcedActive, hforcedCorner, hforcedProduct⟩
  let rect : Rectangle n n := fun i j =>
    (x (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val)).1
  have hrect : ValidRectangle (combineWithScaffold S T seed) rect := by
    constructor
    · intro i j
      exact (x (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val)).2
    constructor
    · intro i j hi
      convert hx.1 (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val) using 2
      ext
      all_goals simp [Nat.cast_add, add_assoc]
    · intro i j hj
      convert hx.2 (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val) using 2
      ext
      all_goals simp [Nat.cast_add, add_assoc]
  rcases exists_validCombinedRectangleLayers_of_validRectangle_combineWithScaffold
      (S := S) (T := T) (seed := seed) hrect with
    ⟨baseRect, payloadRect, hlayers⟩
  refine ⟨rect, baseRect, payloadRect, hlayers, ?_, ?_⟩
  · intro i j
    rcases hforcedProduct i j with ⟨payload, hproduct⟩
    have hbase : baseRect i j = forcedBase i j := by
      exact (product_eq_iff.1 ((hlayers.2.1 i j).trans hproduct.symm)).1
    simpa [hbase] using hforcedActive i j
  · rcases hforcedProduct ⟨0, hn⟩ ⟨0, hn⟩ with ⟨payload, hproduct⟩
    have hbase : baseRect ⟨0, hn⟩ ⟨0, hn⟩ = forcedBase ⟨0, hn⟩ ⟨0, hn⟩ := by
      exact (product_eq_iff.1 ((hlayers.2.1 ⟨0, hn⟩ ⟨0, hn⟩).trans hproduct.symm)).1
    exact hbase.trans hforcedCorner

def ForcesActiveCornerSquares (S : Scaffold) : Prop :=
  ∀ {T : TileSet} {seed : WangTile},
    TilesPlane (combineWithScaffold S T seed) →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ rect baseRect payloadRect : Rectangle n n,
          ValidCombinedRectangleLayers S T seed rect baseRect payloadRect ∧
            (∀ i : Fin n, ∀ j : Fin n, S.active (baseRect i j) = true) ∧
            baseRect ⟨0, hn⟩ ⟨0, hn⟩ = S.corner

theorem forcesActiveCornerSquares_of_planeTilingForcesActiveCornerWindows
    {S : Scaffold} (hS : PlaneTilingForcesActiveCornerWindows S) :
    ForcesActiveCornerSquares S := by
  intro T seed htiles n hn
  rcases htiles with ⟨x, hx⟩
  exact hS x hx n hn

def RealizesActiveCornerSquares (S : Scaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    (∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n) →
      TilesPlane (combineWithScaffold S T seed)

/--
Finite-box form of the backward scaffold construction.

Robinson's Section 7 argument builds larger and larger finite board patches by
placing the supplied fixed-corner payload squares into the free rows and
columns.  Once every centered box of the combined scaffold tileset is tileable,
the existing Wang compactness theorem produces a full plane tiling.
-/
def RealizesActiveCornerBoxes (S : Scaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    (∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n) →
      ∀ r : Nat, TileableBox (combineWithScaffold S T seed) r

/--
Patch-witness form of `RealizesActiveCornerBoxes`.

This is the concrete target for the backward Robinson construction: given
arbitrarily large fixed-corner payload squares, build a base/payload patch over
each requested centered box of the combined scaffold tileset.
-/
def HasActiveCornerBoxPatches (S : Scaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    (∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n) →
      ∀ r : Nat, Nonempty (CombinedBoxPatch S T seed r)

/--
Layered patch-witness form of `RealizesActiveCornerBoxes`.

This is the intended finite target for the Robinson board construction: build a
valid finite scaffold box and a compatible payload labelling over it, then let
the generic product construction assemble the combined box patch.
-/
def HasActiveCornerLayerBoxPatches (S : Scaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    (∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n) →
      ∀ r : Nat, Nonempty (CombinedBoxLayerPatch S T seed r)

/--
Turn a purely scaffold-geometric indexed-box construction into the layered
patch realization invariant by filling active cells from the available
fixed-corner payload square.
-/
theorem activeCornerLayerBoxPatches_of_activeCornerIndexedBoxes
    {S : Scaffold}
    (hboxes : ∀ r : Nat, Nonempty (ActiveCornerIndexedBox S r)) :
    HasActiveCornerLayerBoxPatches S := by
  intro T seed hsquares r
  rcases hboxes r with ⟨box⟩
  exact ⟨box.toCombinedBoxLayerPatch (hsquares box.n box.hn)⟩

/--
For the layered patch invariant, it is enough to construct indexed boxes at
positive radii and know that the scaffold corner belongs to the scaffold
tileset.  The radius-zero patch is then the singleton corner box.
-/
theorem activeCornerLayerBoxPatches_of_positiveActiveCornerIndexedBoxes
    {S : Scaffold}
    (hmem : S.corner ∈ S.tiles)
    (hboxes_pos : ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox S r)) :
    HasActiveCornerLayerBoxPatches S :=
  activeCornerLayerBoxPatches_of_activeCornerIndexedBoxes
    (ActiveCornerIndexedBox.nonempty_all_of_pos_and_corner_mem hmem hboxes_pos)

theorem activeCornerBoxPatches_of_layerBoxPatches
    {S : Scaffold} (hpatches : HasActiveCornerLayerBoxPatches S) :
    HasActiveCornerBoxPatches S := by
  intro T seed hsquares r
  rcases hpatches T seed hsquares r with ⟨patch⟩
  exact ⟨patch.toCombinedBoxPatch⟩

theorem realizesActiveCornerBoxes_of_activeCornerBoxPatches
    {S : Scaffold} (hpatches : HasActiveCornerBoxPatches S) :
    RealizesActiveCornerBoxes S := by
  intro T seed hsquares r
  rcases hpatches T seed hsquares r with ⟨patch⟩
  exact patch.tileableBox

theorem realizesActiveCornerBoxes_of_activeCornerLayerBoxPatches
    {S : Scaffold} (hpatches : HasActiveCornerLayerBoxPatches S) :
    RealizesActiveCornerBoxes S :=
  realizesActiveCornerBoxes_of_activeCornerBoxPatches
    (activeCornerBoxPatches_of_layerBoxPatches hpatches)

theorem realizesActiveCornerSquares_of_realizesActiveCornerBoxes
    {S : Scaffold} (hboxes : RealizesActiveCornerBoxes S) :
    RealizesActiveCornerSquares S := by
  intro T seed hsquares
  exact tilesPlane_of_all_tileableBoxes (hboxes T seed hsquares)

theorem realizesActiveCornerSquares_of_activeCornerLayerBoxPatches
    {S : Scaffold} (hpatches : HasActiveCornerLayerBoxPatches S) :
    RealizesActiveCornerSquares S :=
  realizesActiveCornerSquares_of_realizesActiveCornerBoxes
    (realizesActiveCornerBoxes_of_activeCornerLayerBoxPatches hpatches)

/--
Forward half of the scaffold reduction, stated directly at the payload-square
level.

This is more flexible than `ForcesActiveCornerSquares`: a concrete scaffold may
route payload adjacencies through channels or other non-contiguous geometry, as
in the Robinson/Ollinger free-subsquare construction, without first exposing a
literal contiguous active block of scaffold cells.
-/
def ForcesFixedCornerSquares (S : Scaffold) : Prop :=
  ∀ {T : TileSet} {seed : WangTile},
    TilesPlane (combineWithScaffold S T seed) →
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n

theorem all_fixedCornerSquares_of_tilesPlane_combineWithScaffold
    {S : Scaffold} (hS : ForcesActiveCornerSquares S)
    {T : TileSet} {seed : WangTile}
    (h : TilesPlane (combineWithScaffold S T seed)) :
    ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n := by
  intro n hn
  rcases hS h n hn with ⟨rect, baseRect, payloadRect, hlayers, hactive, hcorner⟩
  exact tileableFixedCornerSquare_payload_of_validCombinedRectangleLayers_of_active_corner
    hn hlayers hactive hcorner

theorem forcesFixedCornerSquares_of_forcesActiveCornerSquares
    {S : Scaffold} (hS : ForcesActiveCornerSquares S) :
    ForcesFixedCornerSquares S := by
  intro T seed htiles n hn
  exact all_fixedCornerSquares_of_tilesPlane_combineWithScaffold hS htiles n hn

theorem combineWithScaffold_primrec (S : Scaffold) :
    Primrec (fun p : TileSet × WangTile => combineWithScaffold S p.1 p.2) := by
  classical
  unfold combineWithScaffold
  refine Primrec.list_flatMap (Primrec.const S.tiles) ?_
  apply Primrec₂.mk
  have hpayload : Primrec fun a : (TileSet × WangTile) × WangTile =>
      scaffoldPayloads S a.1.1 a.1.2 a.2 := by
    unfold scaffoldPayloads
    have hactive : Primrec fun a : (TileSet × WangTile) × WangTile => S.active a.2 :=
      S.active_primrec.comp Primrec.snd
    refine Primrec.ite (Primrec.eq.comp hactive (Primrec.const true)) ?_
      (completePayloads_primrec.comp (Primrec.fst.comp Primrec.fst))
    refine Primrec.ite ?_ ?_ ?_
    · exact Primrec.eq.comp Primrec.snd (Primrec.const S.corner)
    · exact (PrimrecRel.listFilter (R := fun p seed : WangTile => p = seed) Primrec.eq).comp
        (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    · exact Primrec.fst.comp Primrec.fst
  refine Primrec.list_map hpayload ?_
  rw [← Primrec₂.uncurry]
  exact WangTile.product_primrec.comp
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem combineWithScaffold_computable (S : Scaffold) :
    Computable (fun p : TileSet × WangTile => combineWithScaffold S p.1 p.2) :=
  (combineWithScaffold_primrec S).to_comp

/-- The abstract property required of a scaffold for the Berger/Robinson reduction. -/
def IsScaffold (S : Scaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    TilesPlane (combineWithScaffold S T seed) ↔
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n

theorem isScaffold_of_realizesActiveCornerSquares_of_forcesFixedCornerSquares
    {S : Scaffold}
    (hrealizes : RealizesActiveCornerSquares S)
    (hforces : ForcesFixedCornerSquares S) :
    IsScaffold S := by
  intro T seed
  constructor
  · intro htiles
    exact hforces htiles
  · intro hsquares
    exact hrealizes T seed hsquares

theorem isScaffold_of_realizesActiveCornerSquares_of_forcesActiveCornerSquares
    {S : Scaffold}
    (hrealizes : RealizesActiveCornerSquares S)
    (hforces : ForcesActiveCornerSquares S) :
    IsScaffold S := by
  exact isScaffold_of_realizesActiveCornerSquares_of_forcesFixedCornerSquares
    hrealizes (forcesFixedCornerSquares_of_forcesActiveCornerSquares hforces)

theorem isScaffold_of_realizesActiveCornerBoxes_of_forcesFixedCornerSquares
    {S : Scaffold}
    (hrealizes : RealizesActiveCornerBoxes S)
    (hforces : ForcesFixedCornerSquares S) :
    IsScaffold S := by
  exact isScaffold_of_realizesActiveCornerSquares_of_forcesFixedCornerSquares
    (realizesActiveCornerSquares_of_realizesActiveCornerBoxes hrealizes)
    hforces

theorem isScaffold_of_realizesActiveCornerBoxes_of_forcesActiveCornerSquares
    {S : Scaffold}
    (hrealizes : RealizesActiveCornerBoxes S)
    (hforces : ForcesActiveCornerSquares S) :
    IsScaffold S := by
  exact isScaffold_of_realizesActiveCornerBoxes_of_forcesFixedCornerSquares
    hrealizes (forcesFixedCornerSquares_of_forcesActiveCornerSquares hforces)

theorem isScaffold_of_activeCornerLayerBoxPatches_of_forcesFixedCornerSquares
    {S : Scaffold}
    (hpatches : HasActiveCornerLayerBoxPatches S)
    (hforces : ForcesFixedCornerSquares S) :
    IsScaffold S :=
  isScaffold_of_realizesActiveCornerSquares_of_forcesFixedCornerSquares
    (realizesActiveCornerSquares_of_activeCornerLayerBoxPatches hpatches)
    hforces

theorem isScaffold_of_activeCornerLayerBoxPatches_of_forcesActiveCornerSquares
    {S : Scaffold}
    (hpatches : HasActiveCornerLayerBoxPatches S)
    (hforces : ForcesActiveCornerSquares S) :
    IsScaffold S :=
  isScaffold_of_activeCornerLayerBoxPatches_of_forcesFixedCornerSquares
    hpatches (forcesFixedCornerSquares_of_forcesActiveCornerSquares hforces)

/-- The empty scaffold example; useful only as a minimal data sanity check. -/
def emptyScaffoldExample : Scaffold where
  tiles := []
  active := fun t => decide (t = monochromeTile)
  corner := monochromeTile
  active_primrec :=
    Primrec.eq.decide.comp Primrec.id (Primrec.const monochromeTile)

/-- Abstract scaffold reduction from fixed-corner squares to ordinary plane tiling. -/
theorem scaffold_reduction_correct {S : Scaffold} (hS : IsScaffold S)
    (T : TileSet) (seed : WangTile) :
    TilesPlane (combineWithScaffold S T seed) ↔
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n :=
  hS T seed

end LeanWang

end
