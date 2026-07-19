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

/--
All payload tiles whose edge colors come from a finite color palette.

Inactive scaffold cells use this complete palette, so they can absorb arbitrary
instance-tile edge colors while still keeping the combined tileset finite.
-/
def completePayloadsFromColors (colors : List Nat) : TileSet :=
  ((colors.product colors).product (colors.product colors)).map fun colors =>
    { n := colors.1.1, s := colors.1.2,
      e := colors.2.1, w := colors.2.2 }

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

theorem mk_mem_completePayloadsFromColors {colors : List Nat}
    {n s e w : Nat}
    (hn : n ∈ colors) (hs : s ∈ colors)
    (he : e ∈ colors) (hw : w ∈ colors) :
    ({ n := n, s := s, e := e, w := w } : WangTile) ∈
      completePayloadsFromColors colors := by
  unfold completePayloadsFromColors
  apply List.mem_map.2
  exact ⟨((n, s), (e, w)), by simp [hn, hs, he, hw], rfl⟩

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

private theorem listProduct_primrec {α β γ : Type*}
    [Primcodable α] [Primcodable β] [Primcodable γ]
    {left : α → List β} {right : α → List γ}
    (hleft : Primrec left) (hright : Primrec right) :
    Primrec fun input => (left input).product (right input) := by
  unfold List.product
  refine Primrec.list_flatMap hleft (Primrec₂.mk ?_)
  refine Primrec.list_map (hright.comp Primrec.fst) ?_
  exact Primrec₂.pair.comp₂
    (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right

theorem completePayloadsFromColors_primrec : Primrec completePayloadsFromColors := by
  unfold completePayloadsFromColors
  have hpairs : Primrec fun colors : List Nat => colors.product colors :=
    listProduct_primrec Primrec.id Primrec.id
  have hquadruples : Primrec fun colors : List Nat =>
      (colors.product colors).product (colors.product colors) :=
    listProduct_primrec hpairs hpairs
  have htuple : Primrec fun colors : (Nat × Nat) × (Nat × Nat) =>
      (colors.1.1, colors.1.2, colors.2.1, colors.2.2) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)))
  refine Primrec.list_map hquadruples (Primrec₂.mk ?_)
  exact (WangTile.ofTuple_primrec.comp htuple).comp Primrec.snd

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
