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

This file collects the generic tiling theorems used by the reductions:
machine-tile correctness, fixed-corner-square compactness, and the abstract
scaffold construction. The partial-recursive-code reduction is kept in
`TM0FoldedReduction`, so this file does not expose a separate machine-side
reduction interface.
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

/--
Payload symbols carried by a scaffold tile. Active scaffold cells carry the
instance tileset, with the marked corner restricted to the requested seed.
Inactive scaffold cells carry one dummy payload tile, so they do not force the
instance tileset outside the free regions.
-/
def scaffoldPayloads (S : Scaffold) (T : TileSet) (seed b : WangTile) : TileSet :=
  if S.active b then
    if b = S.corner then T.filter fun p => p = seed else T
  else
    [monochromeTile]

/-- Combine a scaffold with a fixed-corner square instance. -/
def combineWithScaffold (S : Scaffold) (T : TileSet) (seed : WangTile) : TileSet :=
  S.tiles.flatMap fun b =>
    (scaffoldPayloads S T seed b).map fun p => WangTile.product b p

theorem mem_combineWithScaffold_iff {S : Scaffold} {T : TileSet}
    {seed tile : WangTile} :
    tile ∈ combineWithScaffold S T seed ↔
      ∃ b ∈ S.tiles, ∃ p : WangTile,
        (S.active b = true → p ∈ T ∧ (b = S.corner → p = seed)) ∧
          (S.active b = false → p = monochromeTile) ∧
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
        have hinactive : S.active b = false → p = monochromeTile := by
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
        have hinactive : S.active b = false → p = monochromeTile := by
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
      rw [List.mem_singleton] at hp
      refine ⟨b, hb, p, ?_⟩
      have hmem : S.active b = true → p ∈ T ∧ (b = S.corner → p = seed) := by
        intro htrue
        rw [hfalse] at htrue
        nomatch htrue
      have hinactive : S.active b = false → p = monochromeTile := by
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
      exact ⟨p, by rw [List.mem_singleton]; exact hinactive (by
        cases h : S.active b
        · rfl
        · exact False.elim (hactive h)), htile⟩

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
      (Primrec.const ([monochromeTile] : TileSet))
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
