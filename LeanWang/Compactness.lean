/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Continuous
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic.Linarith

/-!
Compactness arguments for Wang tilings.

The main result here is centered-box compactness: a finite tileset tiles every
centered box if and only if it tiles the whole plane.
-/

namespace LeanWang

instance instDecidableInBox (r : Nat) (p : Int × Int) : Decidable (InBox r p) := by
  unfold InBox
  infer_instance

instance instTopologicalSpaceTileIn (T : TileSet) : TopologicalSpace (TileIn T) :=
  ⊥

instance instDiscreteTopologyTileIn (T : TileSet) : DiscreteTopology (TileIn T) :=
  discreteTopology_bot _

instance instCompactSpaceTileIn (T : TileSet) : CompactSpace (TileIn T) :=
  Finite.compactSpace

/-- Global assignments of tiles from a fixed tileset, without adjacency constraints. -/
abbrev GlobalAssignment (T : TileSet) :=
  Int × Int → TileIn T

/-- A global assignment whose restriction to `Box r` is a valid box tiling. -/
def BoxCylinder (T : TileSet) (r : Nat) : Set (GlobalAssignment T) :=
  {x | ValidBoxTiling T r (fun p => x p.1)}

theorem inBox_mono {r s : Nat} (h : r ≤ s) {p : Int × Int} :
    InBox r p → InBox s p := by
  intro hp
  rcases hp with ⟨hx0, hx1, hy0, hy1⟩
  have hrs : (r : Int) ≤ (s : Int) := by exact_mod_cast h
  exact ⟨(neg_le_neg hrs).trans hx0, hx1.trans hrs,
    (neg_le_neg hrs).trans hy0, hy1.trans hrs⟩

theorem inBox_of_natAbs_le {r : Nat} {p : Int × Int}
    (hx : p.1.natAbs ≤ r) (hy : p.2.natAbs ≤ r) : InBox r p := by
  unfold InBox
  have hx' : ((p.1.natAbs : Nat) : Int) ≤ (r : Int) := by exact_mod_cast hx
  have hy' : ((p.2.natAbs : Nat) : Int) ≤ (r : Int) := by exact_mod_cast hy
  have hxlow : -(((p.1.natAbs : Nat) : Int)) ≤ p.1 := by
    simpa [Int.natCast_natAbs] using neg_abs_le p.1
  have hxhigh : p.1 ≤ ((p.1.natAbs : Nat) : Int) := by
    simpa [Int.natCast_natAbs] using le_abs_self p.1
  have hylow : -(((p.2.natAbs : Nat) : Int)) ≤ p.2 := by
    simpa [Int.natCast_natAbs] using neg_abs_le p.2
  have hyhigh : p.2 ≤ ((p.2.natAbs : Nat) : Int) := by
    simpa [Int.natCast_natAbs] using le_abs_self p.2
  constructor
  · exact (neg_le_neg hx').trans hxlow
  constructor
  · exact hxhigh.trans hx'
  constructor
  · exact (neg_le_neg hy').trans hylow
  · exact hyhigh.trans hy'

/-- Side length of the square corresponding to the centered box of radius `r`. -/
def boxSide (r : Nat) : Nat :=
  2 * r + 1

/-- Coordinate map from `[-r, r]` to `[0, 2*r]`. -/
def boxCoord (r : Nat) (z : Int) : Nat :=
  (z + (r : Int)).toNat

theorem boxCoord_lt {r : Nat} {z : Int}
    (hlo : -(r : Int) ≤ z) (hhi : z ≤ (r : Int)) :
    boxCoord r z < boxSide r := by
  have hnonneg : 0 ≤ z + (r : Int) := by linarith
  rw [boxCoord, Int.toNat_lt hnonneg]
  unfold boxSide
  norm_num
  linarith

theorem boxCoord_succ {r : Nat} {z : Int} (hlo : -(r : Int) ≤ z) :
    boxCoord r (z + 1) = boxCoord r z + 1 := by
  have h0 : 0 ≤ z + (r : Int) := by linarith
  have h1 : 0 ≤ z + 1 + (r : Int) := by linarith
  apply Int.ofNat.inj
  simp [boxCoord, Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h1]
  linarith

theorem boxCoord_lt_of_inBox {r : Nat} {p : Int × Int} (hp : InBox r p) :
    boxCoord r p.1 < boxSide r ∧ boxCoord r p.2 < boxSide r := by
  exact ⟨boxCoord_lt hp.1 hp.2.1, boxCoord_lt hp.2.2.1 hp.2.2.2⟩

def boxFinX {r : Nat} (p : Box r) : Fin (boxSide r) :=
  ⟨boxCoord r p.1.1, (boxCoord_lt_of_inBox p.2).1⟩

def boxFinY {r : Nat} (p : Box r) : Fin (boxSide r) :=
  ⟨boxCoord r p.1.2, (boxCoord_lt_of_inBox p.2).2⟩

/-- A tiling of the square of side `2 * r + 1` restricts to the centered box of radius `r`. -/
theorem tileableBox_of_tileableSquare {T : TileSet} {r : Nat} :
    TileableSquare T (boxSide r) → TileableBox T r := by
  rintro ⟨x, hx⟩
  let y : BoxPattern T r := fun p => ⟨x (boxFinX p) (boxFinY p), hx.1 (boxFinX p) (boxFinY p)⟩
  refine ⟨y, ?_⟩
  constructor
  · intro p hp
    let q : Box r := ⟨(p.1.1 + 1, p.1.2), hp⟩
    have hsucc : boxCoord r (p.1.1 + 1) = boxCoord r p.1.1 + 1 :=
      boxCoord_succ p.2.1
    have hi : (boxFinX p).val + 1 < boxSide r := by
      simpa [boxFinX, q, hsucc] using (boxFinX q).isLt
    have hxq : boxFinX q = ⟨(boxFinX p).val + 1, hi⟩ := by
      apply Fin.ext
      simp [boxFinX, q, hsucc]
    have hyq : boxFinY q = boxFinY p := by
      apply Fin.ext
      simp [boxFinY, q]
    have hmatch := hx.2.1 (boxFinX p) (boxFinY p) hi
    simpa [y, q, hxq, hyq] using hmatch
  · intro p hp
    let q : Box r := ⟨(p.1.1, p.1.2 + 1), hp⟩
    have hsucc : boxCoord r (p.1.2 + 1) = boxCoord r p.1.2 + 1 :=
      boxCoord_succ p.property.right.right.left
    have hj : (boxFinY p).val + 1 < boxSide r := by
      simpa [boxFinY, q, hsucc] using (boxFinY q).isLt
    have hxq : boxFinX q = boxFinX p := by
      apply Fin.ext
      simp [boxFinX, q]
    have hyq : boxFinY q = ⟨(boxFinY p).val + 1, hj⟩ := by
      apply Fin.ext
      simp [boxFinY, q, hsucc]
    have hmatch := hx.2.2 (boxFinX p) (boxFinY p) hj
    simpa [y, q, hxq, hyq] using hmatch

theorem all_tileableBoxes_of_all_tileableSquares {T : TileSet} :
    (∀ n : Nat, TileableSquare T n) → ∀ r : Nat, TileableBox T r := by
  intro hsquares r
  exact tileableBox_of_tileableSquare (hsquares (boxSide r))

/-- Extend a finite centered box pattern to an arbitrary global assignment. -/
def extendBoxPattern {T : TileSet} {r : Nat} (x : BoxPattern T r) : GlobalAssignment T :=
  fun p => if h : InBox r p then x ⟨p, h⟩ else x ⟨(0, 0), by simp [InBox]⟩

@[simp]
theorem extendBoxPattern_of_mem {T : TileSet} {r : Nat} (x : BoxPattern T r) (p : Box r) :
    extendBoxPattern x p.1 = x p := by
  rw [extendBoxPattern, dif_pos p.2]

theorem boxCylinder_nonempty {T : TileSet} {r : Nat} :
    TileableBox T r → (BoxCylinder T r).Nonempty := by
  intro h
  rcases h with ⟨x, hx⟩
  refine ⟨extendBoxPattern x, ?_⟩
  have heq : (fun p : Box r => extendBoxPattern x p.1) = x := by
    funext p
    simp
  simpa [BoxCylinder, heq] using hx

theorem isClosed_boxCylinder (T : TileSet) (r : Nat) : IsClosed (BoxCylinder T r) := by
  unfold BoxCylinder ValidBoxTiling
  rw [Set.setOf_and]
  apply IsClosed.inter
  · convert (isClosed_iInter fun (p : Box r) =>
      isClosed_iInter fun (_hp : InBox r (p.1.1 + 1, p.1.2)) => by
        have hclosed : IsClosed
            {q : TileIn T × TileIn T | WangTile.HMatches q.1.1 q.2.1} := by
          exact isClosed_discrete _
        exact (IsClosed.preimage
          ((continuous_apply p.1).prodMk (continuous_apply (p.1.1 + 1, p.1.2))) hclosed :
            IsClosed ((fun x : GlobalAssignment T => (x p.1, x (p.1.1 + 1, p.1.2))) ⁻¹'
              {q : TileIn T × TileIn T | WangTile.HMatches q.1.1 q.2.1}))) using 1
    ext x
    simp
  · convert (isClosed_iInter fun (p : Box r) =>
      isClosed_iInter fun (_hp : InBox r (p.1.1, p.1.2 + 1)) => by
        have hclosed : IsClosed
            {q : TileIn T × TileIn T | WangTile.VMatches q.1.1 q.2.1} := by
          exact isClosed_discrete _
        exact (IsClosed.preimage
          ((continuous_apply p.1).prodMk (continuous_apply (p.1.1, p.1.2 + 1))) hclosed :
            IsClosed ((fun x : GlobalAssignment T => (x p.1, x (p.1.1, p.1.2 + 1))) ⁻¹'
              {q : TileIn T × TileIn T | WangTile.VMatches q.1.1 q.2.1}))) using 1
    ext x
    simp

theorem boxCylinder_succ_subset (T : TileSet) (r : Nat) :
    BoxCylinder T (r + 1) ⊆ BoxCylinder T r := by
  intro x hx
  rcases hx with ⟨hxH, hxV⟩
  constructor
  · intro p hp
    exact hxH ⟨p.1, inBox_mono (Nat.le_succ r) p.2⟩
      (inBox_mono (Nat.le_succ r) hp)
  · intro p hp
    exact hxV ⟨p.1, inBox_mono (Nat.le_succ r) p.2⟩
      (inBox_mono (Nat.le_succ r) hp)

theorem tilesPlane_of_all_tileableBoxes {T : TileSet} :
    (∀ r : Nat, TileableBox T r) → TilesPlane T := by
  intro hboxes
  have hnonempty : ∀ r : Nat, (BoxCylinder T r).Nonempty :=
    fun r => boxCylinder_nonempty (hboxes r)
  have hclosed : ∀ r : Nat, IsClosed (BoxCylinder T r) :=
    isClosed_boxCylinder T
  have hcompact0 : IsCompact (BoxCylinder T 0) :=
    (hclosed 0).isCompact
  rcases IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (BoxCylinder T) (boxCylinder_succ_subset T) hnonempty hcompact0 hclosed with ⟨x, hx⟩
  have hxall : ∀ r : Nat, x ∈ BoxCylinder T r := by
    simpa using hx
  refine ⟨x, ?_⟩
  constructor
  · intro p
    let r := max (max p.1.natAbs (p.1 + 1).natAbs) p.2.natAbs
    have hp : InBox r p := by
      exact inBox_of_natAbs_le
        ((Nat.le_max_left p.1.natAbs (p.1 + 1).natAbs).trans (Nat.le_max_left _ _))
        (Nat.le_max_right _ _)
    have hpE : InBox r (p.1 + 1, p.2) := by
      exact inBox_of_natAbs_le
        ((Nat.le_max_right p.1.natAbs (p.1 + 1).natAbs).trans (Nat.le_max_left _ _))
        (Nat.le_max_right _ _)
    exact (hxall r).1 ⟨p, hp⟩ hpE
  · intro p
    let r := max p.1.natAbs (max p.2.natAbs (p.2 + 1).natAbs)
    have hp : InBox r p := by
      exact inBox_of_natAbs_le
        (Nat.le_max_left _ _)
        ((Nat.le_max_left p.2.natAbs (p.2 + 1).natAbs).trans (Nat.le_max_right _ _))
    have hpN : InBox r (p.1, p.2 + 1) := by
      exact inBox_of_natAbs_le
        (Nat.le_max_left _ _)
        ((Nat.le_max_right p.2.natAbs (p.2 + 1).natAbs).trans (Nat.le_max_right _ _))
    exact (hxall r).2 ⟨p, hp⟩ hpN

theorem tilesPlane_iff_all_tileableBoxes (T : TileSet) :
    TilesPlane T ↔ ∀ r : Nat, TileableBox T r := by
  constructor
  · exact tileableBox_of_tilesPlane
  · exact tilesPlane_of_all_tileableBoxes

/--
Compactness from a cofinal family of finite square tilings.

This is convenient for substitution arguments, which naturally produce
tileable squares at selected large side lengths rather than at every exact side
length.  Cropping supplies the missing smaller exact squares.
-/
theorem tilesPlane_of_cofinal_tileableSquares {T : TileSet}
    (hsquares : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ TileableSquare T m) :
    TilesPlane T := by
  apply tilesPlane_of_all_tileableBoxes
  apply all_tileableBoxes_of_all_tileableSquares
  intro n
  rcases hsquares n with ⟨m, hnm, hm⟩
  exact tileableSquare_crop hnm hm

/--
Square compactness for plane tilings, derived by translating centered boxes to
ordinary finite squares and applying centered-box compactness.
-/
theorem tilesPlane_iff_all_tileableSquares (T : TileSet) :
    TilesPlane T ↔ ∀ n : Nat, TileableSquare T n := by
  constructor
  · exact tileableSquare_of_tilesPlane
  · intro hsquares
    exact tilesPlane_of_all_tileableBoxes (all_tileableBoxes_of_all_tileableSquares hsquares)

/-- Global assignments of tiles on the first quadrant, without adjacency constraints. -/
abbrev QuarterAssignment (T : TileSet) :=
  Nat × Nat → TileIn T

/--
A global first-quadrant assignment whose restriction to `[0,n] × [0,n]` is valid
and whose origin is the prescribed seed.
-/
def QuarterCylinder (T : TileSet) (seed : WangTile) (n : Nat) :
    Set (QuarterAssignment T) :=
  {x |
    (∀ p : Nat × Nat, p.1 + 1 ≤ n → p.2 ≤ n →
      WangTile.HMatches (x p).1 (x (p.1 + 1, p.2)).1) ∧
    (∀ p : Nat × Nat, p.1 ≤ n → p.2 + 1 ≤ n →
      WangTile.VMatches (x p).1 (x (p.1, p.2 + 1)).1) ∧
    (x (0, 0)).1 = seed}

/-- Extend a seeded finite square to an arbitrary first-quadrant assignment. -/
def extendFixedCornerSquare {T : TileSet} {seed : WangTile} {n : Nat}
    (x : Rectangle (n + 1) (n + 1)) (hx : ValidRectangle T x)
    (hseed : x ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ = seed) :
    QuarterAssignment T :=
  have hseed_mem : seed ∈ T := by
    rw [← hseed]
    exact hx.1 ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩
  fun p =>
    if hp : p.1 < n + 1 ∧ p.2 < n + 1 then
      ⟨x ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩, hx.1 ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩⟩
    else
      ⟨seed, hseed_mem⟩

theorem quarterCylinder_nonempty {T : TileSet} {seed : WangTile} {n : Nat} :
    TileableFixedCornerSquare T seed (n + 1) →
      (QuarterCylinder T seed n).Nonempty := by
  rintro ⟨_hn, x, hx, hseed⟩
  let y := extendFixedCornerSquare x hx hseed
  refine ⟨y, ?_⟩
  constructor
  · intro p hpE hpY
    have hpX : p.1 < n + 1 :=
      Nat.lt_succ_of_le ((Nat.le_succ p.1).trans hpE)
    have hpY' : p.2 < n + 1 :=
      Nat.lt_succ_of_le hpY
    have hpEX : p.1 + 1 < n + 1 :=
      Nat.lt_succ_of_le hpE
    have hmatch := hx.2.1 ⟨p.1, hpX⟩ ⟨p.2, hpY'⟩ hpEX
    simpa [y, extendFixedCornerSquare, hpX, hpY', hpEX] using hmatch
  constructor
  · intro p hpX hpN
    have hpX' : p.1 < n + 1 :=
      Nat.lt_succ_of_le hpX
    have hpY : p.2 < n + 1 :=
      Nat.lt_succ_of_le ((Nat.le_succ p.2).trans hpN)
    have hpNY : p.2 + 1 < n + 1 :=
      Nat.lt_succ_of_le hpN
    have hmatch := hx.2.2 ⟨p.1, hpX'⟩ ⟨p.2, hpY⟩ hpNY
    simpa [y, extendFixedCornerSquare, hpX', hpY, hpNY] using hmatch
  · simpa [y, extendFixedCornerSquare] using hseed

theorem isClosed_quarterCylinder (T : TileSet) (seed : WangTile) (n : Nat) :
    IsClosed (QuarterCylinder T seed n) := by
  unfold QuarterCylinder
  rw [Set.setOf_and, Set.setOf_and]
  apply IsClosed.inter
  · convert (isClosed_iInter fun (p : Nat × Nat) =>
      isClosed_iInter fun (_hpE : p.1 + 1 ≤ n) =>
        isClosed_iInter fun (_hpY : p.2 ≤ n) => by
          have hclosed : IsClosed
              {q : TileIn T × TileIn T | WangTile.HMatches q.1.1 q.2.1} := by
            exact isClosed_discrete _
          exact (IsClosed.preimage
            ((continuous_apply p).prodMk (continuous_apply (p.1 + 1, p.2))) hclosed :
              IsClosed ((fun x : QuarterAssignment T => (x p, x (p.1 + 1, p.2))) ⁻¹'
                {q : TileIn T × TileIn T | WangTile.HMatches q.1.1 q.2.1}))) using 1
    ext x
    simp
  · apply IsClosed.inter
    · convert (isClosed_iInter fun (p : Nat × Nat) =>
        isClosed_iInter fun (_hpX : p.1 ≤ n) =>
          isClosed_iInter fun (_hpN : p.2 + 1 ≤ n) => by
            have hclosed : IsClosed
                {q : TileIn T × TileIn T | WangTile.VMatches q.1.1 q.2.1} := by
              exact isClosed_discrete _
            exact (IsClosed.preimage
              ((continuous_apply p).prodMk (continuous_apply (p.1, p.2 + 1))) hclosed :
                IsClosed ((fun x : QuarterAssignment T => (x p, x (p.1, p.2 + 1))) ⁻¹'
                  {q : TileIn T × TileIn T | WangTile.VMatches q.1.1 q.2.1}))) using 1
      ext x
      simp
    · have hclosed : IsClosed {t : TileIn T | t.1 = seed} := by
        exact isClosed_discrete _
      exact (IsClosed.preimage (continuous_apply (0, 0)) hclosed :
        IsClosed ((fun x : QuarterAssignment T => x (0, 0)) ⁻¹' {t : TileIn T | t.1 = seed}))

theorem quarterCylinder_succ_subset (T : TileSet) (seed : WangTile) (n : Nat) :
    QuarterCylinder T seed (n + 1) ⊆ QuarterCylinder T seed n := by
  intro x hx
  rcases hx with ⟨hxH, hxV, hxSeed⟩
  constructor
  · intro p hpE hpY
    exact hxH p (Nat.le_trans hpE (Nat.le_succ n)) (Nat.le_trans hpY (Nat.le_succ n))
  constructor
  · intro p hpX hpN
    exact hxV p (Nat.le_trans hpX (Nat.le_succ n)) (Nat.le_trans hpN (Nat.le_succ n))
  · exact hxSeed

theorem tilesQuarterWithSeed_of_all_fixedCornerSquares {T : TileSet} {seed : WangTile} :
    (∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n) →
      TilesQuarterWithSeed T seed := by
  intro hsquares
  have hnonempty : ∀ n : Nat, (QuarterCylinder T seed n).Nonempty := by
    intro n
    exact quarterCylinder_nonempty (hsquares (n + 1) (Nat.succ_pos n))
  have hclosed : ∀ n : Nat, IsClosed (QuarterCylinder T seed n) :=
    isClosed_quarterCylinder T seed
  have hcompact0 : IsCompact (QuarterCylinder T seed 0) :=
    (hclosed 0).isCompact
  rcases IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (QuarterCylinder T seed) (quarterCylinder_succ_subset T seed)
      hnonempty hcompact0 hclosed with ⟨x, hx⟩
  have hxall : ∀ n : Nat, x ∈ QuarterCylinder T seed n := by
    simpa using hx
  refine ⟨x, ?_, ?_⟩
  · constructor
    · intro p
      exact (hxall (max (p.1 + 1) p.2)).1 p
        (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    · intro p
      exact (hxall (max p.1 (p.2 + 1))).2.1 p
        (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  · exact (hxall 0).2.2

/--
Seeded quarter-plane compactness: a seeded first-quadrant tiling exists exactly
when every nonempty finite square has a tiling with that lower-left seed.
-/
theorem tilesQuarterWithSeed_iff_all_fixedCornerSquares (T : TileSet) (seed : WangTile) :
    TilesQuarterWithSeed T seed ↔
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n := by
  constructor
  · exact fixedCornerSquare_of_tilesQuarterWithSeed
  · intro hsquares
    exact tilesQuarterWithSeed_of_all_fixedCornerSquares hsquares

end LeanWang
