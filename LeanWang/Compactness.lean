/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/
import LeanWang.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Continuous
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic

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

end LeanWang
