/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic

/-!
# Finite transducers as Wang tiles

This file formalizes the local transducer-to-tile conversion used in Kari's
construction.  A transition reads a digit on the south edge, writes a digit on
the north edge, and passes a finite-state carry from west to east.  Consequently,
plane tilings by the resulting tiles are exactly bi-infinite space-time diagrams
of the transducer.

The construction follows Section 5.3 of Jeandel and Vanier, *The Undecidability
of the Domino Problem* (2020), which presents Kari's rational-multiplier method.
All definitions and proofs here are independent Lean formulations.
-/

namespace LeanWang
namespace Kari

/-- One transition of a nondeterministic letter-to-letter transducer. -/
structure Transition where
  input : Nat
  output : Nat
  left : Nat
  right : Nat
deriving DecidableEq, Repr

namespace Transition

/-- Encode a transition by the tuple in Wang-edge order. -/
def edgeTuple (t : Transition) : Nat × Nat × Nat × Nat :=
  (t.output, t.input, t.right, t.left)

/-- Recover a transition from a tuple in Wang-edge order. -/
def ofEdgeTuple (p : Nat × Nat × Nat × Nat) : Transition where
  output := p.1
  input := p.2.1
  right := p.2.2.1
  left := p.2.2.2

/-- Transitions are equivalent to their four edge labels. -/
def equivEdgeTuple : Transition ≃ Nat × Nat × Nat × Nat where
  toFun := edgeTuple
  invFun := ofEdgeTuple
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro p
    rcases p with ⟨output, input, right, left⟩
    rfl

instance instPrimcodableTransition : Primcodable Transition :=
  Primcodable.ofEquiv (Nat × Nat × Nat × Nat) equivEdgeTuple

/-- The Wang tile associated with a transducer transition. -/
def toTile (t : Transition) : WangTile :=
  WangTile.ofTuple t.edgeTuple

@[simp] theorem toTile_n (t : Transition) : t.toTile.n = t.output := rfl
@[simp] theorem toTile_s (t : Transition) : t.toTile.s = t.input := rfl
@[simp] theorem toTile_e (t : Transition) : t.toTile.e = t.right := rfl
@[simp] theorem toTile_w (t : Transition) : t.toTile.w = t.left := rfl

theorem edgeTuple_primrec : Primrec edgeTuple := by
  simpa [equivEdgeTuple] using
    (Primrec.of_equiv (e := equivEdgeTuple) : Primrec equivEdgeTuple)

theorem toTile_primrec : Primrec toTile :=
  WangTile.ofTuple_primrec.comp edgeTuple_primrec

theorem toTile_injective : Function.Injective toTile := by
  intro a b h
  cases a
  cases b
  simp only [toTile, edgeTuple, WangTile.ofTuple, WangTile.mk.injEq,
    Transition.mk.injEq] at h ⊢
  exact ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

end Transition

/-- A finite nondeterministic letter-to-letter transducer. -/
abbrev Transducer := List Transition

/-- Turn every transition into its Wang tile. -/
def Transducer.tiles (M : Transducer) : TileSet :=
  M.map Transition.toTile

theorem Transducer.tiles_primrec : Primrec Transducer.tiles := by
  unfold Transducer.tiles
  refine Primrec.list_map Primrec.id ?_
  exact Primrec₂.mk (Transition.toTile_primrec.comp Primrec.snd)

@[simp]
theorem Transition.mem_tiles_iff {M : Transducer} {tile : WangTile} :
    tile ∈ M.tiles ↔ ∃ t ∈ M, t.toTile = tile := by
  simp [Transducer.tiles]

theorem Transition.toTile_mem_tiles {M : Transducer} {t : Transition}
    (ht : t ∈ M) : t.toTile ∈ M.tiles := by
  exact Transition.mem_tiles_iff.2 ⟨t, ht, rfl⟩

/--
A bi-infinite space-time diagram of `M`.  `digits p` labels the horizontal
boundary immediately below cell `p`, while `carries p` labels its west edge.
-/
def Transducer.IsPlaneDiagram (M : Transducer)
    (digits carries : Int × Int → Nat) : Prop :=
  ∀ p : Int × Int, ∃ t ∈ M,
    t.input = digits p ∧
      t.output = digits (p.1, p.2 + 1) ∧
      t.left = carries p ∧
      t.right = carries (p.1 + 1, p.2)

/-- The transducer admits a bi-infinite space-time diagram. -/
def Transducer.HasPlaneDiagram (M : Transducer) : Prop :=
  ∃ digits carries : Int × Int → Nat, M.IsPlaneDiagram digits carries

/-- Every tiling by transducer tiles decodes to a transducer diagram. -/
theorem Transducer.hasPlaneDiagram_of_tilesPlane {M : Transducer} :
    TilesPlane M.tiles → M.HasPlaneDiagram := by
  rintro ⟨x, hx⟩
  let digits : Int × Int → Nat := fun p => (x p).1.s
  let carries : Int × Int → Nat := fun p => (x p).1.w
  refine ⟨digits, carries, ?_⟩
  intro p
  rcases Transition.mem_tiles_iff.1 (x p).2 with ⟨t, ht, htile⟩
  refine ⟨t, ht, ?_, ?_, ?_, ?_⟩
  · simpa [digits] using congrArg WangTile.s htile
  · calc
      t.output = (x p).1.n := by
        simpa using congrArg WangTile.n htile
      _ = (x (p.1, p.2 + 1)).1.s := hx.2 p
      _ = digits (p.1, p.2 + 1) := rfl
  · simpa [carries] using congrArg WangTile.w htile
  · calc
      t.right = (x p).1.e := by
        simpa using congrArg WangTile.e htile
      _ = (x (p.1 + 1, p.2)).1.w := hx.1 p
      _ = carries (p.1 + 1, p.2) := rfl

/-- Every transducer diagram encodes as a tiling by the transition tiles. -/
theorem Transducer.tilesPlane_of_hasPlaneDiagram {M : Transducer} :
    M.HasPlaneDiagram → TilesPlane M.tiles := by
  classical
  rintro ⟨digits, carries, hdiagram⟩
  let transitionAt : Int × Int → Transition := fun p => Classical.choose (hdiagram p)
  have transitionAt_mem (p : Int × Int) : transitionAt p ∈ M :=
    (Classical.choose_spec (hdiagram p)).1
  have transitionAt_spec (p : Int × Int) :
      (transitionAt p).input = digits p ∧
        (transitionAt p).output = digits (p.1, p.2 + 1) ∧
        (transitionAt p).left = carries p ∧
        (transitionAt p).right = carries (p.1 + 1, p.2) :=
    (Classical.choose_spec (hdiagram p)).2
  let x : Int × Int → TileIn M.tiles := fun p =>
    ⟨(transitionAt p).toTile,
      Transition.toTile_mem_tiles (transitionAt_mem p)⟩
  refine ⟨x, ?_⟩
  constructor
  · intro p
    change (transitionAt p).right =
      (transitionAt (p.1 + 1, p.2)).left
    calc
      (transitionAt p).right = carries (p.1 + 1, p.2) :=
        (transitionAt_spec p).2.2.2
      _ = (transitionAt (p.1 + 1, p.2)).left :=
        (transitionAt_spec (p.1 + 1, p.2)).2.2.1.symm
  · intro p
    change (transitionAt p).output =
      (transitionAt (p.1, p.2 + 1)).input
    calc
      (transitionAt p).output = digits (p.1, p.2 + 1) :=
        (transitionAt_spec p).2.1
      _ = (transitionAt (p.1, p.2 + 1)).input :=
        (transitionAt_spec (p.1, p.2 + 1)).1.symm

/--
The local transducer-to-Wang conversion is exact: its plane tilings are precisely
the bi-infinite space-time diagrams of the transducer.
-/
theorem Transducer.tilesPlane_iff_hasPlaneDiagram (M : Transducer) :
    TilesPlane M.tiles ↔ M.HasPlaneDiagram :=
  ⟨Transducer.hasPlaneDiagram_of_tilesPlane,
    Transducer.tilesPlane_of_hasPlaneDiagram⟩

end Kari
end LeanWang
