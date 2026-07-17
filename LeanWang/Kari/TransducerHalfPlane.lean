/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.HalfPlane
import LeanWang.Kari.Transducer

/-!
# Upper-half-plane transducer diagrams

This module specializes the local transducer-to-Wang correspondence to the
upper half-plane.  Rows are indexed by `Nat`, matching the forward-time
orientation used in Kari's construction, while columns remain bi-infinite.
-/

namespace LeanWang
namespace Kari

/--
An upper-half-plane space-time diagram of `M`.  `digits p` labels the boundary
immediately below cell `p`, while `carries p` labels its west edge.
-/
def Transducer.IsUpperHalfDiagram (M : Transducer)
    (digits carries : Int × Nat → Nat) : Prop :=
  ∀ p : Int × Nat, ∃ t ∈ M,
    t.input = digits p ∧
      t.output = digits (p.1, p.2 + 1) ∧
      t.left = carries p ∧
      t.right = carries (p.1 + 1, p.2)

/-- The transducer admits a space-time diagram indexed by `Int × Nat`. -/
def Transducer.HasUpperHalfDiagram (M : Transducer) : Prop :=
  ∃ digits carries : Int × Nat → Nat, M.IsUpperHalfDiagram digits carries

/-- Every upper-half-plane tiling by transducer tiles decodes to a diagram. -/
theorem Transducer.hasUpperHalfDiagram_of_tilesUpperHalf {M : Transducer} :
    TilesUpperHalf M.tiles → M.HasUpperHalfDiagram := by
  rintro ⟨x, hx⟩
  let digits : Int × Nat → Nat := fun p => (x p).1.s
  let carries : Int × Nat → Nat := fun p => (x p).1.w
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

/-- Every upper-half-plane transducer diagram encodes as a tiling. -/
theorem Transducer.tilesUpperHalf_of_hasUpperHalfDiagram {M : Transducer} :
    M.HasUpperHalfDiagram → TilesUpperHalf M.tiles := by
  classical
  rintro ⟨digits, carries, hdiagram⟩
  let transitionAt : Int × Nat → Transition := fun p => Classical.choose (hdiagram p)
  have transitionAt_mem (p : Int × Nat) : transitionAt p ∈ M :=
    (Classical.choose_spec (hdiagram p)).1
  have transitionAt_spec (p : Int × Nat) :
      (transitionAt p).input = digits p ∧
        (transitionAt p).output = digits (p.1, p.2 + 1) ∧
        (transitionAt p).left = carries p ∧
        (transitionAt p).right = carries (p.1 + 1, p.2) :=
    (Classical.choose_spec (hdiagram p)).2
  let x : Int × Nat → TileIn M.tiles := fun p =>
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
The local transducer-to-Wang conversion is exact on the upper half-plane.
-/
theorem Transducer.tilesUpperHalf_iff_hasUpperHalfDiagram (M : Transducer) :
    TilesUpperHalf M.tiles ↔ M.HasUpperHalfDiagram :=
  ⟨Transducer.hasUpperHalfDiagram_of_tilesUpperHalf,
    Transducer.tilesUpperHalf_of_hasUpperHalfDiagram⟩

/-- By compactness, a transducer tiles the plane exactly when it has a
forward-time diagram on the upper half-plane. -/
theorem Transducer.tilesPlane_iff_hasUpperHalfDiagram (M : Transducer) :
    TilesPlane M.tiles ↔ M.HasUpperHalfDiagram := by
  calc
    TilesPlane M.tiles ↔ TilesUpperHalf M.tiles :=
      (tilesUpperHalf_iff_tilesPlane M.tiles).symm
    _ ↔ M.HasUpperHalfDiagram := M.tilesUpperHalf_iff_hasUpperHalfDiagram

end Kari
end LeanWang
