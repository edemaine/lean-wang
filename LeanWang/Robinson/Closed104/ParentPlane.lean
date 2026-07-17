/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.Desubstitution

/-!
Global parent-plane construction for the corrected Ollinger tiles.

The thin layer chooses one of four parity classes. Local recognizability then
selects a unique parent above every `2 x 2` block in that class, while boundary
reflection proves that the selected parents form another valid plane tiling.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ParentPlane

open LocalRecognizability Desubstitution

set_option maxRecDepth 20000

/-- Every valid plane has a site in thin phase `a`, at most one step from any site. -/
theorem exists_phaseA_origin {z : IndexPlane} (hz : ValidIndexPlane z) :
    ∃ origin : Int × Int, thinAt z origin = .a := by
  let p : Int × Int := (0, 0)
  cases hphase : thinAt z p with
  | a => exact ⟨p, hphase⟩
  | b =>
      refine ⟨shift p 1 1, ?_⟩
      calc
        thinAt z (shift p 1 1) =
            phaseNorth (thinAt z (shift p 1 0)) := by
          simpa only [shift_shift, Int.reduceAdd] using
            thin_north hz (shift p 1 0)
        _ = phaseNorth (phaseEast (thinAt z p)) := by
          rw [thin_east hz p]
        _ = .a := by rw [hphase]; rfl
  | c =>
      refine ⟨shift p 1 0, ?_⟩
      calc
        thinAt z (shift p 1 0) = phaseEast (thinAt z p) := thin_east hz p
        _ = .a := by rw [hphase]; rfl
  | d =>
      refine ⟨shift p 0 1, ?_⟩
      calc
        thinAt z (shift p 0 1) = phaseNorth (thinAt z p) := thin_north hz p
        _ = .a := by rw [hphase]; rfl

/-- Southwest child coordinate of a parent-lattice site. -/
def blockOrigin (origin k : Int × Int) : Int × Int :=
  shift origin (2 * k.1) (2 * k.2)

theorem blockOrigin_phaseA {z : IndexPlane} (hz : ValidIndexPlane z)
    {origin : Int × Int} (horigin : thinAt z origin = .a) (k : Int × Int) :
    thinAt z (blockOrigin origin k) = .a := by
  exact (thin_even hz origin k.1 k.2).trans horigin

@[simp]
theorem blockOrigin_east (origin k : Int × Int) :
    blockOrigin origin (k.1 + 1, k.2) = shift (blockOrigin origin k) 2 0 := by
  ext <;> simp [blockOrigin, shift, mul_add, add_assoc]

@[simp]
theorem blockOrigin_north (origin k : Int × Int) :
    blockOrigin origin (k.1, k.2 + 1) = shift (blockOrigin origin k) 0 2 := by
  ext <;> simp [blockOrigin, shift, mul_add, add_assoc]

/-- Four child equations saying that `parent` desubstitutes the block at `k`. -/
def IsParentAt (z : IndexPlane) (origin : Int × Int)
    (parent : Index) (k : Int × Int) : Prop :=
  childBlock parent offset0 offset0 = z (blockOrigin origin k) ∧
    childBlock parent offset1 offset0 =
      z (shift (blockOrigin origin k) 1 0) ∧
    childBlock parent offset0 offset1 =
      z (shift (blockOrigin origin k) 0 1) ∧
    childBlock parent offset1 offset1 =
      z (shift (blockOrigin origin k) 1 1)

/-- Choice applied pointwise to locally unique parents. -/
theorem exists_parentFunction {z : IndexPlane} (hz : ValidIndexPlane z)
    {origin : Int × Int} (horigin : thinAt z origin = .a) :
    ∃ parent : IndexPlane, ∀ k, IsParentAt z origin (parent k) k := by
  have hlocal : ∀ k : Int × Int, ∃ parent : Index,
      IsParentAt z origin parent k := by
    intro k
    rcases existsUnique_parentAt hz (blockOrigin origin k)
        (blockOrigin_phaseA hz horigin k) with ⟨parent, hparent, _⟩
    exact ⟨parent, hparent⟩
  choose parent hparent using hlocal
  exact ⟨parent, hparent⟩

private theorem childRectangle_apply (parent : Index) (i j : Fin 2) :
    childRectangle parent i j = tile (components (childBlock parent i j)) :=
  rfl

private theorem hMatches_of_child_eqs
    {left right leftSouth leftNorth rightSouth rightNorth : Index}
    (hlSouth : childBlock left offset1 offset0 = leftSouth)
    (hlNorth : childBlock left offset1 offset1 = leftNorth)
    (hrSouth : childBlock right offset0 offset0 = rightSouth)
    (hrNorth : childBlock right offset0 offset1 = rightNorth)
    (hsouth : WangTile.HMatches
      (tile (components leftSouth)) (tile (components rightSouth)))
    (hnorth : WangTile.HMatches
      (tile (components leftNorth)) (tile (components rightNorth))) :
    WangTile.HMatches (tile (components left)) (tile (components right)) := by
  apply hMatches_of_childHMatches
  constructor
  · rw [childRectangle_apply, childRectangle_apply]
    change WangTile.HMatches
      (tile (components (childBlock left offset1 offset0)))
      (tile (components (childBlock right offset0 offset0)))
    rw [hlSouth, hrSouth]
    exact hsouth
  · rw [childRectangle_apply, childRectangle_apply]
    change WangTile.HMatches
      (tile (components (childBlock left offset1 offset1)))
      (tile (components (childBlock right offset0 offset1)))
    rw [hlNorth, hrNorth]
    exact hnorth

private theorem vMatches_of_child_eqs
    {lower upper lowerWest lowerEast upperWest upperEast : Index}
    (hlWest : childBlock lower offset0 offset1 = lowerWest)
    (hlEast : childBlock lower offset1 offset1 = lowerEast)
    (huWest : childBlock upper offset0 offset0 = upperWest)
    (huEast : childBlock upper offset1 offset0 = upperEast)
    (hwest : WangTile.VMatches
      (tile (components lowerWest)) (tile (components upperWest)))
    (heast : WangTile.VMatches
      (tile (components lowerEast)) (tile (components upperEast))) :
    WangTile.VMatches (tile (components lower)) (tile (components upper)) := by
  apply vMatches_of_childVMatches
  constructor
  · rw [childRectangle_apply, childRectangle_apply]
    change WangTile.VMatches
      (tile (components (childBlock lower offset0 offset1)))
      (tile (components (childBlock upper offset0 offset0)))
    rw [hlWest, huWest]
    exact hwest
  · rw [childRectangle_apply, childRectangle_apply]
    change WangTile.VMatches
      (tile (components (childBlock lower offset1 offset1)))
      (tile (components (childBlock upper offset1 offset0)))
    rw [hlEast, huEast]
    exact heast

/-- Boundary reflection makes any pointwise recognized parent plane valid. -/
theorem parentFunction_valid {z parent : IndexPlane} (hz : ValidIndexPlane z)
    (origin : Int × Int)
    (hparent : ∀ k, IsParentAt z origin (parent k) k) :
    ValidIndexPlane parent := by
  constructor
  · intro k
    have hk := hparent k
    have he := hparent (k.1 + 1, k.2)
    apply hMatches_of_child_eqs hk.2.1 hk.2.2.2 he.1 he.2.2.1
    · simpa only [blockOrigin_east, shift_east, Int.reduceAdd] using
        hz.1 (shift (blockOrigin origin k) 1 0)
    · simpa only [blockOrigin_east, shift_east, shift_shift, Int.reduceAdd] using
        hz.1 (shift (blockOrigin origin k) 1 1)
  · intro k
    have hk := hparent k
    have hn := hparent (k.1, k.2 + 1)
    apply vMatches_of_child_eqs hk.2.2.1 hk.2.2.2 hn.1 hn.2.1
    · simpa only [blockOrigin_north, shift_north, Int.reduceAdd] using
        hz.2 (shift (blockOrigin origin k) 0 1)
    · simpa only [blockOrigin_north, shift_north, shift_shift, Int.reduceAdd] using
        hz.2 (shift (blockOrigin origin k) 1 1)

/-- A valid plane is exactly a substitution of another valid plane, up to parity. -/
theorem exists_valid_parentPlane {z : IndexPlane} (hz : ValidIndexPlane z) :
    ∃ (origin : Int × Int) (parent : IndexPlane),
      thinAt z origin = .a ∧
      ValidIndexPlane parent ∧
      ∀ k : Int × Int,
        childBlock (parent k) offset0 offset0 = z (blockOrigin origin k) ∧
        childBlock (parent k) offset1 offset0 =
          z (shift (blockOrigin origin k) 1 0) ∧
        childBlock (parent k) offset0 offset1 =
          z (shift (blockOrigin origin k) 0 1) ∧
        childBlock (parent k) offset1 offset1 =
          z (shift (blockOrigin origin k) 1 1) := by
  obtain ⟨origin, horigin⟩ := exists_phaseA_origin hz
  obtain ⟨parent, hparent⟩ := exists_parentFunction hz horigin
  exact ⟨origin, parent, horigin, parentFunction_valid hz origin hparent, hparent⟩

end ParentPlane
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
