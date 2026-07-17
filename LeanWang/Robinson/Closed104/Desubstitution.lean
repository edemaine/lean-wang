/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.LocalRecognizability
import Mathlib.Algebra.Ring.Periodic

/-!
Desubstitution of valid plane tilings by the corrected Ollinger tiles.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Desubstitution

open LocalRecognizability

set_option maxRecDepth 20000

abbrev IndexPlane := Int × Int → Index

def thinAt (z : IndexPlane) (p : Int × Int) : Figure16.Thin :=
  (components (z p)).1

def ValidIndexPlane (z : IndexPlane) : Prop :=
  (∀ p : Int × Int,
      WangTile.HMatches (tile (components (z p)))
        (tile (components (z (p.1 + 1, p.2))))) ∧
    ∀ p : Int × Int,
      WangTile.VMatches (tile (components (z p)))
        (tile (components (z (p.1, p.2 + 1))))

def shift (p : Int × Int) (dx dy : Int) : Int × Int :=
  (p.1 + dx, p.2 + dy)

@[simp]
theorem shift_east (p : Int × Int) (dx dy : Int) :
    ((shift p dx dy).1 + 1, (shift p dx dy).2) = shift p (dx + 1) dy := by
  simp [shift, add_assoc]

@[simp]
theorem shift_north (p : Int × Int) (dx dy : Int) :
    ((shift p dx dy).1, (shift p dx dy).2 + 1) = shift p dx (dy + 1) := by
  simp [shift, add_assoc]

@[simp]
theorem shift_shift (p : Int × Int) (dx dy ex ey : Int) :
    shift (shift p dx dy) ex ey = shift p (dx + ex) (dy + ey) := by
  simp [shift, add_assoc]

theorem shift_even_xy (p : Int × Int) (kx ky : Int) :
    shift p (2 * kx) (2 * ky) =
      shift (shift p (2 * kx) 0) 0 (2 * ky) := by
  ext <;> simp [shift]

def rowAt (z : IndexPlane) (center : Int × Int) (dy : Int) : IndexRow4 where
  x0 := z (shift center (-1) dy)
  x1 := z (shift center 0 dy)
  x2 := z (shift center 1 dy)
  x3 := z (shift center 2 dy)

theorem rowAt_hValid {z : IndexPlane} (hz : ValidIndexPlane z)
    (center : Int × Int) (dy : Int) :
    (rowAt z center dy).HValid := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [rowAt, shift_east, Int.reduceNeg, Int.reduceAdd] using
      hz.1 (shift center (-1) dy)
  · simpa only [rowAt, shift_east, Int.reduceAdd] using
      hz.1 (shift center 0 dy)
  · simpa only [rowAt, shift_east, Int.reduceAdd] using
      hz.1 (shift center 1 dy)

theorem rowAt_vCompatible {z : IndexPlane} (hz : ValidIndexPlane z)
    (center : Int × Int) (dy : Int) :
    (rowAt z center dy).VCompatible (rowAt z center (dy + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [rowAt, shift_north] using hz.2 (shift center (-1) dy)
  · simpa only [rowAt, shift_north] using hz.2 (shift center 0 dy)
  · simpa only [rowAt, shift_north] using hz.2 (shift center 1 dy)
  · simpa only [rowAt, shift_north] using hz.2 (shift center 2 dy)

/-- The `4 x 4` neighborhood centered on a phase-`a` southwest child. -/
def neighborhoodAt {z : IndexPlane} (hz : ValidIndexPlane z)
    (center : Int × Int) (hphase : thinAt z center = .a) :
    Neighborhood where
  south := rowAt z center (-1)
  middleSouth := rowAt z center 0
  middleNorth := rowAt z center 1
  north := rowAt z center 2
  south_h := rowAt_hValid hz center (-1)
  middleSouth_h := rowAt_hValid hz center 0
  middleNorth_h := rowAt_hValid hz center 1
  north_h := rowAt_hValid hz center 2
  south_middle_v := by
    simpa using rowAt_vCompatible hz center (-1)
  middle_v := by
    simpa using rowAt_vCompatible hz center 0
  middle_north_v := by
    simpa using rowAt_vCompatible hz center 1
  centerThin := by
    simpa [thinAt, rowAt, shift] using hphase

/-- Every phase-`a` site has a unique parent whose children occupy that `2 x 2` block. -/
theorem existsUnique_parentAt {z : IndexPlane} (hz : ValidIndexPlane z)
    (center : Int × Int) (hphase : thinAt z center = .a) :
    ∃! parent : Index,
      childBlock parent offset0 offset0 = z center ∧
      childBlock parent offset1 offset0 = z (shift center 1 0) ∧
      childBlock parent offset0 offset1 = z (shift center 0 1) ∧
      childBlock parent offset1 offset1 = z (shift center 1 1) := by
  simpa [Neighborhood.IsCenterParent, neighborhoodAt, rowAt, shift] using
    (neighborhoodAt hz center hphase).existsUnique_centerParentIndex

theorem thin_east {z : IndexPlane} (hz : ValidIndexPlane z)
    (p : Int × Int) :
    thinAt z (shift p 1 0) = phaseEast (thinAt z p) := by
  simpa only [thinAt, shift, Int.add_zero] using
    thin_eq_thinEast_of_hMatches (hz.1 p)

theorem thin_north {z : IndexPlane} (hz : ValidIndexPlane z)
    (p : Int × Int) :
    thinAt z (shift p 0 1) = phaseNorth (thinAt z p) := by
  simpa only [thinAt, shift, Int.add_zero] using
    thin_eq_thinNorth_of_vMatches (hz.2 p)

theorem thin_east_two {z : IndexPlane} (hz : ValidIndexPlane z)
    (p : Int × Int) :
    thinAt z (shift p 2 0) = thinAt z p := by
  calc
    thinAt z (shift p 2 0) = phaseEast (thinAt z (shift p 1 0)) := by
      simpa only [shift_shift, Int.reduceAdd] using
        thin_east hz (shift p 1 0)
    _ = phaseEast (phaseEast (thinAt z p)) := by rw [thin_east hz p]
    _ = thinAt z p := phaseEast_involutive _

theorem thin_north_two {z : IndexPlane} (hz : ValidIndexPlane z)
    (p : Int × Int) :
    thinAt z (shift p 0 2) = thinAt z p := by
  calc
    thinAt z (shift p 0 2) = phaseNorth (thinAt z (shift p 0 1)) := by
      simpa only [shift_shift, Int.reduceAdd] using
        thin_north hz (shift p 0 1)
    _ = phaseNorth (phaseNorth (thinAt z p)) := by rw [thin_north hz p]
    _ = thinAt z p := phaseNorth_involutive _

theorem thin_east_even {z : IndexPlane} (hz : ValidIndexPlane z)
    (p : Int × Int) (k : Int) :
    thinAt z (shift p (2 * k) 0) = thinAt z p := by
  have hperiodic : Function.Periodic
      (fun dx : Int => thinAt z (shift p dx 0)) 2 := by
    intro dx
    simpa only [shift_shift, Int.add_zero] using
      thin_east_two hz (shift p dx 0)
  simpa [mul_comm, shift] using hperiodic.int_mul_eq k

theorem thin_north_even {z : IndexPlane} (hz : ValidIndexPlane z)
    (p : Int × Int) (k : Int) :
    thinAt z (shift p 0 (2 * k)) = thinAt z p := by
  have hperiodic : Function.Periodic
      (fun dy : Int => thinAt z (shift p 0 dy)) 2 := by
    intro dy
    simpa only [shift_shift, Int.add_zero] using
      thin_north_two hz (shift p 0 dy)
  simpa [mul_comm, shift] using hperiodic.int_mul_eq k

theorem thin_even {z : IndexPlane} (hz : ValidIndexPlane z)
    (p : Int × Int) (kx ky : Int) :
    thinAt z (shift p (2 * kx) (2 * ky)) = thinAt z p := by
  calc
    thinAt z (shift p (2 * kx) (2 * ky)) =
        thinAt z (shift (shift p (2 * kx) 0) 0 (2 * ky)) := by
      exact congrArg (thinAt z) (shift_even_xy p kx ky)
    _ = thinAt z (shift p (2 * kx) 0) := thin_north_even hz _ ky
    _ = thinAt z p := thin_east_even hz p kx

end Desubstitution
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
