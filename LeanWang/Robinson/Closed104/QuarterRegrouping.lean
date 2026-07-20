/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.Quarters

/-!
# Regrouping corrected quarter tiles

The generic tile subdivision marks each quarter with its quadrant.  Matching
edges force those quadrant labels into a period-two checkerboard, so every
valid quarter plane has a southwest origin and a unique global `2 x 2`
alignment.  Internal subdivision colors then force all four quarters in an
aligned block to come from the same corrected Ollinger tile.

`macroPlane` reads that common parent.  `block_spec` is the main result of this
module: it reconstructs the four quarter tiles at every macro coordinate.
`QuarterPlaneDecode` uses the remaining, external edges of these blocks to
prove that the reconstructed parent plane is Wang-valid.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace QuarterRegrouping

open Desubstitution ParentPlane Quarters

abbrev QuarterPlane := Int × Int → QuarterIndex

def ValidQuarterPlane (z : QuarterPlane) : Prop :=
  (∀ p : Int × Int,
      WangTile.HMatches (quarterTile (z p))
        (quarterTile (z (p.1 + 1, p.2)))) ∧
    ∀ p : Int × Int,
      WangTile.VMatches (quarterTile (z p))
        (quarterTile (z (p.1, p.2 + 1)))

def phaseAt (z : QuarterPlane) (p : Int × Int) : Quadrant :=
  (z p).2

theorem phase_east {z : QuarterPlane} (hz : ValidQuarterPlane z)
    (p : Int × Int) :
    phaseAt z (shift p 1 0) = Quarters.phaseEast (phaseAt z p) := by
  simpa only [phaseAt, shift, Int.add_zero] using
    phase_eq_east_of_hMatches (hz.1 p)

theorem phase_north {z : QuarterPlane} (hz : ValidQuarterPlane z)
    (p : Int × Int) :
    phaseAt z (shift p 0 1) = Quarters.phaseNorth (phaseAt z p) := by
  simpa only [phaseAt, shift, Int.add_zero] using
    phase_eq_north_of_vMatches (hz.2 p)

theorem phase_east_two {z : QuarterPlane} (hz : ValidQuarterPlane z)
    (p : Int × Int) :
    phaseAt z (shift p 2 0) = phaseAt z p := by
  calc
    phaseAt z (shift p 2 0) = Quarters.phaseEast (phaseAt z (shift p 1 0)) := by
      simpa only [shift_shift, Int.reduceAdd] using phase_east hz (shift p 1 0)
    _ = Quarters.phaseEast (Quarters.phaseEast (phaseAt z p)) := by
      rw [phase_east hz p]
    _ = phaseAt z p := Quarters.phaseEast_involutive _

theorem phase_north_two {z : QuarterPlane} (hz : ValidQuarterPlane z)
    (p : Int × Int) :
    phaseAt z (shift p 0 2) = phaseAt z p := by
  calc
    phaseAt z (shift p 0 2) = Quarters.phaseNorth (phaseAt z (shift p 0 1)) := by
      simpa only [shift_shift, Int.reduceAdd] using phase_north hz (shift p 0 1)
    _ = Quarters.phaseNorth (Quarters.phaseNorth (phaseAt z p)) := by
      rw [phase_north hz p]
    _ = phaseAt z p := Quarters.phaseNorth_involutive _

theorem phase_east_even {z : QuarterPlane} (hz : ValidQuarterPlane z)
    (p : Int × Int) (k : Int) :
    phaseAt z (shift p (2 * k) 0) = phaseAt z p := by
  have hperiodic : Function.Periodic
      (fun dx : Int => phaseAt z (shift p dx 0)) 2 := by
    intro dx
    simpa only [shift_shift, Int.add_zero] using
      phase_east_two hz (shift p dx 0)
  simpa [mul_comm, shift] using hperiodic.int_mul_eq k

theorem phase_north_even {z : QuarterPlane} (hz : ValidQuarterPlane z)
    (p : Int × Int) (k : Int) :
    phaseAt z (shift p 0 (2 * k)) = phaseAt z p := by
  have hperiodic : Function.Periodic
      (fun dy : Int => phaseAt z (shift p 0 dy)) 2 := by
    intro dy
    simpa only [shift_shift, Int.add_zero] using
      phase_north_two hz (shift p 0 dy)
  simpa [mul_comm, shift] using hperiodic.int_mul_eq k

theorem phase_even {z : QuarterPlane} (hz : ValidQuarterPlane z)
    (p : Int × Int) (kx ky : Int) :
    phaseAt z (shift p (2 * kx) (2 * ky)) = phaseAt z p := by
  calc
    phaseAt z (shift p (2 * kx) (2 * ky)) =
        phaseAt z (shift (shift p (2 * kx) 0) 0 (2 * ky)) := by
      exact congrArg (phaseAt z) (shift_even_xy p kx ky)
    _ = phaseAt z (shift p (2 * kx) 0) := phase_north_even hz _ ky
    _ = phaseAt z p := phase_east_even hz p kx

theorem exists_southwest_origin {z : QuarterPlane} (hz : ValidQuarterPlane z) :
    ∃ origin : Int × Int, phaseAt z origin = .southwest := by
  let p : Int × Int := (0, 0)
  cases hphase : phaseAt z p with
  | southwest => exact ⟨p, hphase⟩
  | southeast =>
      exact ⟨shift p 1 0, (phase_east hz p).trans (by rw [hphase]; rfl)⟩
  | northwest =>
      exact ⟨shift p 0 1, (phase_north hz p).trans (by rw [hphase]; rfl)⟩
  | northeast =>
      refine ⟨shift p 1 1, ?_⟩
      calc
        phaseAt z (shift p 1 1) =
            Quarters.phaseNorth (phaseAt z (shift p 1 0)) := by
          simpa only [shift_shift, Int.reduceAdd] using
            phase_north hz (shift p 1 0)
        _ = Quarters.phaseNorth (Quarters.phaseEast (phaseAt z p)) := by
          rw [phase_east hz p]
        _ = .southwest := by rw [hphase]; rfl

/- The phase checkerboard fixes where blocks lie.  The next two lemmas use the
private internal subdivision colors to show that adjacent quarters inside one
such block also share the same parent index. -/

theorem parentTile_injective :
    Function.Injective (fun index : Index => tile (components index)) := by
  intro left right heq
  have hquarter : quarterTile (left, .southwest) =
      quarterTile (right, .southwest) := by
    exact congrArg (fun wang =>
      TileSubdivision.subdivideTileAt wang .southwest) heq
  exact congrArg Prod.fst (quarterTile_injective hquarter)

theorem parent_eq_of_internal_hMatch
    {left right : QuarterIndex}
    (hleft : left.2 = .southwest ∨ left.2 = .northwest)
    (hmatch : WangTile.HMatches (quarterTile left) (quarterTile right)) :
    left.1 = right.1 := by
  have hallowed := (TileSubdivision.hMatches_subdivideTileAt_iff
    (tile (components left.1)) (tile (components right.1)) left.2 right.2).1 hmatch
  have hright := phase_eq_east_of_hMatches hmatch
  rcases left with ⟨left, leftQuadrant⟩
  rcases right with ⟨right, rightQuadrant⟩
  rcases hleft with hleft | hleft
  · change leftQuadrant = .southwest at hleft
    subst leftQuadrant
    change rightQuadrant = Quarters.phaseEast .southwest at hright
    have hright' : rightQuadrant = .southeast := by
      simpa [Quarters.phaseEast] using hright
    subst rightQuadrant
    exact parentTile_injective hallowed
  · change leftQuadrant = .northwest at hleft
    subst leftQuadrant
    change rightQuadrant = Quarters.phaseEast .northwest at hright
    have hright' : rightQuadrant = .northeast := by
      simpa [Quarters.phaseEast] using hright
    subst rightQuadrant
    exact parentTile_injective hallowed

theorem parent_eq_of_internal_vMatch
    {lower upper : QuarterIndex}
    (hlower : lower.2 = .southwest ∨ lower.2 = .southeast)
    (hmatch : WangTile.VMatches (quarterTile lower) (quarterTile upper)) :
    lower.1 = upper.1 := by
  have hallowed := (TileSubdivision.vMatches_subdivideTileAt_iff
    (tile (components lower.1)) (tile (components upper.1)) lower.2 upper.2).1 hmatch
  have hupper := phase_eq_north_of_vMatches hmatch
  rcases lower with ⟨lower, lowerQuadrant⟩
  rcases upper with ⟨upper, upperQuadrant⟩
  rcases hlower with hlower | hlower
  · change lowerQuadrant = .southwest at hlower
    subst lowerQuadrant
    change upperQuadrant = Quarters.phaseNorth .southwest at hupper
    have hupper' : upperQuadrant = .northwest := by
      simpa [Quarters.phaseNorth] using hupper
    subst upperQuadrant
    exact parentTile_injective hallowed
  · change lowerQuadrant = .southeast at hlower
    subst lowerQuadrant
    change upperQuadrant = Quarters.phaseNorth .southeast at hupper
    have hupper' : upperQuadrant = .northeast := by
      simpa [Quarters.phaseNorth] using hupper
    subst upperQuadrant
    exact parentTile_injective hallowed

def macroPlane (z : QuarterPlane) (origin : Int × Int) : IndexPlane :=
  fun k => (z (blockOrigin origin k)).1

/-- Exact four-quarter decomposition of every selected macrocell. -/
theorem block_spec {z : QuarterPlane} (hz : ValidQuarterPlane z)
    {origin : Int × Int} (horigin : phaseAt z origin = .southwest)
    (k : Int × Int) :
    z (blockOrigin origin k) = (macroPlane z origin k, .southwest) ∧
      z (shift (blockOrigin origin k) 1 0) =
        (macroPlane z origin k, .southeast) ∧
      z (shift (blockOrigin origin k) 0 1) =
        (macroPlane z origin k, .northwest) ∧
      z (shift (blockOrigin origin k) 1 1) =
        (macroPlane z origin k, .northeast) := by
  have hphase : phaseAt z (blockOrigin origin k) = .southwest := by
    exact (phase_even hz origin k.1 k.2).trans horigin
  have heast := phase_east hz (blockOrigin origin k)
  have hnorth := phase_north hz (blockOrigin origin k)
  have hnortheast := phase_east hz (shift (blockOrigin origin k) 0 1)
  have heastPhase : phaseAt z (shift (blockOrigin origin k) 1 0) =
      .southeast := by
    rw [heast, hphase]
    rfl
  have hnorthPhase : phaseAt z (shift (blockOrigin origin k) 0 1) =
      .northwest := by
    rw [hnorth, hphase]
    rfl
  have hnortheastPhase : phaseAt z (shift (blockOrigin origin k) 1 1) =
      .northeast := by
    have hnortheast' : phaseAt z (shift (blockOrigin origin k) 1 1) =
        Quarters.phaseEast
          (phaseAt z (shift (blockOrigin origin k) 0 1)) := by
      simpa only [shift_shift, Int.reduceAdd] using hnortheast
    rw [hnortheast', hnorthPhase]
    rfl
  have hparentEast := parent_eq_of_internal_hMatch (Or.inl hphase)
    (hz.1 (blockOrigin origin k))
  have hparentNorth := parent_eq_of_internal_vMatch (Or.inl hphase)
    (hz.2 (blockOrigin origin k))
  have hparentNortheast := parent_eq_of_internal_hMatch
    (Or.inr hnorthPhase)
    (hz.1 (shift (blockOrigin origin k) 0 1))
  have hparentEast' :
      (z (shift (blockOrigin origin k) 1 0)).1 = macroPlane z origin k := by
    simpa only [shift, Int.add_zero, macroPlane] using hparentEast.symm
  have hparentNorth' :
      (z (shift (blockOrigin origin k) 0 1)).1 = macroPlane z origin k := by
    simpa only [shift, Int.add_zero, macroPlane] using hparentNorth.symm
  have hparentNortheast' :
      (z (shift (blockOrigin origin k) 1 1)).1 =
        (z (shift (blockOrigin origin k) 0 1)).1 := by
    simpa only [shift, Int.add_zero, add_assoc] using hparentNortheast.symm
  refine ⟨Prod.ext rfl hphase, ?_⟩
  constructor
  · apply Prod.ext
    · exact hparentEast'
    · exact heastPhase
  constructor
  · apply Prod.ext
    · exact hparentNorth'
    · exact hnorthPhase
  · apply Prod.ext
    · exact hparentNortheast'.trans hparentNorth'
    · exact hnortheastPhase

end QuarterRegrouping
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
