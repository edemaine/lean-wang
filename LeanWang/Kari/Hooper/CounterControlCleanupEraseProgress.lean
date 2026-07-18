/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlFiniteConverse

/-!
# Immortal progress through one generated erasing search

The converse Basic Lemma resolves every finite generated search either to its
exact found state or to a terminal configuration.  For an erasing boundary
command, the command continuation then clears the found boundary and performs
its optional departure exactly once.

This file packages the resulting one-command fact under immortality.  It is
independent of the four-command collision-cleanup chain and can therefore be
used at any generated erasing search entry.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCleanupEraseProgress

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlSearchResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- An immortal generated erasing boundary search reaches its exact
erase-and-depart endpoint.  No a priori search bound is needed: global finite
resolution supplies `ShortResolves` at `distance + 1`, and immortality
eliminates the halting alternative. -/
theorem machine_reaches_boundary_erase_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (departure : Option Turing.Dir)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      (.erase departure) ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth direction) distance)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩
      ⟨resolve base c success,
        match departure with
        | none =>
            (outer.moveN (orient address.growth direction) distance).write
              blankSymbol
        | some departure =>
            ((outer.moveN (orient address.growth direction) distance).write
              blankSymbol).move (orient address.growth departure)⟩ := by
  let limit := distance + 1
  have hshort : ShortResolves base c limit := by
    intro shorter _hshorter
    exact CounterControlFiniteConverse.resolves_all base c shorter
  have hdistance : distance < limit := by
    simp [limit]
  rcases CounterControlInstructionResolution.machine_reaches_boundary_erase_or_halts
      base c limit hshort address expected direction success departure hraw
      outer distance hdistance hgap with hreach | hhalts
  · exact hreach
  · exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩).mp himmortal hhalts)

end

end CounterControlCleanupEraseProgress
end Hooper
end Kari
end LeanWang
