/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlInstructionResolution
import LeanWang.Kari.Hooper.CounterControlTraceSimulation
import LeanWang.Kari.Hooper.GlobalSourceMortality

/-!
# Resolving counter traces inside a uniformly large frame

The general resolving instruction law permits an outward increment to collide
with the suspended target.  Along a fixed finite abstract trace, a simple
layout bound excludes that outcome.  This file packages the resulting
room-conditional one-step law and applies it to the designated mortal source
run, producing one uniform size beyond which every canonical nested frame
halts instead of cleaning up.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlRoomResolution

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlFrameBacking CounterControlFrameSimulation
open CounterControlInstructionResolution CounterControlSearchResolution
open CounterControlTraceSimulation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- If the supplied abstract successor still fits strictly inside the saved
target, the collision alternative of the uniform resolving instruction API
is impossible. -/
theorem roomStepContinuesOrHalts
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (hshort : ShortResolves base c frame.distance) :
    RoomStepContinuesOrHalts base c frame := by
  intro current next concrete hstep hnextRoom hlogical
  rcases hlogical with
    ⟨hcore, T, hback, rfl, _hstate, hframe⟩
  let spec := activeSpec base c frame current.registers hcore
  change BackedBy spec T frame.outer at hback
  have hrun := machine_resolves_counterStep base c current next
    (spec := spec) hback (by simp [spec]) hstep
    (by simpa [spec] using hshort)
  rcases hrun with hnext | hcollision | hhalts
  · rcases hnext with ⟨hnextCore, nextTape, hreach, hnextBack⟩
    have hnextCore' : layoutEnd next.registers < frame.distance := by
      simpa [spec] using hnextCore
    have hnextBack' : BackedBy
        (activeSpec base c frame next.registers hnextCore')
        nextTape frame.outer := by
      simpa [spec, activeSpec, updateSpec] using hnextBack
    let nextConcrete := logicalCfg base c frame next nextTape
    have hnextFrame : LogicalFrame base c frame next nextConcrete := by
      exact ⟨hnextCore', nextTape, hnextBack', rfl,
        CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep,
        hframe⟩
    left
    refine ⟨nextConcrete, ?_, hnextFrame⟩
    simpa [nextConcrete, logicalCfg, spec, activeSpec] using hreach
  · rcases hcollision with
      ⟨register, target, hrule, hcollision, _hcollisionReach⟩
    have hlookup : CounterMachine.lookupInstruction
        GlobalSourceProgram.program current.state =
        some (.increment register target) :=
      (CounterProgram.lookupInstruction_eq_some_iff_of_deterministic
        GlobalSourceProgram.program_deterministic).2 hrule
    have hnextEq : next =
        ⟨target, current.registers.increment register⟩ := by
      rw [CounterMachine.step, hlookup] at hstep
      exact (Option.some.inj hstep).symm
    subst next
    have hhit : layoutEnd (current.registers.increment register) =
        frame.distance := by
      rw [layoutEnd_increment]
      simpa [spec, activeSpec] using hcollision
    exact False.elim (Nat.ne_of_lt hnextRoom hhit)
  · right
    simpa [logicalCfg, spec, activeSpec] using hhalts

/-- When the designated source computation is mortal, one finite bound works
for every genuine canonical frame: beyond that bound the compiled core halts,
provided all shorter searches resolve. -/
theorem exists_bound_halts_nested
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    ∃ bound : Nat,
      ∀ {frame : Frame (Symbol numTags) Search}
          {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State},
        bound < frame.distance →
        ShortResolves base c frame.distance →
        NestedAt base c frame concrete →
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          concrete := by
  rcases GlobalSourceMortality.not_fixedNonhalting_haltsFrom hmortal with
    ⟨terminal, hreach, hterminal⟩
  rcases Dynamics.exists_iterate_eq_some_of_reaches hreach with
    ⟨steps, hrun⟩
  let start := GlobalSourceSemantics.canonicalCounterCfg c
  refine ⟨layoutEnd start.registers + steps, ?_⟩
  intro frame concrete hlarge hshort hnested
  have hlogical := logicalFrame_of_nestedAt base c hnested
  apply haltsFrom_of_terminal_iterate_of_room base c
    (roomStepContinuesOrHalts base c frame hshort) steps hrun hterminal
    hlarge hlogical

end

end CounterControlRoomResolution
end Hooper
end Kari
end LeanWang
