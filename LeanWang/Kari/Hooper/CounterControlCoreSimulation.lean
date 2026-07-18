/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlTraceSimulation
import LeanWang.Kari.Hooper.GlobalSourceLiveness

/-!
# From instruction simulation to Hooper's nested-core laws

This file is the abstract last step of the finite-frame argument.  It does not
depend on how an individual counter instruction is compiled.  Instead it
assumes a one-step implementation law under the shorter-search hypotheses and
turns it into the `CoreGrows` and `CoreResolves` obligations used by Hooper's
two Basic Lemmas.

For the forward direction, fixed nonhalting makes the canonical counter orbit
immortal, so its clock eventually reaches the suspended target distance.  A
finite represented frame cannot still exist then, and hence it must already
have cleaned up.  For the converse, the canonical counter orbit either halts
or is immortal; the two endpoint lemmas handle these cases separately.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCoreSimulation

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlTraceSimulation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Instruction-sized forward semantics, uniformly for every suspended frame
whose shorter searches have already been solved. -/
def ForwardStepLaws (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ {frame : Frame (Symbol numTags) Search},
    (∀ j < frame.distance, (searchSystem base c).Solves j) →
      OneStepGrows base c frame

/-- Halting-aware instruction semantics, uniformly for every suspended frame
whose shorter searches are known to resolve. -/
def ResolvingStepLaws (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ {frame : Frame (Symbol numTags) Search},
    (∀ j < frame.distance, (searchSystem base c).Resolves j) →
      OneStepResolves base c frame

/-- Uniform forward instruction semantics discharges the sole semantic core
obligation of Hooper's forward Basic Lemma. -/
theorem coreGrows_of_forwardStepLaws (base : Nat) (c : Nat.Partrec.Code)
    (hlaws : ForwardStepLaws base c) :
    CoreGrows base c (DominoProblem.FixedNonhalting c) := by
  intro frame concrete hnonhalting hshort hnested
  have hlogical :=
    CounterControlFrameSimulation.logicalFrame_of_nestedAt base c hnested
  have himmortal :=
    GlobalSourceSemantics.fixedNonhalting_immortalFrom hnonhalting
  rcases GlobalSourceLiveness.cycleLaws
      |>.exists_reachable_logical_clock_ge_of_immortalFrom
        himmortal frame.distance with
    ⟨finish, hreach, _hfinishLogical, hclock⟩
  have hboundary := reachesBoundary_of_clock_ge base c
    (hlaws hshort) hreach hclock hlogical
  simpa [ReachesBoundary, searchSystem] using hboundary

/-- Uniform halting-aware instruction semantics discharges the sole semantic
core obligation of Hooper's converse Basic Lemma. -/
theorem coreResolves_of_resolvingStepLaws (base : Nat)
    (c : Nat.Partrec.Code) (hlaws : ResolvingStepLaws base c) :
    CoreResolves base c := by
  intro frame concrete hshort hnested
  have hlogical :=
    CounterControlFrameSimulation.logicalFrame_of_nestedAt base c hnested
  rcases CounterLiveness.haltsFrom_or_immortalFrom
      GlobalSourceProgram.program
      (GlobalSourceSemantics.canonicalCounterCfg c) with
    hhalts | himmortal
  · have hresult := reachesBoundary_or_halts_of_haltsFrom base c
      (hlaws hshort) hhalts hlogical
    simpa [ReachesBoundary, searchSystem] using hresult
  · rcases GlobalSourceLiveness.cycleLaws
        |>.exists_reachable_logical_clock_ge_of_immortalFrom
          himmortal frame.distance with
      ⟨finish, hreach, _hfinishLogical, hclock⟩
    have hresult := reachesBoundary_or_halts_of_clock_ge base c
      (hlaws hshort) hreach hclock hlogical
    simpa [ReachesBoundary, searchSystem] using hresult

end

end CounterControlCoreSimulation
end Hooper
end Kari
end LeanWang
