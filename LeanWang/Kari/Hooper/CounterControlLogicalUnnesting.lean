/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlPrefixInstructionResolution
import LeanWang.Kari.Hooper.CounterControlCleanupResume
import LeanWang.Kari.Hooper.CounterControlValidationRoundtrip

/-!
# Unnesting an immortal bounded logical core

Validation reconstructs a tag-free counter core and its first outward
obstruction.  The finite-prefix semantics then follows the abstract counter
computation until that obstruction is hit and the core is erased.  On an
immortal concrete orbit, the shared return dispatcher must recognize a real
generated command, so cleanup reaches the exact resumed search.

This file composes those three layers without forgetting the tape geometry.
In particular, both the initial and collision-time core ends lie no farther
out than the resumed gap.  The separate parent-embedding argument is what
turns this non-strict bound into Hooper's strict growth across nesting levels.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlLogicalUnnesting

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlCoreFrame CounterControlCleanupSemantics
open CounterControlPrefixInstructionResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private theorem immortalFrom_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {start finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start finish) :
    FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) finish := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-- Every immortal bounded logical configuration with mortal designated
source reaches the generated search selected after exact tag-free cleanup.

The existential data retains both represented cores and the common first
obstruction `limit`.  This is the geometry needed by the later nesting-level
comparison; ordinary global-frontier normalization would forget it. -/
theorem reaches_resumed_search_of_immortal_logical
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat)
    (hsource : source < logicalSpan)
    (logical : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source, logical⟩) :
    ∃ (initialRegisters : Registers)
        (initialTape : FullTM0.Tape (Symbol numTags))
        (limit : Nat) (target : Target numTags),
      CoreTargetRepresents initialRegisters growth limit target initialTape ∧
      logical = atLogical growth initialTape (layoutEnd initialRegisters) ∧
      ∃ (collisionRegisters : Registers)
          (collisionTape : FullTM0.Tape (Symbol numTags))
          (hcollision : CoreTargetRepresents collisionRegisters growth limit
            target collisionTape),
        let spec := prefixSpec collisionRegisters growth limit target
          hcollision.core_before_limit
        ∃ (search : Search) (distance : Nat),
          FullTM0.Reaches (CounterControlNestingBridge.machine base c)
              ⟨logicalState base c growth source, logical⟩
              ((searchSystem base c).startCfg search
                ((afterTag spec collisionTape).move growth)) ∧
            (command base c search).searchDirection = growth ∧
            SearchGap (fun symbol => symbol = blankSymbol)
              (command base c search).target.Matches
              ((afterTag spec collisionTape).move growth) growth distance ∧
            distance = limit - 1 ∧
            layoutEnd initialRegisters ≤ distance ∧
            layoutEnd collisionRegisters ≤ distance := by
  rcases CounterControlValidationRoundtrip.logical_reconstructs_coreTarget_fields_of_immortal
      base c hmortal growth source hsource logical himmortal with
    ⟨instruction, initialRegisters, initialTape, limit, target,
      _hrule, hcore, hbefore, hrunway, htarget, hcenter, _hbody⟩
  have hinitial : CoreTargetRepresents initialRegisters growth limit target
      initialTape := by
    exact ⟨⟨hcore, hbefore, hrunway⟩, htarget⟩
  let frame : PrefixEnvelope := ⟨growth, limit, target⟩
  let abstract : CounterMachine.Cfg := ⟨source, initialRegisters⟩
  have hlogical : PrefixLogical base c frame abstract
      ⟨logicalState base c growth source, logical⟩ := by
    refine .intro initialTape hinitial ?_ hsource
    simp [prefixLogicalCfg, frame, abstract, hcenter]
  rcases prefix_return_or_halts base c frame hlogical with
    hreturn | hhalts
  · rcases hreturn with
      ⟨collisionRegisters, collisionTape, hcollision, hcollisionBound,
        hreturn⟩
    let spec := prefixSpec collisionRegisters growth limit target
      hcollision.core_before_limit
    have himmortalReturn : FullTM0.ImmortalFrom
        (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c growth,
          atLogical growth (afterZero spec collisionTape) 0⟩ := by
      apply immortalFrom_of_reaches base c himmortal
      simpa [frame, spec] using hreturn
    rcases CounterControlCleanupResume.reaches_resumed_search_at_first_obstruction_sub_one
        base c hmortal (spec := spec) (T := collisionTape)
        hcollision.toCorePrefixRepresents.toCoreRepresents
        hcollision.toCorePrefixRepresents.runway
        hcollision.target_matches himmortalReturn with
      ⟨search, distance, hresume, hdirection, hgap, hdistance⟩
    have hreturn' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source, logical⟩
        ⟨controllerReturn base c growth,
          atLogical growth (afterZero spec collisionTape) 0⟩ := by
      simpa [frame, spec] using hreturn
    have hdistanceLimit : distance = limit - 1 := by
      simpa [spec, prefixSpec] using hdistance
    refine ⟨initialRegisters, initialTape, limit, target, hinitial,
      hcenter, collisionRegisters, collisionTape, hcollision, ?_⟩
    dsimp only
    refine ⟨search, distance, ?_, hdirection, hgap, hdistanceLimit, ?_, ?_⟩
    · exact hreturn'.trans hresume
    · omega
    · rw [hdistanceLimit]
      simpa [frame] using hcollisionBound
  · exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source, logical⟩).mp
          himmortal hhalts)

end

end CounterControlLogicalUnnesting
end Hooper
end Kari
end LeanWang
