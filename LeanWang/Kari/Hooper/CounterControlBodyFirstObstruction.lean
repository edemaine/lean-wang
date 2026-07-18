/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitrarySearchMortality
import LeanWang.Kari.Hooper.CounterControlBodyMonotone
import LeanWang.Kari.Hooper.CounterControlCoreRunway
import LeanWang.Kari.Hooper.CounterControlOpenBodyMortality

/-!
# The first obstruction beyond an immortal reconstructed body

An arbitrary controller suffix can reconstruct the finite five-boundary core
without yet locating its first outward target.  If the source machine is
mortal, an infinite blank tail would make the reconstructed instruction body
halt.  Immortality therefore forces a least nonblank obstruction, which
upgrades the reconstructed core to `CoreTargetRepresents` and permits the
common body-continuation theorems to take over.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlBodyFirstObstruction

open Turing CounterMachine CounterProgram
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlCoreFrame
open CounterControlPrefixInstructionResolution
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation CounterControlGuardedParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- An immortal instruction body on a reconstructed core has a finite first
nonblank obstruction beyond the core. -/
theorem exists_coreTarget_of_immortal_body
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (instruction : Instruction)
    (registers : Registers) (T : FullTM0.Tape (Symbol numTags))
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcore : CoreRepresents registers growth T)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (bodyCfg base c growth ⟨source, registers⟩ instruction T)) :
    ∃ limit target,
      CoreTargetRepresents registers growth limit target T := by
  rcases CounterControlCoreRunway.coreOpen_or_firstNonblank hcore with
    hopen | ⟨limit, hbefore, hrunway, hnonblank⟩
  · have hhalts :=
      CounterControlOpenBodyMortality.haltsFrom_body_of_coreOpen
        base c hmortal growth source instruction registers T hrule hopen
    exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        (bodyCfg base c growth ⟨source, registers⟩ instruction T)).mp
          himmortal hhalts)
  · rcases
      CounterControlArbitrarySearchMortality.exists_target_matches_of_ne_blank
        (logicalTape growth T limit) hnonblank with ⟨target, htarget⟩
    exact ⟨limit, target,
      { toCorePrefixRepresents :=
          { toCoreRepresents := hcore
            core_before_limit := hbefore
            runway := hrunway }
        target_matches := htarget }⟩

/-- A genuine search which reaches an immortal reconstructed body strictly
inside its core has the common monotone continuation outcome. -/
theorem foundMonotoneGuardedEntryOutcome_of_reconstructedBody
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (instruction : Instruction)
    (registers : Registers) (T : FullTM0.Tape (Symbol numTags))
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcore : CoreRepresents registers growth T)
    (hbody : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current)
      (bodyCfg base c growth ⟨source, registers⟩ instruction T))
    (hinside : current.distance < layoutEnd registers)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  have himmortalBody := FullTM0.ImmortalFrom.of_reaches himmortal hbody
  rcases exists_coreTarget_of_immortal_body base c hmortal growth source
      instruction registers T hrule hcore himmortalBody with
    ⟨limit, target, represented⟩
  exact CounterControlBodyMonotone.foundMonotoneGuardedEntryOutcome_of_body
    base c hmortal current growth source instruction registers limit target T
    hrule represented hbody hinside himmortal

/-- The same first-obstruction reduction with the extra one-cell guard gives
the strict guarded escape outcome. -/
theorem foundGuardedEscapeOutcome_of_reconstructedBody
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (instruction : Instruction)
    (registers : Registers) (T : FullTM0.Tape (Symbol numTags))
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcore : CoreRepresents registers growth T)
    (hbody : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      (bodyCfg base c growth ⟨source, registers⟩ instruction T))
    (hinside : current.current.distance + 1 < layoutEnd registers)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedEscapeOutcome current) := by
  have himmortalBody := FullTM0.ImmortalFrom.of_reaches himmortal hbody
  rcases exists_coreTarget_of_immortal_body base c hmortal growth source
      instruction registers T hrule hcore himmortalBody with
    ⟨limit, target, represented⟩
  exact CounterControlBodyMonotone.foundGuardedEscapeOutcome_of_body
    base c hmortal current growth source instruction registers limit target T
    hrule represented hbody hinside himmortal

end

end CounterControlBodyFirstObstruction
end Hooper
end Kari
end LeanWang
