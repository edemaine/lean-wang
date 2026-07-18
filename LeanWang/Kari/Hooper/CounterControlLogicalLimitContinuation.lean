/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation

/-!
# Continuing through a logical core by its outer limit

Some leftward callers, notably increment shifts, can start beyond the small
five-boundary counter layout.  They therefore need not be contained in
`layoutEnd`.  A reconstructed finite core retains a stronger outer fact: its
first obstruction is at `limit`, and exact cleanup resumes a guarded caller
with distance `limit - 1`.  This file packages direct outcome constructors
using that comparison.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlLogicalLimitContinuation

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation CounterControlParentEmbedding
open CounterControlGuardedResume CounterControlGuardedParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- If a guarded caller lies before a reconstructed core's first obstruction,
cleaning that core gives the required strict guarded parent continuation even
when the caller is not inside the five-boundary layout. -/
theorem foundGuardedParentOutcome_of_logicalLimit
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (core : LogicalCore base c)
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current) core.cfg)
    (hdistance : current.current.distance < core.limit - 1)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedParentOutcome current) := by
  have himmortalCore := FullTM0.ImmortalFrom.of_reaches himmortal hreach
  rcases core.reaches_resumed_of_immortal base c hmortal himmortalCore with
    ⟨resumed⟩
  let next : GuardedSearch base c :=
    CounterControlGuardedResume.PrefixResumedSearch.toGuardedSearch resumed
  refine ⟨.nextSearch next (hreach.trans resumed.reaches) ?_⟩
  change current.current.distance < resumed.next.distance
  have hdistance' : resumed.next.distance = core.limit - 1 := by
    simpa [LogicalCore.frame] using resumed.distance_eq
  rw [hdistance']
  exact hdistance

/-- Escape-sum wrapper for the strict parent continuation supplied by a
logical limit. -/
theorem foundGuardedEscapeOutcome_of_logicalLimit
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (core : LogicalCore base c)
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current) core.cfg)
    (hdistance : current.current.distance < core.limit - 1)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedEscapeOutcome current) := by
  rcases foundGuardedParentOutcome_of_logicalLimit base c hmortal current
      core hreach hdistance himmortal with ⟨outcome⟩
  exact ⟨.parent outcome⟩

/-- Weak-comparison counterpart for an arbitrary first genuine caller. -/
theorem foundMonotoneGuardedEntryOutcome_of_logicalLimit
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (core : LogicalCore base c)
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current) core.cfg)
    (hdistance : current.distance ≤ core.limit - 1)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  have himmortalCore := FullTM0.ImmortalFrom.of_reaches himmortal hreach
  rcases core.reaches_resumed_of_immortal base c hmortal himmortalCore with
    ⟨resumed⟩
  let next : GuardedSearch base c :=
    CounterControlGuardedResume.PrefixResumedSearch.toGuardedSearch resumed
  refine ⟨.nextSearch next (hreach.trans resumed.reaches) ?_⟩
  change current.distance ≤ resumed.next.distance
  have hdistance' : resumed.next.distance = core.limit - 1 := by
    simpa [LogicalCore.frame] using resumed.distance_eq
  rw [hdistance']
  exact hdistance

end

end CounterControlLogicalLimitContinuation
end Hooper
end Kari
end LeanWang
