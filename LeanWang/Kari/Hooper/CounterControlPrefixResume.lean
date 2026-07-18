/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlPrefixInstructionResolution
import LeanWang.Kari.Hooper.CounterControlCleanupResume

/-!
# Level-aware resumed searches from finite counter prefixes

`PrefixReachesReturn` retains the collision-time tag-free core and the exact
shared-return tape.  `CounterControlCleanupResume` identifies the generated
search selected by an immortal return and proves that its gap is the old
first-obstruction distance minus one.  This file composes the two endpoints
without forgetting the enclosing prefix limit.

The resulting `PrefixResumedSearch` is deliberately richer than a bare
`GenuineSearch`: it remembers the represented collision-time core, the exact
cleaned outer tape, and `next.distance = frame.limit - 1`.  Those fields are
the level witness needed to compare a resumed caller with searches embedded
strictly inside the next reconstructed core.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlPrefixResume

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlCoreFrame CounterControlCleanupSemantics
open CounterControlPrefixInstructionResolution
open CounterControlGlobalUnnesting

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- A resumed generated caller together with the collision-time prefix whose
cleanup exposed it. -/
structure PrefixResumedSearch
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : PrefixEnvelope)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) where
  registers : Registers
  tape : FullTM0.Tape (Symbol numTags)
  represented : CoreTargetRepresents registers frame.growth frame.limit
    frame.target tape
  coreEnd_le : layoutEnd registers ≤ frame.limit - 1
  next : GenuineSearch base c
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    start next.cfg
  direction_eq :
    (command base c next.search).searchDirection = frame.growth
  outer_eq : next.outer =
    (afterTag
      (prefixSpec registers frame.growth frame.limit frame.target
        represented.core_before_limit) tape).move frame.growth
  distance_eq : next.distance = frame.limit - 1

namespace PrefixResumedSearch

theorem coreEnd_le_distance
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (h : PrefixResumedSearch base c frame start) :
    layoutEnd h.registers ≤ h.next.distance := by
  rw [h.distance_eq]
  exact h.coreEnd_le

/-- A triggering search strictly inside the reconstructed core is strictly
smaller than the resumed caller retained by `PrefixResumedSearch`. -/
theorem clearedPrefixUnnests
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {current : GenuineSearch base c}
    (h : PrefixResumedSearch base c frame current.cfg)
    (hinside : current.distance < layoutEnd h.registers) :
    ClearedPrefixUnnests current h.next := by
  exact ⟨h.reaches, hinside.trans_le h.coreEnd_le_distance⟩

end PrefixResumedSearch

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

/-- Exact return cleanup followed by immortal tag dispatch produces a
level-aware resumed generated search. -/
theorem PrefixReachesReturn.resumes_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hreturn : PrefixReachesReturn base c frame start)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    Nonempty (PrefixResumedSearch base c frame start) := by
  rcases hreturn with ⟨registers, T, h, hcoreEnd, hreturn⟩
  let spec := prefixSpec registers frame.growth frame.limit frame.target
    h.core_before_limit
  let returnCfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
    ⟨controllerReturn base c frame.growth,
      atLogical frame.growth (afterZero spec T) 0⟩
  have himmortalReturn : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) returnCfg :=
    immortalFrom_of_reaches base c himmortal
      (by simpa [returnCfg, spec] using hreturn)
  have hcore : CoreRepresents spec.registers spec.growth T := by
    change CoreRepresents registers frame.growth T
    exact h.toCorePrefixRepresents.toCoreRepresents
  have hrunway : ∀ position, layoutEnd spec.registers < position →
      position < spec.outerDistance →
        logicalTape spec.growth T position = blankSymbol := by
    change ∀ position, layoutEnd registers < position →
      position < frame.limit →
        logicalTape frame.growth T position = blankSymbol
    exact h.toCorePrefixRepresents.runway
  have htarget : spec.outerTarget.Matches
      (logicalTape spec.growth T spec.outerDistance) := by
    change frame.target.Matches
      (logicalTape frame.growth T frame.limit)
    exact h.target_matches
  have himmortalReturn' : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c spec.growth,
        atLogical spec.growth (afterZero spec T) 0⟩ := by
    change FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) returnCfg
    exact himmortalReturn
  rcases CounterControlCleanupResume.reaches_resumed_search_at_first_obstruction_sub_one
      base c hmortal (spec := spec) (T := T) hcore hrunway htarget
      himmortalReturn' with
    ⟨search, distance, hresume, hdirection, hgap, hdistance⟩
  let outer := (afterTag spec T).move spec.growth
  let next : GenuineSearch base c := {
    search := search
    outer := outer
    distance := distance
    gap := by
      rw [hdirection]
      simpa [outer] using hgap }
  refine ⟨{
    registers := registers
    tape := T
    represented := h
    coreEnd_le := hcoreEnd
    next := next
    reaches := ?_
    direction_eq := by
      change (command base c search).searchDirection = spec.growth
      exact hdirection
    outer_eq := by rfl
    distance_eq := hdistance }⟩
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    start ((searchSystem base c).startCfg search outer)
  exact hreturn.trans hresume

/-- Any represented logical prefix on an immortal concrete orbit reaches a
level-aware resumed caller.  The finite-prefix totality theorem supplies the
return-or-halt dichotomy; immortality removes the halt branch. -/
theorem prefixLogical_reaches_resumedSearch_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (frame : PrefixEnvelope)
    {abstract : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : PrefixLogical base c frame abstract concrete)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) concrete) :
    Nonempty (PrefixResumedSearch base c frame concrete) := by
  rcases prefix_return_or_halts base c frame hlogical with
    hreturn | hhalts
  · exact PrefixReachesReturn.resumes_of_immortal
      base c hmortal hreturn himmortal
  · exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c) concrete).mp
          himmortal hhalts)

/-- Direct wrapper for a concrete canonical logical configuration. -/
theorem reaches_resumedSearch_from_prefixLogicalCfg_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (frame : PrefixEnvelope)
    (abstract : CounterMachine.Cfg)
    (T : FullTM0.Tape (Symbol numTags))
    (h : CoreTargetRepresents abstract.registers frame.growth frame.limit
      frame.target T)
    (hstate : abstract.state < logicalSpan)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (prefixLogicalCfg base c frame abstract T)) :
    Nonempty (PrefixResumedSearch base c frame
      (prefixLogicalCfg base c frame abstract T)) := by
  apply prefixLogical_reaches_resumedSearch_of_immortal
    base c hmortal frame (abstract := abstract)
  · exact ⟨T, h, rfl, hstate⟩
  · exact himmortal

end


end CounterControlPrefixResume
end Hooper
end Kari
end LeanWang
