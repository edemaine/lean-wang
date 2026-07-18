/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlPrefixInstructionResolution
import LeanWang.Kari.Hooper.CounterControlCoreEnvelope
import LeanWang.Kari.Hooper.CounterControlTargetUniqueness
import LeanWang.Kari.Hooper.CounterControlSearchSystem

/-!
# Recovering a suspended search frame from a tag-free prefix

Finite-prefix resolution initially leaves logical coordinate `0`
unconstrained.  Once the shared return dispatcher identifies that symbol as
the tag of a real generated search, the same prefix is no longer merely
tag-free: it is an exact represented frame backed by its cleanup tape.

This module isolates that upgrade.  It does not assume that the recorded gap
is already beyond the private scan radius; when that additional inequality is
available, the recovered search envelope is a genuine `FrameWellFormed`.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlRecoveredFrame

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlCoreFrame CounterControlFrameBacking
open CounterControlCleanupSemantics
open CounterControlPrefixInstructionResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The real frame specification obtained after identifying coordinate `0`
as the tag of `search`. -/
def recoveredSpec (search : Search) (registers : Registers)
    (growth : Turing.Dir) (limit : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < limit) : Spec numTags where
  growth := growth
  returnTag := search
  registers := registers
  outerDistance := limit
  outerTarget := target
  core_before_target := hcore

/-- Erasing the recovered represented frame exposes its exact backing tape. -/
def recoveredOuter (search : Search) (registers : Registers)
    (growth : Turing.Dir) (limit : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < limit)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  cleanupTape (recoveredSpec search registers growth limit target hcore) T

/-- The suspended search envelope named by the recovered return tag. -/
def recoveredFrame (search : Search) (registers : Registers)
    (growth : Turing.Dir) (limit : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < limit)
    (T : FullTM0.Tape (Symbol numTags)) :
    Frame (Symbol numTags) Search :=
  ⟨search, recoveredOuter search registers growth limit target hcore T,
    limit⟩

@[simp] theorem recoveredSpec_returnTag
    (search : Search) (registers : Registers) (growth : Turing.Dir)
    (limit : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < limit) :
    (recoveredSpec search registers growth limit target hcore).returnTag =
      search := rfl

@[simp] theorem recoveredFrame_saved
    (search : Search) (registers : Registers) (growth : Turing.Dir)
    (limit : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < limit)
    (T : FullTM0.Tape (Symbol numTags)) :
    (recoveredFrame search registers growth limit target hcore T).saved =
      search := rfl

@[simp] theorem recoveredFrame_distance
    (search : Search) (registers : Registers) (growth : Turing.Dir)
    (limit : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < limit)
    (T : FullTM0.Tape (Symbol numTags)) :
    (recoveredFrame search registers growth limit target hcore T).distance =
      limit := rfl

/-- Boundary cleanup never touches the tag coordinate `0`. -/
theorem logicalTape_afterZero_zero {spec : Spec numTags}
    (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape spec.growth (afterZero spec T) (0 : Nat) =
      logicalTape spec.growth T (0 : Nat) := by
  simp only [afterZero, afterOne, afterTwo, afterThree, afterFour,
    clearBoundary]
  rw [writeLogical_of_ne spec.growth _
    (boundaryOffset spec.registers 0) 0 blankSymbol (by
      simp only [boundaryOffset]
      omega)]
  rw [writeLogical_of_ne spec.growth _
    (boundaryOffset spec.registers 1) 0 blankSymbol (by
      simp only [boundaryOffset]
      omega)]
  rw [writeLogical_of_ne spec.growth _
    (boundaryOffset spec.registers 2) 0 blankSymbol (by
      simp only [boundaryOffset]
      omega)]
  rw [writeLogical_of_ne spec.growth _
    (boundaryOffset spec.registers 3) 0 blankSymbol (by
      simp only [boundaryOffset]
      omega)]
  rw [writeLogical_of_ne spec.growth _
    (boundaryOffset spec.registers 4) 0 blankSymbol (by
      simp only [boundaryOffset]
      omega)]

/-- A tag recognized at the shared-return tape was already present at
logical coordinate `0` before boundary cleanup. -/
theorem tag_eq_of_afterZero_read {spec : Spec numTags}
    (T : FullTM0.Tape (Symbol numTags)) (search : Search)
    (hread : (atLogical spec.growth (afterZero spec T) 0).read =
      tagSymbol search) :
    logicalTape spec.growth T (0 : Nat) = tagSymbol search := by
  rw [atLogical_read] at hread
  change logicalTape spec.growth (afterZero spec T) (0 : Nat) =
    tagSymbol search at hread
  rw [logicalTape_afterZero_zero] at hread
  exact hread

/-- A tag-free core target becomes a genuine represented frame once its
coordinate-`0` tag is identified. -/
theorem represents_recoveredSpec
    (search : Search)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {target : Target numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreTargetRepresents registers growth limit target T)
    (htag : logicalTape growth T 0 = tagSymbol search) :
    Represents
      (recoveredSpec search registers growth limit target
        h.core_before_limit) T := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [recoveredSpec] using htag
  · exact h.toCorePrefixRepresents.toCoreRepresents.core
  · exact h.toCorePrefixRepresents.runway
  · exact h.target_matches

/-- The cleanup tape is the exact backing tape of the recovered frame. -/
theorem backedBy_recoveredSpec
    (search : Search)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {target : Target numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreTargetRepresents registers growth limit target T)
    (htag : logicalTape growth T 0 = tagSymbol search) :
    BackedBy
      (recoveredSpec search registers growth limit target
        h.core_before_limit) T
      (recoveredOuter search registers growth limit target
        h.core_before_limit T) := by
  change BackedBy
    (recoveredSpec search registers growth limit target h.core_before_limit)
    T
    (cleanupTape
      (recoveredSpec search registers growth limit target h.core_before_limit)
      T)
  exact CounterControlCoreEnvelope.backedBy_cleanupTape_of_represents
    (represents_recoveredSpec search h htag)

/-- If the selected command recognizes the same first obstruction, the
recovered outer tape carries exactly that command's suspended search gap. -/
theorem recoveredFrame_searchGap
    (base : Nat) (c : Nat.Partrec.Code) (search : Search)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {target : Target numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreTargetRepresents registers growth limit target T)
    (htag : logicalTape growth T 0 = tagSymbol search)
    (hselected : (command base c search).target.Matches
      (logicalTape growth T limit))
    (hdirection : (command base c search).searchDirection = growth) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (command base c search).target.Matches
      (recoveredFrame search registers growth limit target
        h.core_before_limit T).outer
      (command base c search).searchDirection
      (recoveredFrame search registers growth limit target
        h.core_before_limit T).distance := by
  have htarget : (command base c search).target = target :=
    CounterControlTargetUniqueness.target_eq_of_matches
      hselected h.target_matches
  have hback := backedBy_recoveredSpec search h htag
  simpa [recoveredFrame, recoveredOuter, recoveredSpec, htarget, hdirection]
    using hback.searchGap

/-- Once the recovered gap is beyond the private scan radius, it is a
well-formed Hooper frame in the original search-system sense. -/
theorem recoveredFrame_wellFormed
    (base : Nat) (c : Nat.Partrec.Code) (search : Search)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {target : Target numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreTargetRepresents registers growth limit target T)
    (htag : logicalTape growth T 0 = tagSymbol search)
    (hselected : (command base c search).target.Matches
      (logicalTape growth T limit))
    (hdirection : (command base c search).searchDirection = growth)
    (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < limit) :
    FrameWellFormed base c
      (recoveredFrame search registers growth limit target
        h.core_before_limit T) := by
  exact ⟨recoveredFrame_searchGap base c search h htag hselected
      hdirection, by simpa using hfar⟩

end

end CounterControlRecoveredFrame
end Hooper
end Kari
end LeanWang
