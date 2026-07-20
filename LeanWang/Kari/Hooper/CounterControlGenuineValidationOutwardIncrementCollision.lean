/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardSuffix
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutward
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardIncrement
import LeanWang.Kari.Hooper.CounterControlGuardedCleanupProgress
import LeanWang.Kari.Hooper.CounterControlRouteRoundtrip

/-!
# Cleanup handoffs for outward-validation increment collisions

Once collision processing has reached any genuine cleanup search whose gap
is at least the original outward-validation gap, the existing cleanup suffix
strictly escapes to a guarded search.  This file packages that common final
step independently of the finite geometry used to locate the appropriate
cleanup stage.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineValidationOutwardIncrementCollision

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedSearch
open CounterControlGenuineValidation
open CounterControlCleanupSuffixGeometry
open CounterControlExactCommandContinuation
open CounterControlCommandContinuationMortality
open CounterControlRouteRoundtrip

noncomputable section

/-! ## Agreement on the inward ray -/

/-- Two tapes agree at and inward from their common head.  Cleanup may have
erased markers farther outward, so full tape equality is unnecessarily
strong for replaying the next inward search. -/
def InwardRayEq (inward : Turing.Dir)
    (first second : FullTM0.Tape (Symbol numTags)) : Prop :=
  ∀ distance,
    (first.moveN inward distance).read =
      (second.moveN inward distance).read

@[refl] theorem InwardRayEq.refl
    (inward : Turing.Dir) (T : FullTM0.Tape (Symbol numTags)) :
    InwardRayEq inward T T := by
  intro distance
  rfl

/-- Ray agreement transports an exact search gap. -/
theorem InwardRayEq.searchGap
    {inward : Turing.Dir}
    {first second : FullTM0.Tape (Symbol numTags)}
    (agreement : InwardRayEq inward first second)
    {target : Fin 5} {distance : Nat}
    (gap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches second inward distance) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches first inward distance := by
  have hagree : ∀ k,
      first (FullTM0.Tape.offset inward k) =
        second (FullTM0.Tape.offset inward k) := by
    intro k
    have heq := agreement k
    cases inward <;>
      simpa [FullTM0.Tape.read, FullTM0.Tape.moveN,
        FullTM0.Tape.offset] using heq
  constructor
  · intro k hk
    rw [hagree k]
    exact gap.blank hk
  · rw [hagree distance]
    exact gap.marked

/-- Erasing the same reached target and departing inward preserves agreement
on the remaining inward ray. -/
theorem InwardRayEq.eraseDepart
    {inward : Turing.Dir}
    {first second : FullTM0.Tape (Symbol numTags)}
    (agreement : InwardRayEq inward first second)
    (distance : Nat) :
    InwardRayEq inward (eraseDepart first inward distance)
      (eraseDepart second inward distance) := by
  intro k
  have heq := agreement (distance + 1 + k)
  change
    (((((first.moveN inward distance).write blankSymbol).move inward).moveN
      inward k).read) =
    (((((second.moveN inward distance).write blankSymbol).move inward).moveN
      inward k).read)
  cases inward <;>
    simp [FullTM0.Tape.read,
      FullTM0.Tape.move, FullTM0.Tape.moveN,
      FullTM0.Tape.offset] at heq ⊢ <;>
    split_ifs <;> try omega
  all_goals
    ring_nf at heq ⊢
    exact heq

theorem InwardRayEq.trans
    {inward : Turing.Dir}
    {first second third : FullTM0.Tape (Symbol numTags)}
    (firstSecond : InwardRayEq inward first second)
    (secondThird : InwardRayEq inward second third) :
    InwardRayEq inward first third := by
  intro distance
  exact (firstSecond distance).trans (secondThird distance)

theorem InwardRayEq.symm
    {inward : Turing.Dir}
    {first second : FullTM0.Tape (Symbol numTags)}
    (agreement : InwardRayEq inward first second) :
    InwardRayEq inward second first := by
  intro distance
  exact (agreement distance).symm

/-- Clearing the cell just behind an inward-moving head does not change the
ray at or ahead of that head. -/
theorem InwardRayEq.clearedBehind
    (T : FullTM0.Tape (Symbol numTags)) (inward : Turing.Dir) :
    InwardRayEq inward ((T.write blankSymbol).move inward)
      (T.move inward) := by
  intro distance
  have hread := CanonicalInitializerProgram.read_moveN_write_of_pos
    T blankSymbol inward (distance + 1) (by omega)
  rw [FullTM0.Tape.move_moveN, FullTM0.Tape.move_moveN]
  exact hread

/-! ## Reversing one retained outward gap -/

/-- After the found endpoint is cleared and the head departs back toward the
source, the preserved outward gap is an exact inward gap of the same length. -/
theorem reverseGap_after_clear_depart
    {sourceTape : FullTM0.Tape (Symbol numTags)}
    {outward : Turing.Dir} {distance : Nat} {found source : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary found).Matches (sourceTape.move outward)
      outward distance)
    (hsource : sourceTape.read = boundarySymbol source) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      ((((sourceTape.move outward).moveN outward distance).write
        blankSymbol).move (NestingMachine.opposite outward))
      (NestingMachine.opposite outward) distance := by
  have hsource' : ((sourceTape.move outward).move
      (NestingMachine.opposite outward)).read = boundarySymbol source := by
    rw [move_move_opposite]
    exact hsource
  have hreverse := reverseGap_of_source_boundary hgap hsource'
  exact (InwardRayEq.clearedBehind
    ((sourceTape.move outward).moveN outward distance)
    (NestingMachine.opposite outward)).searchGap hreverse

/-- At the collision entry the cleared endpoint itself contributes one
additional blank cell before the same reverse gap. -/
theorem reverseGap_from_cleared_endpoint
    {sourceTape : FullTM0.Tape (Symbol numTags)}
    {outward : Turing.Dir} {distance : Nat} {found source : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary found).Matches (sourceTape.move outward)
      outward distance)
    (hsource : sourceTape.read = boundarySymbol source) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      (((sourceTape.move outward).moveN outward distance).write blankSymbol)
      (NestingMachine.opposite outward) (distance + 1) := by
  let foundTape := (sourceTape.move outward).moveN outward distance
  have htail : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      ((foundTape.write blankSymbol).move
        (NestingMachine.opposite outward))
      (NestingMachine.opposite outward) distance := by
    simpa only [foundTape] using reverseGap_after_clear_depart hgap hsource
  have hmove : (foundTape.write blankSymbol).moveN
      (NestingMachine.opposite outward) 1 =
        (foundTape.write blankSymbol).move
          (NestingMachine.opposite outward) := by
    simpa using (FullTM0.Tape.move_moveN (foundTape.write blankSymbol)
      (NestingMachine.opposite outward) 0).symm
  have hprefix : ∀ i < 1,
      ((foundTape.write blankSymbol)
        (FullTM0.Tape.offset (NestingMachine.opposite outward) i)) =
          blankSymbol := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simp
  have hfull :=
    CounterControlArbitrarySearch.SearchGap.prepend_moveN hprefix (by
      rw [hmove]
      exact htail)
  simpa [foundTape, Nat.add_comm] using hfull

private theorem outward_then_reverse
    (T : FullTM0.Tape (Symbol numTags)) (outward : Turing.Dir)
    (distance : Nat) :
    ((((T.move outward).moveN outward distance).move
      (NestingMachine.opposite outward)).moveN
        (NestingMachine.opposite outward) distance) = T := by
  exact (reverseGap_finish (T.move outward) outward distance).trans
    (move_move_opposite T outward)

/-- Once a reversed retained gap has been erased, its actual tape agrees on
the remaining inward ray with the canonical tape obtained by clearing its
source boundary and departing inward. -/
theorem clearedRouteStep_ray
    (sourceTape : FullTM0.Tape (Symbol numTags))
    (outward : Turing.Dir) (distance : Nat) :
    InwardRayEq (NestingMachine.opposite outward)
      (eraseDepart
        ((((sourceTape.move outward).moveN outward distance).write
          blankSymbol).move (NestingMachine.opposite outward))
        (NestingMachine.opposite outward) distance)
      ((sourceTape.write blankSymbol).move
        (NestingMachine.opposite outward)) := by
  let foundTape := (sourceTape.move outward).moveN outward distance
  have hagreement := (InwardRayEq.clearedBehind foundTape
    (NestingMachine.opposite outward)).eraseDepart distance
  have hnormalize : eraseDepart
      (foundTape.move (NestingMachine.opposite outward))
        (NestingMachine.opposite outward) distance =
      (sourceTape.write blankSymbol).move
        (NestingMachine.opposite outward) := by
    simp only [eraseDepart]
    rw [outward_then_reverse]
  rw [hnormalize] at hagreement
  exact hagreement

/-- The same ray statement at the first cleanup stage, where the collision
entry is still centered on the cleared final endpoint. -/
theorem clearedEndpointStep_ray
    (sourceTape : FullTM0.Tape (Symbol numTags))
    (outward : Turing.Dir) (distance : Nat) :
    InwardRayEq (NestingMachine.opposite outward)
      (eraseDepart
        (((sourceTape.move outward).moveN outward distance).write blankSymbol)
        (NestingMachine.opposite outward) (distance + 1))
      ((sourceTape.write blankSymbol).move
        (NestingMachine.opposite outward)) := by
  have hstep := clearedRouteStep_ray sourceTape outward distance
  simpa only [eraseDepart, FullTM0.Tape.move_moveN,
    Nat.add_comm] using hstep

/-! ## Genuine cleanup checkpoints -/

/-- Package an exact gap at any of the four cleanup stages as a genuine
generated search. -/
def cleanupSearch
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (stage : CounterControlCleanupRoute.Stage)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches outer
      (orient growth .left) distance) : GenuineSearch base c := by
  let raw := CounterControlCleanupRoute.command growth source stage
  let hmem := CounterControlCleanupRoute.command_mem_rawCommands_of_increment
    growth source register targetState hrule stage
  let search : Search := CounterControlCommandAt.rawTag raw hmem
  exact {
    search := search
    outer := outer
    distance := distance
    gap := by
      have hcommand : CounterControlSearchSystem.command base c search =
          CounterControlCommandAt.compileRawCommand base c raw hmem := rfl
      rw [hcommand, CounterControlCleanupRoute.compile_command]
      simpa [raw, Command.target, Command.searchDirection] using hgap }

@[simp] theorem cleanupSearch_cfg
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (stage : CounterControlCleanupRoute.Stage)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches outer
      (orient growth .left) distance) :
    (cleanupSearch base c growth source register targetState hrule stage
      outer distance hgap).cfg =
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩ := by
  let raw := CounterControlCleanupRoute.command growth source stage
  let hmem := CounterControlCleanupRoute.command_mem_rawCommands_of_increment
    growth source register targetState hrule stage
  let search : Search := CounterControlCommandAt.rawTag raw hmem
  have hget : rawCommands.get search = raw :=
    CounterControlCommandAt.rawCommands_get_rawTag raw hmem
  change (searchSystem base c).startCfg search outer = _
  change (⟨CounterControlSearchSystem.commandOffset base c search, outer⟩ :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
  unfold CounterControlSearchSystem.commandOffset
  rw [hget]
  rw [CounterControlCleanupRoute.command_address]

@[simp] theorem cleanupSearch_selectedRaw
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (stage : CounterControlCleanupRoute.Stage)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches outer
      (orient growth .left) distance) :
    (cleanupSearch base c growth source register targetState hrule stage
      outer distance hgap).selectedRaw =
      CounterControlCleanupRoute.command growth source stage := by
  let raw := CounterControlCleanupRoute.command growth source stage
  let hmem := CounterControlCleanupRoute.command_mem_rawCommands_of_increment
    growth source register targetState hrule stage
  unfold cleanupSearch GenuineSearch.selectedRaw
  change rawCommands.get (CounterControlCommandAt.rawTag raw hmem) = raw
  exact CounterControlCommandAt.rawCommands_get_rawTag raw hmem

private theorem cleanupGap_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (stage : CounterControlCleanupRoute.Stage)
    (outer : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩) :
    ∃ distance, SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches outer
      (orient growth .left) distance := by
  have hraw := CounterControlCleanupRoute.command_mem_rawCommands_of_increment
    growth source register targetState hrule stage
  exact CounterControlGeneratedSearchGap.boundaryNavigation_gap_of_immortal
    base c hmortal ⟨growth, source, stage.slot⟩ stage.expected .left
    (stage.successRef growth source) (.erase (some .left))
    (by simpa [CounterControlCleanupRoute.command] using hraw)
    outer himmortal

private theorem reaches_cleanupSuccess_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (stage : CounterControlCleanupRoute.Stage)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches outer
      (orient growth .left) distance)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩
      ⟨resolve base c (stage.successRef growth source),
        eraseDepart outer (orient growth .left) distance⟩ := by
  have hraw := CounterControlCleanupRoute.command_mem_rawCommands_of_increment
    growth source register targetState hrule stage
  have hreach :=
    CounterControlCleanupEraseProgress.machine_reaches_boundary_erase_of_immortal
      base c ⟨growth, source, stage.slot⟩ stage.expected .left
      (stage.successRef growth source) (some .left)
      (by simpa [CounterControlCleanupRoute.command] using hraw)
      outer distance hgap himmortal
  simpa [eraseDepart] using hreach

/-! ## Operational reverse replay of retained route legs -/

private theorem reverseFinalRouteLeg
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (sourceTape : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (4 : Fin 5)).Matches
      (sourceTape.move (orient growth .right))
      (orient growth .right) distance)
    (hsource : sourceTape.read = boundarySymbol 3)
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ⟨searchState base c
          ⟨growth, source, CounterControlCleanupRoute.Stage.three.slot⟩,
        (((sourceTape.move (orient growth .right)).moveN
          (orient growth .right) distance).write blankSymbol)⟩)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    ∃ outer,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
        ⟨searchState base c
          ⟨growth, source, CounterControlCleanupRoute.Stage.two.slot⟩,
          outer⟩ ∧
      InwardRayEq (orient growth .left) outer
        ((sourceTape.write blankSymbol).move (orient growth .left)) := by
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  have hreverse : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (3 : Fin 5)).Matches
      (((sourceTape.move (orient growth .right)).moveN
        (orient growth .right) distance).write blankSymbol)
      (orient growth .left) (distance + 1) := by
    rw [← hopposite]
    exact reverseGap_from_cleared_endpoint hgap hsource
  let outer :=
    eraseDepart
      (((sourceTape.move (orient growth .right)).moveN
        (orient growth .right) distance).write blankSymbol)
      (orient growth .left) (distance + 1)
  have himmortalEntry := FullTM0.ImmortalFrom.of_reaches himmortal hreaches
  have hstep := reaches_cleanupSuccess_of_immortal base c growth source
    register targetState hrule .three
    (((sourceTape.move (orient growth .right)).moveN
      (orient growth .right) distance).write blankSymbol)
    (distance + 1) hreverse himmortalEntry
  have hstep' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c
          ⟨growth, source, CounterControlCleanupRoute.Stage.three.slot⟩,
        (((sourceTape.move (orient growth .right)).moveN
          (orient growth .right) distance).write blankSymbol)⟩
      ⟨searchState base c
          ⟨growth, source, CounterControlCleanupRoute.Stage.two.slot⟩,
        outer⟩ := by
    simpa [outer] using hstep
  refine ⟨outer, hreaches.trans hstep', ?_⟩
  dsimp [outer]
  rw [← hopposite]
  exact clearedEndpointStep_ray sourceTape (orient growth .right) distance

private theorem reverseEarlierRouteLeg
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (stage nextStage : CounterControlCleanupRoute.Stage)
    (sourceBoundary foundBoundary : Fin 5)
    (hstage : stage.expected = sourceBoundary)
    (hsuccess : resolve base c (stage.successRef growth source) =
      searchState base c ⟨growth, source, nextStage.slot⟩)
    (sourceTape : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary foundBoundary).Matches
      (sourceTape.move (orient growth .right))
      (orient growth .right) distance)
    (hsource : sourceTape.read = boundarySymbol sourceBoundary)
    (outer : FullTM0.Tape (Symbol numTags))
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩)
    (agreement : InwardRayEq (orient growth .left) outer
      (((sourceTape.move (orient growth .right)).moveN
          (orient growth .right) distance).write blankSymbol |>.move
        (orient growth .left)))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    ∃ nextOuter,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
        ⟨searchState base c ⟨growth, source, nextStage.slot⟩,
          nextOuter⟩ ∧
      InwardRayEq (orient growth .left) nextOuter
        ((sourceTape.write blankSymbol).move (orient growth .left)) := by
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  have hideal : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary sourceBoundary).Matches
      ((((sourceTape.move (orient growth .right)).moveN
        (orient growth .right) distance).write blankSymbol).move
          (orient growth .left))
      (orient growth .left) distance := by
    rw [← hopposite]
    exact reverseGap_after_clear_depart hgap hsource
  have hactual : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches outer
      (orient growth .left) distance := by
    rw [hstage]
    exact agreement.searchGap hideal
  let nextOuter := eraseDepart outer (orient growth .left) distance
  have himmortalEntry := FullTM0.ImmortalFrom.of_reaches himmortal hreaches
  have hstep := reaches_cleanupSuccess_of_immortal base c growth source
    register targetState hrule stage outer distance hactual himmortalEntry
  have hstep' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩
      ⟨searchState base c ⟨growth, source, nextStage.slot⟩,
        nextOuter⟩ := by
    rw [hsuccess] at hstep
    simpa [nextOuter] using hstep
  refine ⟨nextOuter, hreaches.trans hstep', ?_⟩
  have hafter := agreement.eraseDepart distance
  have hcanonical := clearedRouteStep_ray sourceTape
    (orient growth .right) distance
  rw [hopposite] at hcanonical
  exact hafter.trans hcanonical

/-- Any reached cleanup caller whose gap contains the original outward gap
produces the required outward-instruction handoff.  The cleanup suffix itself
grows strictly, so the consumer-facing comparison is weak only because that
is all `OutwardInstructionHandoff.nextSearch` requires. -/
theorem handoff_of_cleanupEntry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {targetState : Nat}
    {instruction : CounterMachine.Instruction}
    {obligation : OutwardObligation current growth source instruction}
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (cleanup : GenuineSearch base c)
    (hcleanup : rawCommands.get cleanup.search ∈
      cleanupCommands growth source)
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current) cleanup.cfg)
    (hdistance : current.distance ≤ cleanup.distance)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (OutwardInstructionHandoff current obligation) := by
  have himmortalCleanup : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) cleanup.cfg :=
    FullTM0.ImmortalFrom.of_reaches himmortal hreaches
  rcases
      CounterControlGuardedCleanupProgress.reaches_larger_guardedSearch_of_genuine_cleanup
        base c hmortal cleanup growth source register targetState hrule
          hcleanup himmortalCleanup with
    ⟨next, hnext, hstrict⟩
  exact ⟨.nextSearch next
    (hreaches.trans hnext) (hdistance.trans hstrict.le)⟩

/-- A cleanup-stage entry whose inward ray is the reverse of the original
outward found tape has a gap at least as large as the original caller. -/
theorem handoff_of_cleanupRayEntry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {targetState : Nat}
    {obligation : OutwardObligation current growth source
      (.increment register targetState)}
    (suffix : CounterControlGenuineValidationOutwardSuffix.Suffix
      current growth source (.increment register targetState))
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (stage : CounterControlCleanupRoute.Stage)
    (outer : FullTM0.Tape (Symbol numTags))
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩)
    (agreement : InwardRayEq (orient growth .left) outer
      ((current.foundTape.write blankSymbol).move (orient growth .left)))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (OutwardInstructionHandoff current obligation) := by
  have himmortalEntry : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩ :=
    FullTM0.ImmortalFrom.of_reaches himmortal hreaches
  rcases cleanupGap_of_immortal base c hmortal growth source register
      targetState hrule stage outer himmortalEntry with
    ⟨distance, hgap⟩
  have hcleared : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches
      ((current.foundTape.write blankSymbol).move (orient growth .left))
      (orient growth .left) distance :=
    agreement.symm.searchGap hgap
  have hreplay : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches
      (current.foundTape.move (orient growth .left))
      (orient growth .left) distance :=
    (InwardRayEq.clearedBehind current.foundTape
      (orient growth .left)).symm.searchGap hcleared
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  have hreplay' : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches
      ((current.outer.moveN (orient growth .right) current.distance).move
        (NestingMachine.opposite (orient growth .right)))
      (NestingMachine.opposite (orient growth .right)) distance := by
    rw [hopposite, suffix.current_foundTape]
    exact hreplay
  have hdistance : current.distance ≤ distance :=
    CounterControlInwardValidationReplay.reverseBoundaryGap_distance_ge
      suffix.current_gap hreplay'
  let cleanup := cleanupSearch base c growth source register targetState
    hrule stage outer distance hgap
  have hcleanup : rawCommands.get cleanup.search ∈
      cleanupCommands growth source := by
    change cleanup.selectedRaw ∈ cleanupCommands growth source
    rw [show cleanup.selectedRaw =
        CounterControlCleanupRoute.command growth source stage by
      simp [cleanup]]
    exact CounterControlCleanupRoute.command_mem_cleanupCommands
      growth source stage
  have hcleanupCfg : cleanup.cfg =
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩ := by
    simp [cleanup]
  apply handoff_of_cleanupEntry base c hmortal hrule cleanup hcleanup
    (by simpa [hcleanupCfg] using hreaches) hdistance himmortal

/-- If collision cleanup starts on the cleared endpoint of the original
outward gap, its first reverse gap is strictly larger immediately. -/
theorem handoff_of_clearedCurrentEntry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {targetState : Nat}
    {obligation : OutwardObligation current growth source
      (.increment register targetState)}
    (suffix : CounterControlGenuineValidationOutwardSuffix.Suffix
      current growth source (.increment register targetState))
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (stage : CounterControlCleanupRoute.Stage)
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨searchState base c ⟨growth, source, stage.slot⟩,
        current.foundTape.write blankSymbol⟩)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (OutwardInstructionHandoff current obligation) := by
  have himmortalEntry : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, stage.slot⟩,
        current.foundTape.write blankSymbol⟩ :=
    FullTM0.ImmortalFrom.of_reaches himmortal hreaches
  rcases cleanupGap_of_immortal base c hmortal growth source register
      targetState hrule stage (current.foundTape.write blankSymbol)
      himmortalEntry with ⟨distance, hgap⟩
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  have hreverse : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches
      ((current.outer.moveN (orient growth .right) current.distance).write
        blankSymbol)
      (NestingMachine.opposite (orient growth .right)) distance := by
    rw [hopposite, suffix.current_foundTape]
    exact hgap
  have hdistance : current.distance ≤ distance :=
    (CounterControlGenuineValidationOutward.clearedReverseGap_distance_gt
      suffix.current_gap hreverse).le
  let cleanup := cleanupSearch base c growth source register targetState
    hrule stage (current.foundTape.write blankSymbol) distance hgap
  have hcleanup : rawCommands.get cleanup.search ∈
      cleanupCommands growth source := by
    change cleanup.selectedRaw ∈ cleanupCommands growth source
    rw [show cleanup.selectedRaw =
        CounterControlCleanupRoute.command growth source stage by
      simp [cleanup]]
    exact CounterControlCleanupRoute.command_mem_cleanupCommands
      growth source stage
  have hcleanupCfg : cleanup.cfg =
      ⟨searchState base c ⟨growth, source, stage.slot⟩,
        current.foundTape.write blankSymbol⟩ := by
    simp [cleanup]
  apply handoff_of_cleanupEntry base c hmortal hrule cleanup hcleanup
    (by simpa [hcleanupCfg] using hreaches) hdistance himmortal

/-! ## Collision entry for an arbitrary outward suffix -/

private abbrev toFour_four :=
  @CounterControlResumedRouteEmbedding.ToFour.four_eq_nil
private abbrev toFour_three :=
  @CounterControlResumedRouteEmbedding.ToFour.three_eq
private abbrev toFour_two :=
  @CounterControlResumedRouteEmbedding.ToFour.two_eq
private abbrev toFour_one :=
  @CounterControlResumedRouteEmbedding.ToFour.one_eq
private theorem routeTail_nil_finish
    {growth : Turing.Dir}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : CounterControlRouteSuffixMortality.RouteTailGaps growth []
      start finish) : finish = start :=
  trace.nil_finish
/-- Starting at the boundary-`4` collision-cleanup entry, replay the retained
outward validation suffix in reverse and hand off from the cleanup stage
opposite the original caller. -/
theorem handoff_of_collisionEntry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {targetState : Nat}
    {obligation : OutwardObligation current growth source
      (.increment register targetState)}
    (suffix : CounterControlGenuineValidationOutwardSuffix.Suffix
      current growth source (.increment register targetState))
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
        suffix.progress.suffix.finish.write blankSymbol⟩)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (OutwardInstructionHandoff current obligation) := by
  generalize hindex : suffix.index = index
  fin_cases index
  · -- The original caller found boundary `1`; replay `4,3,2`.
    have htoFour : CounterControlResumedRouteEmbedding.ToFour 1
        suffix.progress.suffix.remaining := by
      simpa [hindex] using suffix.remaining_toFour
    have hremaining := toFour_one htoFour
    have htail := suffix.tailGaps
    rw [hremaining] at htail
    rcases htail.uncons with ⟨d2, gap2, tail3⟩
    let found2 :=
      (current.foundTape.move (orient growth .right)).moveN
        (orient growth .right) d2
    rcases tail3.uncons with ⟨d3, gap3, tail4⟩
    let found3 :=
      (found2.move (orient growth .right)).moveN
        (orient growth .right) d3
    rcases tail4.uncons with ⟨d4, gap4, tailEnd⟩
    have hfinish := routeTail_nil_finish tailEnd
    have hread3 : found3.read = boundarySymbol 3 := by
      simpa [found3, found2, FullTM0.Tape.read_moveN,
        Target.Matches] using gap3.marked
    rcases reverseFinalRouteLeg base c growth source register
        targetState hrule found3 d4 (by simpa [found3, found2] using gap4)
        hread3 (by simpa [found3, found2, hfinish,
          CounterControlCleanupRoute.Stage.slot] using hreaches) himmortal with
      ⟨outer2, hreach2, hagree2⟩
    have hread2 : found2.read = boundarySymbol 2 := by
      simpa [found2, FullTM0.Tape.read_moveN,
        Target.Matches] using gap2.marked
    rcases reverseEarlierRouteLeg base c growth source register
        targetState hrule .two .one 2 3 rfl rfl found2 d3
        (by simpa [found2] using gap3) hread2 outer2 hreach2
        (by simpa [found3] using hagree2) himmortal with
      ⟨outer1, hreach1, hagree1⟩
    have hread1 : current.foundTape.read = boundarySymbol 1 := by
      simpa [hindex] using suffix.current_read
    rcases reverseEarlierRouteLeg base c growth source register
        targetState hrule .one .zero 1 2 rfl rfl
        current.foundTape d2 (by simpa using gap2) hread1
        outer1 hreach1 (by simpa [found2] using hagree1)
        himmortal with ⟨outer0, hreach0, hagree0⟩
    exact handoff_of_cleanupRayEntry base c hmortal suffix hrule
      .zero outer0 hreach0 hagree0 himmortal
  · -- The original caller found boundary `2`; replay `4,3`.
    have htoFour : CounterControlResumedRouteEmbedding.ToFour 2
        suffix.progress.suffix.remaining := by
      simpa [hindex] using suffix.remaining_toFour
    have hremaining := toFour_two htoFour
    have htail := suffix.tailGaps
    rw [hremaining] at htail
    rcases htail.uncons with ⟨d3, gap3, tail4⟩
    let found3 :=
      (current.foundTape.move (orient growth .right)).moveN
        (orient growth .right) d3
    rcases tail4.uncons with ⟨d4, gap4, tailEnd⟩
    have hfinish := routeTail_nil_finish tailEnd
    have hread3 : found3.read = boundarySymbol 3 := by
      simpa [found3, FullTM0.Tape.read_moveN,
        Target.Matches] using gap3.marked
    rcases reverseFinalRouteLeg base c growth source register
        targetState hrule found3 d4 (by simpa [found3] using gap4)
        hread3 (by simpa [found3, hfinish,
          CounterControlCleanupRoute.Stage.slot] using hreaches) himmortal with
      ⟨outer2, hreach2, hagree2⟩
    have hread2 : current.foundTape.read = boundarySymbol 2 := by
      simpa [hindex] using suffix.current_read
    rcases reverseEarlierRouteLeg base c growth source register
        targetState hrule .two .one 2 3 rfl rfl
        current.foundTape d3 (by simpa using gap3) hread2
        outer2 hreach2 (by simpa [found3] using hagree2)
        himmortal with ⟨outer1, hreach1, hagree1⟩
    exact handoff_of_cleanupRayEntry base c hmortal suffix hrule
      .one outer1 hreach1 hagree1 himmortal
  · -- The original caller found boundary `3`; replay `4`.
    have htoFour : CounterControlResumedRouteEmbedding.ToFour 3
        suffix.progress.suffix.remaining := by
      simpa [hindex] using suffix.remaining_toFour
    have hremaining := toFour_three htoFour
    have htail := suffix.tailGaps
    rw [hremaining] at htail
    rcases htail.uncons with ⟨d4, gap4, tailEnd⟩
    have hfinish := routeTail_nil_finish tailEnd
    have hread3 : current.foundTape.read = boundarySymbol 3 := by
      simpa [hindex] using suffix.current_read
    rcases reverseFinalRouteLeg base c growth source register
        targetState hrule current.foundTape d4 (by simpa using gap4)
        hread3 (by simpa [hfinish,
          CounterControlCleanupRoute.Stage.slot] using hreaches) himmortal with
      ⟨outer2, hreach2, hagree2⟩
    exact handoff_of_cleanupRayEntry base c hmortal suffix hrule
      .two outer2 hreach2 hagree2 himmortal
  · -- Boundary `4` is already the original found endpoint.
    have htoFour : CounterControlResumedRouteEmbedding.ToFour 4
        suffix.progress.suffix.remaining := by
      simpa [hindex] using suffix.remaining_toFour
    have hremaining := toFour_four htoFour
    have htail := suffix.tailGaps
    rw [hremaining] at htail
    have hfinish := routeTail_nil_finish htail
    exact handoff_of_clearedCurrentEntry base c hmortal suffix hrule
      .three (by simpa [hfinish,
        CounterControlCleanupRoute.Stage.slot] using hreaches) himmortal

/-! ## The first increment-shift collision -/

private theorem found_reaches_firstIncrementCollision
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (hraw : current.selectedRaw =
      CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw
        growth source register)
    (hoccupied : ShiftDestinationOccupied current.selectedRaw
      current.foundTape) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current)
      ⟨resolve base c (directRef growth source testDirectSlot),
        exactCollisionTape
          (CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw
            growth source register) current.foundTape⟩ := by
  let raw :=
    CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw
      growth source register
  let move : MarkerProgram.Move :=
    ⟨4, orient growth .left, orient growth .right⟩
  have hread : current.foundTape.read = boundarySymbol 4 := by
    have htarget := current.selectedRaw_target_matches_foundTape
    rw [CounterControlCommandAt.compileRawCommand_spec] at htarget
    simpa [hraw, raw,
      CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw,
      CounterControlCommandAt.compileRawAtTag, Command.target,
      Target.Matches] using htarget
  have hatRaw := CounterControlCommandAt.CommandAt.compileRawCommand
    base c current.selectedRaw current.selectedRaw_mem
  rw [CounterControlCommandAt.compileRawCommand_spec] at hatRaw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c ⟨growth, source, bodySearchBase⟩)
      (.markerShift move
        (resolve base c (rawSuccessRef raw))
        (CounterControlCommandAt.rawTag current.selectedRaw
          current.selectedRaw_mem)
        (some (orient growth .left))
        (some (resolve base c
          (directRef growth source testDirectSlot))))
      (commands base c) := by
    simpa [hraw, raw,
      CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw,
      move, CounterControlCommandAt.compileRawAtTag, RawCommand.address,
      rawSuccessRef] using hatRaw
  have hcollisionLocal :=
    BoundedMarkerContinuation.machine_reaches_shift_collision_native
      (coreTable base c) move (resolve base c (rawSuccessRef raw))
      (resolve base c (directRef growth source testDirectSlot))
      (CounterControlCommandAt.rawTag current.selectedRaw
        current.selectedRaw_mem)
      (some (orient growth .left)) hat current.foundTape hread (by
        simpa [hraw, raw,
          CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw,
          move, ShiftDestinationOccupied] using hoccupied)
  rw [current.foundCfg_eq, hraw]
  simpa [CounterControlNestingBridge.machine, raw,
    CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw,
    move, exactCollisionTape, controllerCoreEntry_eq,
    RawCommand.address] using hcollisionLocal

/-- An occupied first increment shift at the end of any outward validation
suffix reaches cleanup and therefore satisfies the outward handoff law.  The
native found-command collision step is derived here; callers need provide
only the occupied-destination fact. -/
theorem handoff_of_firstIncrementCollision
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {targetState : Nat}
    {obligation : OutwardObligation current growth source
      (.increment register targetState)}
    (suffix : CounterControlGenuineValidationOutwardSuffix.Suffix
      current growth source (.increment register targetState))
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (hoccupied : ShiftDestinationOccupied
      (CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw
        growth source register) suffix.progress.suffix.finish)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (OutwardInstructionHandoff current obligation) := by
  let shift :=
    CounterControlGenuineValidationOutwardIncrement.bodyIncrementShift
      base c growth source targetState register hrule
      suffix.progress.suffix.finish suffix.finish_read
  have hentry : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      shift.cfg := by
    rw [CounterControlGenuineValidationOutwardIncrement.bodyIncrementShift_cfg]
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve] using
      suffix.reaches_bodyEntry
  have himmortalShift : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) shift.cfg :=
    FullTM0.ImmortalFrom.of_reaches himmortal hentry
  have hfound := CounterControlParentContinuation.reaches_foundCfg_of_immortal
    shift himmortalShift
  have hshiftRaw : shift.selectedRaw =
      CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw
        growth source register := by
    simp [shift]
  have hshiftTape : shift.foundTape = suffix.progress.suffix.finish := by
    simp [shift, GenuineSearch.foundTape]
  have hcollisionShift := found_reaches_firstIncrementCollision base c shift
    growth source register hshiftRaw (by
      rw [hshiftRaw, hshiftTape]
      exact hoccupied)
  have hcollision : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨resolve base c (directRef growth source testDirectSlot),
        exactCollisionTape
          (CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw
            growth source register) suffix.progress.suffix.finish⟩ := by
    rw [hshiftTape] at hcollisionShift
    exact hentry.trans (hfound.trans hcollisionShift)
  have hcleanupDirect :=
    CounterControlGenuineValidationOutwardIncrement.reaches_cleanup_of_firstIncrementCollision
      base c growth source targetState register hrule
      suffix.progress.suffix.finish hoccupied
  have hcleanup : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
        suffix.progress.suffix.finish.write blankSymbol⟩ :=
    hcollision.trans hcleanupDirect
  exact handoff_of_collisionEntry base c hmortal suffix hrule hcleanup
    himmortal

end

end CounterControlGenuineValidationOutwardIncrementCollision
end Hooper
end Kari
end LeanWang
