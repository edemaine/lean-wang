/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlBodyMonotone
import LeanWang.Kari.Hooper.CounterControlGenuineRouteEmbedding
import LeanWang.Kari.Hooper.CounterControlInwardValidationReplay

/-!
# Guard-free validation callers

An arbitrary genuine generated search may enter at any of the eight positions
of the symmetric validation sweep.  Preserving navigation is collision-free,
so every such caller completes the remaining suffix and reaches the selected
instruction body.  This file packages that common operational fact and the
exact finite position of the caller.

The four inward positions retain the complete outward half of the sweep and
therefore contain enough geometry to reconstruct the counter core.  The four
outward positions deliberately retain their exact suffix: their missing
inward prefix is not determined by an arbitrary search configuration.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineValidation

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape CounterControlPlan
open CounterControlCoreFrame
open CounterControlGlobalUnnesting
open CounterControlGenuineRouteEmbedding
open CounterControlValidationMortality
open CounterControlRouteSuffixMortality
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The exact completed suffix of an arbitrary genuine validation caller. -/
abbrev ValidationEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) :=
  GenuineRouteEnd current growth source validationSearchBase
    validationDirectBase (bodyEntry growth source instruction)
    MarkerValidation.sweep

/-- Preserving validation commands and their direct continuations are part
of the global controller whenever the source instruction is a global rule. -/
theorem progressedValidation
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      validationCommands growth source instruction) :
    Nonempty (ValidationEnd current growth source instruction) := by
  have hcommands : ∀ command,
      command ∈ routeCommandsAux growth source validationSearchBase
          validationDirectBase (bodyEntry growth source instruction)
          MarkerValidation.sweep →
        command ∈ rawCommands := by
    intro command hmem
    apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
      growth hrule
    cases instruction <;>
      simp [commandsForRule, validationCommands, hmem]
  have hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth source validationSearchBase
          validationDirectBase MarkerValidation.sweep →
        rule ∈ rawDirectRules := by
    intro rule hmem
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth hrule
    cases instruction <;>
      simp [directRulesForRule, validationRules, hmem]
  exact progressedRoute base c hmortal current himmortal growth source
    validationSearchBase validationDirectBase
    (bodyEntry growth source instruction) MarkerValidation.sweep
    (by simpa [validationCommands] using hcommand)
    hcommands hcontinuations

/-- Exact finite position of a completed validation suffix.  Inward cases
still contain the complete outward sweep.  Outward cases record precisely
which prefix of that sweep is missing. -/
inductive Position
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) : Type where
  | inwardThree
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 0⟩ 3 .left (directRef growth source 0)
          .preserve)
  | inwardTwo
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 1⟩ 2 .left (directRef growth source 1)
          .preserve)
  | inwardOne
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 2⟩ 1 .left (directRef growth source 2)
          .preserve)
  | inwardZero
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 3⟩ 0 .left (directRef growth source 3)
          .preserve)
  | outwardOne
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 4⟩ 1 .right (directRef growth source 4)
          .preserve)
  | outwardTwo
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 5⟩ 2 .right (directRef growth source 5)
          .preserve)
  | outwardThree
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 6⟩ 3 .right (directRef growth source 6)
          .preserve)
  | outwardFour
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 7⟩ 4 .right
          (bodyEntry growth source instruction) .preserve)

/-- Compile membership in the validation family into its exact one of eight
positions, retaining the completed operational suffix in every case. -/
theorem classify
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      validationCommands growth source instruction) :
    Nonempty (Position current growth source instruction) := by
  rcases progressedValidation base c hmortal current himmortal growth source
      instruction hrule hcommand with ⟨progress⟩
  have hcases := hcommand
  simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
    validationSearchBase, validationDirectBase] at hcases
  rcases hcases with hraw | hraw | hraw | hraw | hraw | hraw | hraw | hraw
  · exact ⟨.inwardThree progress hraw⟩
  · exact ⟨.inwardTwo progress hraw⟩
  · exact ⟨.inwardOne progress hraw⟩
  · exact ⟨.inwardZero progress hraw⟩
  · exact ⟨.outwardOne progress hraw⟩
  · exact ⟨.outwardTwo progress hraw⟩
  · exact ⟨.outwardThree progress hraw⟩
  · exact ⟨.outwardFour progress hraw⟩

private theorem inwardZero_remaining
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (progress : ValidationEnd current growth source instruction)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 3⟩ 0 .left (directRef growth source 3)
        .preserve) :
    progress.suffix.remaining =
      CounterControlValidationConverse.outwardSweep := by
  have hroute := progress.suffix.route_eq
  have hcompiled := hraw.symm.trans progress.suffix.raw_eq
  simp [validationSearchBase, validationDirectBase,
    routeSuffixSuccess] at hcompiled
  calc
    progress.suffix.remaining =
        List.drop (progress.suffix.before.length + 1)
          (progress.suffix.before ++
            progress.suffix.current :: progress.suffix.remaining) := by
      simp
    _ = List.drop 4 MarkerValidation.sweep := by
      rw [← hroute]
      congr 1
      omega
    _ = CounterControlValidationConverse.outwardSweep := by
      rfl

private theorem direction_eq_of_boundaryRaw
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source slot : Nat) (expected : Fin 5)
    (logicalDirection : Turing.Dir) (success : ControlRef)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, slot⟩ expected logicalDirection success .preserve) :
    current.direction = orient growth logicalDirection := by
  have hdirection := current.selectedRaw_direction_eq
  rw [CounterControlCommandAt.compileRawCommand_searchDirection] at hdirection
  rw [hraw] at hdirection
  exact hdirection.symm

private theorem gap_of_boundaryRaw
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source slot : Nat) (expected : Fin 5)
    (logicalDirection : Turing.Dir) (success : ControlRef)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, slot⟩ expected logicalDirection success .preserve) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches current.outer
      (orient growth logicalDirection) current.distance := by
  have hgap := current.gap
  rw [← current.compileRawCommand_selectedRaw,
    CounterControlCommandAt.compileRawCommand_spec] at hgap
  simpa [hraw, CounterControlCommandAt.compileRawAtTag,
    compileNavigationAction, Command.target,
    Command.searchDirection] using hgap

private theorem foundTape_read_of_boundaryRaw
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source slot : Nat) (expected : Fin 5)
    (logicalDirection : Turing.Dir) (success : ControlRef)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, slot⟩ expected logicalDirection success .preserve) :
    current.foundTape.read = boundarySymbol expected := by
  have hmatch := current.selectedRaw_target_matches_foundTape
  rw [CounterControlCommandAt.compileRawCommand_spec] at hmatch
  simpa [hraw, CounterControlCommandAt.compileRawAtTag,
    compileNavigationAction, Command.target, Target.Matches] using hmatch

@[simp] private theorem opposite_orient_left (growth : Turing.Dir) :
    NestingMachine.opposite (orient growth .left) = orient growth .right := by
  cases growth <;> rfl

private theorem atLogical_boundaryZero_to_core
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (position : Nat) :
    atLogical growth (T.move (orient growth .left)) (position + 1) =
      atLogical growth T position := by
  funext coordinate
  cases growth <;>
    simp [atLogical, orient, FullTM0.Tape.moveN,
      FullTM0.Tape.offset, FullTM0.Tape.move] <;>
    congr 1 <;> ring

/-- A validation suffix which still contains boundary `0` and the complete
outward sweep reconstructs an exact body core.  The original genuine gap is
strictly inside that core. -/
structure ReconstructedBody
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) : Type where
  registers : Registers
  tape : FullTM0.Tape (Symbol numTags)
  represented : CounterControlCoreFrame.CoreRepresents registers growth tape
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current)
    (CounterControlPrefixInstructionResolution.bodyCfg base c growth
      ⟨source, registers⟩ instruction tape)
  strictly_inside : current.distance < FramedMarkerTape.layoutEnd registers

/-- The last inward validation position already sits on boundary `0`; its
remaining suffix is exactly the four-leg outward reconstruction. -/
theorem reconstruct_inwardZero
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (progress : ValidationEnd current growth source instruction)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 3⟩ 0 .left (directRef growth source 3)
        .preserve) :
    Nonempty (ReconstructedBody current growth source instruction) := by
  have hremaining := inwardZero_remaining progress hraw
  have htail := progress.suffix.tailGaps
  rw [hremaining] at htail
  cases htail with
  | cons _ _ _ _ htrace =>
      have hzero : current.foundTape.read = boundarySymbol 0 := by
        simpa using foundTape_read_of_boundaryRaw current growth source 3 0
          .left (directRef growth source 3) hraw
      rcases outwardRouteGaps_reconstructs growth current.foundTape
          progress.suffix.finish hzero htrace with
        ⟨registers, hboundary, hcore, hfinish⟩
      let coreTape := current.foundTape.move (orient growth .left)
      have hfinishCore : progress.suffix.finish =
          atLogical growth coreTape (FramedMarkerTape.layoutEnd registers) := by
        rw [hfinish]
        change atLogical growth current.foundTape
            (RegisterLayout.clockBoundary registers) =
          atLogical growth
            (current.foundTape.move (orient growth .left))
            (FramedMarkerTape.layoutEnd registers)
        rw [show FramedMarkerTape.layoutEnd registers =
            RegisterLayout.clockBoundary registers + 1 by
          simp [FramedMarkerTape.layoutEnd]]
        exact (atLogical_boundaryZero_to_core growth current.foundTape
          (RegisterLayout.clockBoundary registers)).symm
      have hbody : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          (foundCfg current)
          (CounterControlPrefixInstructionResolution.bodyCfg base c growth
            ⟨source, registers⟩ instruction coreTape) := by
        have hrun := progress.reaches
        rw [hfinishCore] at hrun
        simpa [CounterControlPrefixInstructionResolution.bodyCfg,
          coreTape] using hrun
      have hcurrentGap : SearchGap (fun symbol => symbol = blankSymbol)
          (Target.boundary (0 : Fin 5)).Matches current.outer
          (orient growth .left) current.distance :=
        gap_of_boundaryRaw current growth source 3 0 .left
          (directRef growth source 3) hraw
      have hdirection : current.direction = orient growth .left :=
        direction_eq_of_boundaryRaw current growth source 3 0 .left
          (directRef growth source 3) hraw
      have hfoundTape : current.foundTape =
          current.outer.moveN (orient growth .left) current.distance := by
        simp [GenuineSearch.foundTape, hdirection]
      cases htrace with
      | cons _ _ _ _ firstDistance firstGap firstFinish firstTail =>
          have hreverseGap : SearchGap (fun symbol => symbol = blankSymbol)
              (Target.boundary (1 : Fin 5)).Matches
              ((current.outer.moveN (orient growth .left)
                  current.distance).move
                (NestingMachine.opposite (orient growth .left)))
              (NestingMachine.opposite (orient growth .left))
              firstDistance := by
            rw [opposite_orient_left]
            simpa [hfoundTape] using firstGap
          have hdistance : current.distance ≤ firstDistance :=
            CounterControlInwardValidationReplay.reverseBoundaryGap_distance_ge
              hcurrentGap hreverseGap
          let firstFound :=
            ((current.foundTape.move (orient growth .right)).moveN
              (orient growth .right) firstDistance)
          have hfirstRead : firstFound.read = boundarySymbol 1 := by
            change (Target.boundary (1 : Fin 5)).Matches firstFound.read
            simpa [firstFound, FullTM0.Tape.read_moveN] using firstGap.marked
          have hrest : RouteTailGaps growth
              [⟨2, .right⟩, ⟨3, .right⟩, ⟨4, .right⟩]
              firstFound progress.suffix.finish :=
            .cons ⟨2, .right⟩ [⟨3, .right⟩, ⟨4, .right⟩]
              firstFound progress.suffix.finish firstTail
          have hfirstCanonical : firstFound =
              atLogical growth coreTape
                (boundaryOffset registers 1) := by
            exact CounterControlResumedRouteEmbedding.ToFour.start_eq
              hcore (.step 1 (.step 2 (.step 3 .four))) hfirstRead hrest
                hfinishCore
          have hfirstShort : firstDistance <
              FramedMarkerTape.layoutEnd registers := by
            exact CounterControlResumedRouteEmbedding.rightGap_distance_lt_layoutEnd
              hcore 0 firstDistance firstGap hfirstCanonical
          exact ⟨⟨registers, coreTape, hcore, hbody,
            lt_of_le_of_lt hdistance hfirstShort⟩⟩

private theorem remaining_of_boundaryRaw
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (progress : ValidationEnd current growth source instruction)
    (slot : Nat) (expected : Fin 5) (logicalDirection : Turing.Dir)
    (success : ControlRef)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, slot⟩ expected logicalDirection success .preserve) :
    progress.suffix.remaining = MarkerValidation.sweep.drop (slot + 1) := by
  have hroute := progress.suffix.route_eq
  have hcompiled := hraw.symm.trans progress.suffix.raw_eq
  simp [validationSearchBase, validationDirectBase,
    routeSuffixSuccess] at hcompiled
  calc
    progress.suffix.remaining =
        List.drop (progress.suffix.before.length + 1)
          (progress.suffix.before ++
            progress.suffix.current :: progress.suffix.remaining) := by
      simp
    _ = List.drop (slot + 1) MarkerValidation.sweep := by
      rw [← hroute]
      congr 1
      omega

/-- Core reconstructed from the complete outward half retained by an inward
validation suffix. -/
structure OutwardBodyCore
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (zeroTape : FullTM0.Tape (Symbol numTags)) : Type where
  registers : Registers
  tape : FullTM0.Tape (Symbol numTags)
  represented : CoreRepresents registers growth tape
  zero_center : zeroTape = atLogical growth tape (boundaryOffset registers 0)
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current)
    (CounterControlPrefixInstructionResolution.bodyCfg base c growth
      ⟨source, registers⟩ instruction tape)

private theorem outwardBodyCore
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (progress : ValidationEnd current growth source instruction)
    (zeroTape : FullTM0.Tape (Symbol numTags))
    (hzero : zeroTape.read = boundarySymbol 0)
    (htrace : RouteGaps growth
      CounterControlValidationConverse.outwardSweep
      (zeroTape.move (orient growth .right)) progress.suffix.finish) :
    Nonempty (OutwardBodyCore current growth source instruction zeroTape) := by
  rcases outwardRouteGaps_reconstructs growth zeroTape progress.suffix.finish
      hzero htrace with ⟨registers, _hboundary, hcore, hfinish⟩
  let coreTape := zeroTape.move (orient growth .left)
  have hfinishCore : progress.suffix.finish =
      atLogical growth coreTape (layoutEnd registers) := by
    rw [hfinish]
    change atLogical growth zeroTape
        (RegisterLayout.clockBoundary registers) =
      atLogical growth (zeroTape.move (orient growth .left))
        (layoutEnd registers)
    rw [show layoutEnd registers =
        RegisterLayout.clockBoundary registers + 1 by
      simp [layoutEnd]]
    exact (atLogical_boundaryZero_to_core growth zeroTape
      (RegisterLayout.clockBoundary registers)).symm
  have hzeroCenter : zeroTape =
      atLogical growth coreTape (boundaryOffset registers 0) := by
    change zeroTape =
      atLogical growth (zeroTape.move (orient growth .left)) 1
    simpa [atLogical] using
      (atLogical_boundaryZero_to_core growth zeroTape 0).symm
  have hbody : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current)
      (CounterControlPrefixInstructionResolution.bodyCfg base c growth
        ⟨source, registers⟩ instruction coreTape) := by
    have hrun := progress.reaches
    rw [hfinishCore] at hrun
    simpa [CounterControlPrefixInstructionResolution.bodyCfg,
      coreTape] using hrun
  exact ⟨⟨registers, coreTape, hcore, hzeroCenter, hbody⟩⟩

private theorem reconstructedBody_of_canonicalFound
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source slot : Nat}
    {instruction : CounterMachine.Instruction}
    (i : Fin 4) (success : ControlRef)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, slot⟩ i.castSucc .left success .preserve)
    {zeroTape : FullTM0.Tape (Symbol numTags)}
    (core : OutwardBodyCore current growth source instruction zeroTape)
    (hfoundCanonical : current.foundTape =
      atLogical growth core.tape (boundaryOffset core.registers i.castSucc)) :
    Nonempty (ReconstructedBody current growth source instruction) := by
  have hdirection : current.direction = orient growth .left :=
    direction_eq_of_boundaryRaw current growth source slot i.castSucc .left
      success hraw
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.castSucc).Matches current.outer
      (orient growth .left) current.distance :=
    gap_of_boundaryRaw current growth source slot i.castSucc .left success
      hraw
  have hfound : current.outer.moveN (orient growth .left) current.distance =
      atLogical growth core.tape
        (boundaryOffset core.registers i.castSucc) := by
    rw [← hfoundCanonical]
    simp [GenuineSearch.foundTape, hdirection]
  have hinside : current.distance < layoutEnd core.registers :=
    CounterControlResumedRouteEmbedding.leftGap_distance_lt_layoutEnd
      core.represented i current.distance hgap hfound
  exact ⟨⟨core.registers, core.tape, core.represented, core.reaches,
    hinside⟩⟩

/-- A caller searching inward for boundary `1` retains the final search for
boundary `0` and then the whole outward sweep. -/
theorem reconstruct_inwardOne
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (progress : ValidationEnd current growth source instruction)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 2⟩ 1 .left (directRef growth source 2)
        .preserve) :
    Nonempty (ReconstructedBody current growth source instruction) := by
  have hremaining := remaining_of_boundaryRaw progress 2 1 .left
    (directRef growth source 2) hraw
  have htail := progress.suffix.tailGaps
  rw [hremaining] at htail
  change RouteTailGaps growth
    [⟨0, .left⟩, ⟨1, .right⟩, ⟨2, .right⟩,
      ⟨3, .right⟩, ⟨4, .right⟩]
    current.foundTape progress.suffix.finish at htail
  cases htail with
  | cons _ _ _ _ hroute =>
      cases hroute with
      | cons _ _ _ _ zeroDistance zeroGap _ outwardTrace =>
          let zeroTape :=
            ((current.foundTape.move (orient growth .left)).moveN
              (orient growth .left) zeroDistance)
          have hzero : zeroTape.read = boundarySymbol 0 := by
            change (Target.boundary (0 : Fin 5)).Matches zeroTape.read
            simpa [zeroTape, FullTM0.Tape.read_moveN] using zeroGap.marked
          have houtward : RouteGaps growth
              CounterControlValidationConverse.outwardSweep
              (zeroTape.move (orient growth .right))
              progress.suffix.finish := by
            simpa [CounterControlValidationConverse.outwardSweep,
              zeroTape] using outwardTrace
          rcases outwardBodyCore progress zeroTape hzero houtward with ⟨core⟩
          have hsource : current.foundTape.read = boundarySymbol 1 :=
            foundTape_read_of_boundaryRaw current growth source 2 1 .left
              (directRef growth source 2) hraw
          have hcanonical : current.foundTape =
              atLogical growth core.tape
                (boundaryOffset core.registers 1) := by
            exact CounterControlResumedRouteEmbedding.start_eq_of_leftLeg_found
              core.represented 0 zeroDistance hsource zeroGap
                core.zero_center
          exact reconstructedBody_of_canonicalFound 1
            (directRef growth source 2) hraw core hcanonical

/-- A caller searching inward for boundary `2` retains two inward legs and
then the whole outward sweep. -/
theorem reconstruct_inwardTwo
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (progress : ValidationEnd current growth source instruction)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 1⟩ 2 .left (directRef growth source 1)
        .preserve) :
    Nonempty (ReconstructedBody current growth source instruction) := by
  have hremaining := remaining_of_boundaryRaw progress 1 2 .left
    (directRef growth source 1) hraw
  have htail := progress.suffix.tailGaps
  rw [hremaining] at htail
  change RouteTailGaps growth
    [⟨1, .left⟩, ⟨0, .left⟩, ⟨1, .right⟩,
      ⟨2, .right⟩, ⟨3, .right⟩, ⟨4, .right⟩]
    current.foundTape progress.suffix.finish at htail
  cases htail with
  | cons _ _ _ _ hroute =>
      cases hroute with
      | cons _ _ _ _ oneDistance oneGap _ oneTail =>
          let oneTape :=
            ((current.foundTape.move (orient growth .left)).moveN
              (orient growth .left) oneDistance)
          cases oneTail with
          | cons _ _ _ _ zeroDistance zeroGap _ outwardTrace =>
              let zeroTape :=
                ((oneTape.move (orient growth .left)).moveN
                  (orient growth .left) zeroDistance)
              have hzero : zeroTape.read = boundarySymbol 0 := by
                change (Target.boundary (0 : Fin 5)).Matches zeroTape.read
                simpa [zeroTape, oneTape, FullTM0.Tape.read_moveN] using
                  zeroGap.marked
              have houtward : RouteGaps growth
                  CounterControlValidationConverse.outwardSweep
                  (zeroTape.move (orient growth .right))
                  progress.suffix.finish := by
                simpa [CounterControlValidationConverse.outwardSweep,
                  zeroTape, oneTape] using outwardTrace
              rcases outwardBodyCore progress zeroTape hzero houtward with
                ⟨core⟩
              have honeRead : oneTape.read = boundarySymbol 1 := by
                change (Target.boundary (1 : Fin 5)).Matches oneTape.read
                simpa [oneTape, FullTM0.Tape.read_moveN] using oneGap.marked
              have honeCanonical : oneTape =
                  atLogical growth core.tape
                    (boundaryOffset core.registers 1) := by
                exact
                  CounterControlResumedRouteEmbedding.start_eq_of_leftLeg_found
                    core.represented 0 zeroDistance honeRead zeroGap
                      core.zero_center
              have hsource : current.foundTape.read = boundarySymbol 2 :=
                foundTape_read_of_boundaryRaw current growth source 1 2 .left
                  (directRef growth source 1) hraw
              have hcanonical : current.foundTape =
                  atLogical growth core.tape
                    (boundaryOffset core.registers 2) := by
                exact
                  CounterControlResumedRouteEmbedding.start_eq_of_leftLeg_found
                    core.represented 1 oneDistance hsource oneGap
                      honeCanonical
              exact reconstructedBody_of_canonicalFound 2
                (directRef growth source 1) hraw core hcanonical

/-- A caller at the first validation command retains all three lower inward
legs and then the whole outward sweep. -/
theorem reconstruct_inwardThree
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (progress : ValidationEnd current growth source instruction)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 0⟩ 3 .left (directRef growth source 0)
        .preserve) :
    Nonempty (ReconstructedBody current growth source instruction) := by
  have hremaining := remaining_of_boundaryRaw progress 0 3 .left
    (directRef growth source 0) hraw
  have htail := progress.suffix.tailGaps
  rw [hremaining] at htail
  change RouteTailGaps growth
    [⟨2, .left⟩, ⟨1, .left⟩, ⟨0, .left⟩,
      ⟨1, .right⟩, ⟨2, .right⟩, ⟨3, .right⟩, ⟨4, .right⟩]
    current.foundTape progress.suffix.finish at htail
  cases htail with
  | cons _ _ _ _ hroute =>
      cases hroute with
      | cons _ _ _ _ twoDistance twoGap _ twoTail =>
          let twoTape :=
            ((current.foundTape.move (orient growth .left)).moveN
              (orient growth .left) twoDistance)
          cases twoTail with
          | cons _ _ _ _ oneDistance oneGap _ oneTail =>
              let oneTape :=
                ((twoTape.move (orient growth .left)).moveN
                  (orient growth .left) oneDistance)
              cases oneTail with
              | cons _ _ _ _ zeroDistance zeroGap _ outwardTrace =>
                  let zeroTape :=
                    ((oneTape.move (orient growth .left)).moveN
                      (orient growth .left) zeroDistance)
                  have hzero : zeroTape.read = boundarySymbol 0 := by
                    change (Target.boundary (0 : Fin 5)).Matches zeroTape.read
                    simpa [zeroTape, oneTape, twoTape,
                      FullTM0.Tape.read_moveN] using zeroGap.marked
                  have houtward : RouteGaps growth
                      CounterControlValidationConverse.outwardSweep
                      (zeroTape.move (orient growth .right))
                      progress.suffix.finish := by
                    simpa [CounterControlValidationConverse.outwardSweep,
                      zeroTape, oneTape, twoTape] using outwardTrace
                  rcases outwardBodyCore progress zeroTape hzero houtward with
                    ⟨core⟩
                  have honeRead : oneTape.read = boundarySymbol 1 := by
                    change (Target.boundary (1 : Fin 5)).Matches oneTape.read
                    simpa [oneTape, twoTape, FullTM0.Tape.read_moveN] using
                      oneGap.marked
                  have honeCanonical : oneTape =
                      atLogical growth core.tape
                        (boundaryOffset core.registers 1) := by
                    exact
                      CounterControlResumedRouteEmbedding.start_eq_of_leftLeg_found
                        core.represented 0 zeroDistance honeRead zeroGap
                          core.zero_center
                  have htwoRead : twoTape.read = boundarySymbol 2 := by
                    change (Target.boundary (2 : Fin 5)).Matches twoTape.read
                    simpa [twoTape, FullTM0.Tape.read_moveN] using
                      twoGap.marked
                  have htwoCanonical : twoTape =
                      atLogical growth core.tape
                        (boundaryOffset core.registers 2) := by
                    exact
                      CounterControlResumedRouteEmbedding.start_eq_of_leftLeg_found
                        core.represented 1 oneDistance htwoRead oneGap
                          honeCanonical
                  have hsource : current.foundTape.read = boundarySymbol 3 :=
                    foundTape_read_of_boundaryRaw current growth source 0 3
                      .left (directRef growth source 0) hraw
                  have hcanonical : current.foundTape =
                      atLogical growth core.tape
                        (boundaryOffset core.registers 3) := by
                    exact
                      CounterControlResumedRouteEmbedding.start_eq_of_leftLeg_found
                        core.represented 2 twoDistance hsource twoGap
                          htwoCanonical
                  exact reconstructedBody_of_canonicalFound 3
                    (directRef growth source 0) hraw core hcanonical

/-- A reconstructed body immediately feeds the generic monotone body
continuation once a finite first obstruction beyond the core is available. -/
theorem ReconstructedBody.monotone_of_coreTarget
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (body : ReconstructedBody current growth source instruction)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (limit : Nat) (target : Target numTags)
    (represented :
      CounterControlPrefixInstructionResolution.CoreTargetRepresents
        body.registers growth limit target body.tape)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  exact
    CounterControlBodyMonotone.foundMonotoneGuardedEntryOutcome_of_body
      base c hmortal current growth source instruction body.registers limit
      target body.tape hrule represented body.reaches body.strictly_inside
      himmortal

/-- Result of compiling arbitrary validation membership as far as the
available geometry allows.  Every inward position reaches an exact body core
which strictly contains the original gap.  The four outward positions retain
their exact completed suffix and identify the missing validation prefix. -/
inductive CompiledOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) : Type where
  | body (reconstructed :
      ReconstructedBody current growth source instruction)
  | outwardOne
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 4⟩ 1 .right (directRef growth source 4) .preserve)
  | outwardTwo
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 5⟩ 2 .right (directRef growth source 5) .preserve)
  | outwardThree
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 6⟩ 3 .right (directRef growth source 6) .preserve)
  | outwardFour
      (progress : ValidationEnd current growth source instruction)
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 7⟩ 4 .right
          (bodyEntry growth source instruction) .preserve)

/-- Consumer-facing classification: the entire inward half is discharged to
an exact containing body core, leaving precisely the four outward-prefix
cases. -/
theorem classify_compiled
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      validationCommands growth source instruction) :
    Nonempty (CompiledOutcome current growth source instruction) := by
  rcases classify base c hmortal current himmortal growth source instruction
      hrule hcommand with ⟨position⟩
  cases position with
  | inwardThree progress hraw =>
      rcases reconstruct_inwardThree progress hraw with ⟨body⟩
      exact ⟨.body body⟩
  | inwardTwo progress hraw =>
      rcases reconstruct_inwardTwo progress hraw with ⟨body⟩
      exact ⟨.body body⟩
  | inwardOne progress hraw =>
      rcases reconstruct_inwardOne progress hraw with ⟨body⟩
      exact ⟨.body body⟩
  | inwardZero progress hraw =>
      rcases reconstruct_inwardZero progress hraw with ⟨body⟩
      exact ⟨.body body⟩
  | outwardOne progress hraw =>
      exact ⟨.outwardOne progress hraw⟩
  | outwardTwo progress hraw =>
      exact ⟨.outwardTwo progress hraw⟩
  | outwardThree progress hraw =>
      exact ⟨.outwardThree progress hraw⟩
  | outwardFour progress hraw =>
      exact ⟨.outwardFour progress hraw⟩

end

end CounterControlGenuineValidation
end Hooper
end Kari
end LeanWang
