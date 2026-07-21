/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlValidationMortality
import LeanWang.Kari.Hooper.CounterControlCoreRunway
import LeanWang.Kari.Hooper.CounterControlOpenMortality
import LeanWang.Kari.Hooper.CounterControlRouteRoundtrip

/-!
# Round-trip geometry of validation

The inward half of validation discovers the same four blank gaps that the
outward half subsequently traverses in reverse.  This file retains that
geometry on arbitrary immortal orbits, so reconstruction can identify the
post-validation boundary-`4` tape with the logical-entry tape from which
validation departed.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlValidationRoundtrip

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlInstructionSemantics
open CounterControlBridge
open CounterControlValidationMortality
open CounterControlRouteRoundtrip

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Cancelling the inward and outward gap traces -/

/-- Moving the boundary-zero view one logical cell inward and compensating
in the logical coordinate leaves every recentered tape unchanged. -/
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

/-- Opposite logical one-cell moves cancel on a full tape. -/
private theorem move_orient_left_right
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags)) :
    (T.move (orient growth .left)).move (orient growth .right) = T := by
  funext coordinate
  cases growth <;>
    simp [orient, FullTM0.Tape.move]

/-- The outward half of a successful full validation trace retraces the four
inward preserving gaps exactly.  Hence the trace finishes on the boundary-`4`
tape immediately behind its initial first-search tape. -/
theorem sweep_routeGaps_roundtrip
    (growth : Turing.Dir)
    (outer finishTape : FullTM0.Tape (Symbol numTags))
    (hsource : (outer.move (orient growth .right)).read = boundarySymbol 4)
    (htrace : RouteGaps growth MarkerValidation.sweep outer finishTape) :
    finishTape = outer.move (orient growth .right) := by
  unfold MarkerValidation.sweep at htrace
  cases htrace with
  | cons _ _ _ _ d0 gap0 _ tail0 =>
    cases tail0 with
    | cons _ _ _ _ d1 gap1 _ tail1 =>
      cases tail1 with
      | cons _ _ _ _ d2 gap2 _ tail2 =>
        cases tail2 with
        | cons _ _ _ _ d3 gap3 _ tail3 =>
          cases tail3 with
          | cons _ _ _ _ d4 gap4 _ tail4 =>
            cases tail4 with
            | cons _ _ _ _ d5 gap5 _ tail5 =>
              cases tail5 with
              | cons _ _ _ _ d6 gap6 _ tail6 =>
                cases tail6 with
                | last _ _ d7 gap7 =>
                  let T1 :=
                    (outer.moveN (orient growth .left) d0).move
                      (orient growth .left)
                  let T2 :=
                    (T1.moveN (orient growth .left) d1).move
                      (orient growth .left)
                  let T3 :=
                    (T2.moveN (orient growth .left) d2).move
                      (orient growth .left)
                  let T4 :=
                    (T3.moveN (orient growth .left) d3).move
                      (orient growth .right)
                  let T5 :=
                    (T4.moveN (orient growth .right) d4).move
                      (orient growth .right)
                  let T6 :=
                    (T5.moveN (orient growth .right) d5).move
                      (orient growth .right)
                  let T7 :=
                    (T6.moveN (orient growth .right) d6).move
                      (orient growth .right)
                  change SearchGap (fun symbol => symbol = blankSymbol)
                    (Target.boundary 3).Matches outer
                    (orient growth .left) d0 at gap0
                  change SearchGap (fun symbol => symbol = blankSymbol)
                    (Target.boundary 2).Matches T1
                    (orient growth .left) d1 at gap1
                  change SearchGap (fun symbol => symbol = blankSymbol)
                    (Target.boundary 1).Matches T2
                    (orient growth .left) d2 at gap2
                  change SearchGap (fun symbol => symbol = blankSymbol)
                    (Target.boundary 0).Matches T3
                    (orient growth .left) d3 at gap3
                  change SearchGap (fun symbol => symbol = blankSymbol)
                    (Target.boundary 1).Matches T4
                    (orient growth .right) d4 at gap4
                  change SearchGap (fun symbol => symbol = blankSymbol)
                    (Target.boundary 2).Matches T5
                    (orient growth .right) d5 at gap5
                  change SearchGap (fun symbol => symbol = blankSymbol)
                    (Target.boundary 3).Matches T6
                    (orient growth .right) d6 at gap6
                  change SearchGap (fun symbol => symbol = blankSymbol)
                    (Target.boundary 4).Matches T7
                    (orient growth .right) d7 at gap7
                  change T7.moveN (orient growth .right) d7 =
                    outer.move (orient growth .right)
                  have hmarked2 :
                      (T2.moveN (orient growth .left) d2).read =
                        boundarySymbol 1 := by
                    simpa [FullTM0.Tape.read_moveN, Target.Matches] using
                      gap2.marked
                  have hpair3 := reverseGap_pair_continue
                    (T := T2.moveN (orient growth .left) d2)
                    (direction := orient growth .left)
                    (source := (1 : Fin 5)) hmarked2
                    (by simpa only [T3] using gap3)
                    (by simpa only [T3, T4, opposite_orient_left] using gap4)
                  have hT5 :
                      T5 = (T2.moveN (orient growth .left) d2).move
                        (orient growth .right) := by
                    change (T4.moveN (orient growth .right) d4).move
                      (orient growth .right) = _
                    simpa only [T3, T4, opposite_orient_left] using hpair3.2
                  have hmarked1 :
                      (T1.moveN (orient growth .left) d1).read =
                        boundarySymbol 2 := by
                    simpa [FullTM0.Tape.read_moveN, Target.Matches] using
                      gap1.marked
                  have hpair2 := reverseGap_pair_continue
                    (T := T1.moveN (orient growth .left) d1)
                    (direction := orient growth .left)
                    (source := (2 : Fin 5)) hmarked1
                    (by simpa only [T2] using gap2)
                    (by rw [hT5] at gap5
                        simpa only [T2, opposite_orient_left] using gap5)
                  have hT6 :
                      T6 = (T1.moveN (orient growth .left) d1).move
                        (orient growth .right) := by
                    change (T5.moveN (orient growth .right) d5).move
                      (orient growth .right) = _
                    rw [hT5]
                    simpa only [T2, opposite_orient_left] using hpair2.2
                  have hmarked0 :
                      (outer.moveN (orient growth .left) d0).read =
                        boundarySymbol 3 := by
                    simpa [FullTM0.Tape.read_moveN, Target.Matches] using
                      gap0.marked
                  have hpair1 := reverseGap_pair_continue
                    (T := outer.moveN (orient growth .left) d0)
                    (direction := orient growth .left)
                    (source := (3 : Fin 5)) hmarked0
                    (by simpa only [T1] using gap1)
                    (by rw [hT6] at gap6
                        simpa only [T1, opposite_orient_left] using gap6)
                  have hT7 :
                      T7 = (outer.moveN (orient growth .left) d0).move
                        (orient growth .right) := by
                    change (T6.moveN (orient growth .right) d6).move
                      (orient growth .right) = _
                    rw [hT6]
                    simpa only [T1, opposite_orient_left] using hpair1.2
                  have hcancel :
                      (outer.move (orient growth .right)).move
                          (orient growth .left) = outer := by
                    simpa only [opposite_orient_right] using
                      move_move_opposite outer (orient growth .right)
                  have hpair0 := reverseGap_pair_finish
                    (T := outer.move (orient growth .right))
                    (direction := orient growth .left)
                    (source := (4 : Fin 5)) hsource
                    (by rw [hcancel]
                        exact gap0)
                    (by rw [hcancel, opposite_orient_left, ← hT7]
                        exact gap7)
                  rw [hT7]
                  simpa only [hcancel, opposite_orient_left] using hpair0.2

/-! ## Reconstructing the completed validation tape -/

/-- A full successful validation trace simultaneously reconstructs the
finite core and identifies its boundary-`4` view with the tape from which
validation originally departed. -/
theorem sweep_routeGaps_reconstructs
    (growth : Turing.Dir)
    (outer finishTape : FullTM0.Tape (Symbol numTags))
    (hsource : (outer.move (orient growth .right)).read = boundarySymbol 4)
    (htrace : RouteGaps growth MarkerValidation.sweep outer finishTape) :
    ∃ (registers : Registers) (T : FullTM0.Tape (Symbol numTags)),
      CounterControlValidationConverse.BoundaryZeroRepresents
          registers growth T ∧
        CounterControlCoreFrame.CoreRepresents registers growth
          (T.move (orient growth .left)) ∧
        atLogical growth T (RegisterLayout.clockBoundary registers) =
          outer.move (orient growth .right) := by
  have hroundtrip := sweep_routeGaps_roundtrip growth outer finishTape
    hsource htrace
  unfold MarkerValidation.sweep at htrace
  cases htrace with
  | cons _ _ _ _ d0 _gap0 _ tail0 =>
    cases tail0 with
    | cons _ _ _ _ d1 _gap1 _ tail1 =>
      cases tail1 with
      | cons _ _ _ _ d2 _gap2 _ tail2 =>
        cases tail2 with
        | cons _ _ _ _ d3 gap3 _ outwardTrace =>
          let T1 :=
            (outer.moveN (orient growth .left) d0).move
              (orient growth .left)
          let T2 :=
            (T1.moveN (orient growth .left) d1).move
              (orient growth .left)
          let T3 :=
            (T2.moveN (orient growth .left) d2).move
              (orient growth .left)
          let T := T3.moveN (orient growth .left) d3
          change SearchGap (fun symbol => symbol = blankSymbol)
            (Target.boundary 0).Matches T3
            (orient growth .left) d3 at gap3
          have hread : T.read = boundarySymbol 0 := by
            simpa [T, FullTM0.Tape.read, Target.Matches] using gap3.marked
          have houtward : RouteGaps growth
              CounterControlValidationConverse.outwardSweep
              (T.move (orient growth .right)) finishTape := by
            simpa [CounterControlValidationConverse.outwardSweep, T, T3,
              T2, T1] using outwardTrace
          rcases outwardRouteGaps_reconstructs growth T finishTape hread
              houtward with
            ⟨registers, hboundary, hcore, hfinish⟩
          refine ⟨registers, T, hboundary, hcore, ?_⟩
          exact hfinish.symm.trans hroundtrip

/-! ## Operational validation reconstruction -/

/-- Starting from the first inward validation search on an immortal orbit,
the complete generated sweep reconstructs a core and reaches the instruction
body on the exact boundary-`4` tape from which validation departed. -/
theorem validation_reconstructs_roundtrip_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (outer : FullTM0.Tape (Symbol numTags))
    (hsource : (outer.move (orient growth .right)).read = boundarySymbol 4)
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨searchState base c ⟨growth, source, validationSearchBase⟩,
        outer⟩) :
    ∃ (registers : Registers) (T : FullTM0.Tape (Symbol numTags)),
      CounterControlValidationConverse.BoundaryZeroRepresents
          registers growth T ∧
        CounterControlCoreFrame.CoreRepresents registers growth
          (T.move (orient growth .left)) ∧
        atLogical growth T (RegisterLayout.clockBoundary registers) =
          outer.move (orient growth .right) ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
          ⟨resolve base c (bodyEntry growth source instruction),
            outer.move (orient growth .right)⟩ := by
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth source validationSearchBase
          validationDirectBase (bodyEntry growth source instruction)
          MarkerValidation.sweep →
        raw ∈ rawCommands := by
    intro raw hraw
    apply CounterControlPlan.command_mem_rawCommands_of_rule
      growth hrule
    cases instruction <;>
      simp_all [commandsForRule, validationCommands,
        MarkerValidation.sweep, routeCommandsAux, validationSearchBase,
        validationDirectBase, directRef] <;> aesop
  have hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth source validationSearchBase
          validationDirectBase MarkerValidation.sweep →
        rule ∈ rawDirectRules := by
    intro rule hrule'
    apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
      growth hrule
    cases instruction <;>
      simp_all [directRulesForRule, validationRules,
        MarkerValidation.sweep, routeEntryRules, routeContinuationRules,
        routeContinuationRulesFrom, validationSearchBase,
        validationDirectBase, directRef, searchRef] <;> aesop
  rcases reaches_routeGaps_of_immortal base c hmortal himmortal growth
      source validationSearchBase validationDirectBase
      (bodyEntry growth source instruction) ⟨3, .left⟩
      [⟨2, .left⟩, ⟨1, .left⟩, ⟨0, .left⟩,
        ⟨1, .right⟩, ⟨2, .right⟩, ⟨3, .right⟩,
        ⟨4, .right⟩]
      outer hreach hcommands hcontinuations with
    ⟨finishTape, htrace, hfinish⟩
  have hroundtrip := sweep_routeGaps_roundtrip growth outer finishTape
    hsource (by simpa [MarkerValidation.sweep] using htrace)
  rcases sweep_routeGaps_reconstructs growth outer finishTape hsource
      (by simpa [MarkerValidation.sweep] using htrace) with
    ⟨registers, T, hboundary, hcore, htape⟩
  rw [hroundtrip] at hfinish
  exact ⟨registers, T, hboundary, hcore, htape, hfinish⟩

/-! ## Logical successor reconstruction -/

/-- An immortal bounded logical entry is already centered on the boundary
`4` of a reconstructed tag-free core.  The mandatory validation prefix
reaches the instruction body without changing that tape. -/
theorem logical_reconstructs_core_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (hsourceBound : source < logicalSpan)
    (logicalTape : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source, logicalTape⟩) :
    ∃ (instruction : CounterMachine.Instruction)
        (registers : Registers)
        (coreTape : FullTM0.Tape (Symbol numTags)),
      (source, instruction) ∈ GlobalSourceProgram.program ∧
        CounterControlCoreFrame.CoreRepresents registers growth coreTape ∧
        logicalTape = atLogical growth coreTape (layoutEnd registers) ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c growth source, logicalTape⟩
          ⟨resolve base c (bodyEntry growth source instruction),
            logicalTape⟩ := by
  have hdirect :=
    CounterControlArbitraryMortality.direct_source_of_immortal_logical
      base c growth source logicalTape himmortal
  rcases CounterControlLogicalEntry.reaches_validationFirst_of_immortalFrom
      base c growth source hsourceBound logicalTape hdirect himmortal with
    ⟨instruction, hrule, hread, hvalidation⟩
  let outer := logicalTape.move (orient growth .left)
  have hboundaryFour :
      (outer.move (orient growth .right)).read = boundarySymbol 4 := by
    rw [show outer.move (orient growth .right) = logicalTape by
      exact move_orient_left_right growth logicalTape]
    exact hread
  rcases validation_reconstructs_roundtrip_of_immortal base c hmortal
      himmortal growth source instruction hrule outer hboundaryFour
      (by simpa [outer] using hvalidation) with
    ⟨registers, boundaryZeroTape, _hboundary, hcore, htape, hbody⟩
  let coreTape := boundaryZeroTape.move (orient growth .left)
  have houterReturn : outer.move (orient growth .right) = logicalTape := by
    exact move_orient_left_right growth logicalTape
  have hcenter :
      logicalTape = atLogical growth coreTape (layoutEnd registers) := by
    rw [FramedMarkerTape.layoutEnd]
    rw [atLogical_boundaryZero_to_core]
    exact (htape.trans houterReturn).symm
  rw [houterReturn] at hbody
  exact ⟨instruction, registers, coreTape, hrule,
    by simpa [coreTape] using hcore, hcenter, hbody⟩

/-- Source mortality rules out the open-tail alternative for the core
reconstructed at an immortal logical entry.  Consequently there is a least
nonblank obstruction beyond boundary `4`, preceded by an exact blank runway.
The instruction body is still reached on the unchanged logical tape. -/
theorem logical_reconstructs_firstNonblank_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (hsourceBound : source < logicalSpan)
    (logicalTape : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source, logicalTape⟩) :
    ∃ (instruction : CounterMachine.Instruction)
        (registers : Registers)
        (coreTape : FullTM0.Tape (Symbol numTags))
        (distance : Nat),
      (source, instruction) ∈ GlobalSourceProgram.program ∧
        CounterControlCoreFrame.CoreRepresents registers growth coreTape ∧
        logicalTape = atLogical growth coreTape (layoutEnd registers) ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c growth source, logicalTape⟩
          ⟨resolve base c (bodyEntry growth source instruction),
            logicalTape⟩ ∧
        layoutEnd registers < distance ∧
        (∀ position, layoutEnd registers < position →
          position < distance →
            FramedMarkerTape.logicalTape growth coreTape position =
              blankSymbol) ∧
        FramedMarkerTape.logicalTape growth coreTape distance ≠
          blankSymbol := by
  rcases logical_reconstructs_core_of_immortal base c hmortal growth source
      hsourceBound logicalTape himmortal with
    ⟨instruction, registers, coreTape, hrule, hcore, hcenter, hbody⟩
  rcases CounterControlCoreRunway.coreOpen_or_firstNonblank hcore with
    hopen | ⟨distance, hpast, hrunway, hnonblank⟩
  · have hhalts :=
      CounterControlOpenMortality.haltsFrom_logical_of_coreOpen
        base c hmortal growth ⟨source, registers⟩ coreTape
        hsourceBound hopen
    rw [← hcenter] at hhalts
    exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source, logicalTape⟩).mp
          himmortal hhalts)
  · exact ⟨instruction, registers, coreTape, distance, hrule, hcore,
      hcenter, hbody, hpast, hrunway, hnonblank⟩

/-- Consumer-facing form of the first-obstruction theorem.  The obstruction
is classified by an actual controller target, and the body configuration is
stated directly on the reconstructed core tape.  These are exactly the raw
fields of a finite tag-free core target representation. -/
theorem logical_reconstructs_coreTarget_fields_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (hsourceBound : source < logicalSpan)
    (logicalTape : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source, logicalTape⟩) :
    ∃ (instruction : CounterMachine.Instruction)
        (registers : Registers)
        (coreTape : FullTM0.Tape (Symbol numTags))
        (distance : Nat) (target : Target numTags),
      (source, instruction) ∈ GlobalSourceProgram.program ∧
        CounterControlCoreFrame.CoreRepresents registers growth coreTape ∧
        layoutEnd registers < distance ∧
        (∀ position, layoutEnd registers < position →
          position < distance →
            FramedMarkerTape.logicalTape growth coreTape position =
              blankSymbol) ∧
        target.Matches
          (FramedMarkerTape.logicalTape growth coreTape distance) ∧
        logicalTape = atLogical growth coreTape (layoutEnd registers) ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c growth source, logicalTape⟩
          ⟨resolve base c (bodyEntry growth source instruction),
            atLogical growth coreTape (layoutEnd registers)⟩ := by
  rcases logical_reconstructs_firstNonblank_of_immortal base c hmortal
      growth source hsourceBound logicalTape himmortal with
    ⟨instruction, registers, coreTape, distance, hrule, hcore, hcenter,
      hbody, hpast, hrunway, hnonblank⟩
  rcases CounterControlArbitrarySearchMortality.exists_target_matches_of_ne_blank
      (FramedMarkerTape.logicalTape growth coreTape distance) hnonblank with
    ⟨target, htarget⟩
  have hbodyCanonical : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c growth source, logicalTape⟩
      ⟨resolve base c (bodyEntry growth source instruction),
        atLogical growth coreTape (layoutEnd registers)⟩ := by
    rw [← hcenter]
    exact hbody
  exact ⟨instruction, registers, coreTape, distance, target, hrule, hcore,
    hpast, hrunway, htarget, hcenter, hbodyCanonical⟩

end

end CounterControlValidationRoundtrip
end Hooper
end Kari
end LeanWang
