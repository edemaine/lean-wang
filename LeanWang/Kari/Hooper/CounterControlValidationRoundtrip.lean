/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlValidationMortality
import LeanWang.Kari.Hooper.CounterControlCoreRunway
import LeanWang.Kari.Hooper.CounterControlOpenMortality

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

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

@[simp] private theorem opposite_orient_left (growth : Turing.Dir) :
    NestingMachine.opposite (orient growth .left) = orient growth .right := by
  cases growth <;> rfl

@[simp] private theorem opposite_orient_right (growth : Turing.Dir) :
    NestingMachine.opposite (orient growth .right) = orient growth .left := by
  cases growth <;> rfl

/-- Moving back across a reversed search gap returns to the cell immediately
behind the original search head. -/
private theorem reverseGap_finish
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir)
    (distance : Nat) :
    (((T.moveN direction distance).move
        (NestingMachine.opposite direction)).moveN
      (NestingMachine.opposite direction) distance) =
        T.move (NestingMachine.opposite direction) := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.moveN,
      FullTM0.Tape.offset, FullTM0.Tape.move] <;>
    congr 1 <;> ring

/-- A departure, an arbitrary preserving search, its reversed search, and a
second departure end one cell beyond the original boundary. -/
private theorem reverseGap_continue
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir)
    (distance : Nat) :
    (((((T.move direction).moveN direction distance).move
        (NestingMachine.opposite direction)).moveN
      (NestingMachine.opposite direction) distance).move
        (NestingMachine.opposite direction)) =
      T.move (NestingMachine.opposite direction) := by
  rw [reverseGap_finish]
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.move]

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

/-- A boundary target cannot occur at two different first-blank-gap
distances on the same tape. -/
private theorem boundaryGap_distance_unique
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {first second : Nat} {target : Fin 5}
    (hfirst : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches T direction first)
    (hsecond : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches T direction second) :
    first = second := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hblank := hsecond.blank hlt
    have hmarked := hfirst.marked
    rw [show T (FullTM0.Tape.offset direction first) =
        boundarySymbol target by simpa [Target.Matches] using hmarked]
      at hblank
    exact blankSymbol_ne_boundarySymbol target hblank.symm
  · have hblank := hfirst.blank hlt
    have hmarked := hsecond.marked
    rw [show T (FullTM0.Tape.offset direction second) =
        boundarySymbol target by simpa [Target.Matches] using hmarked]
      at hblank
    exact blankSymbol_ne_boundarySymbol target hblank.symm

/-- Returning across the one-cell departure exposes the boundary found by
the preceding preserving search. -/
private theorem read_return_of_gap
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {distance : Nat} {target : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches T direction distance) :
    (((T.moveN direction distance).move direction).move
      (NestingMachine.opposite direction)).read = boundarySymbol target := by
  have hmarked : (T.moveN direction distance).read =
      boundarySymbol target := by
    simpa [FullTM0.Tape.read_moveN, Target.Matches] using hgap.marked
  cases direction <;>
    simpa [NestingMachine.opposite, FullTM0.Tape.read,
      FullTM0.Tape.move] using hmarked

/-- A preserving gap can be traversed in reverse when the symbol immediately
behind its original search head is the desired return marker. -/
private theorem reverseGap_of_source_boundary
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {distance : Nat} {found source : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary found).Matches T direction distance)
    (hsource : (T.move (NestingMachine.opposite direction)).read =
      boundarySymbol source) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      ((T.moveN direction distance).move
        (NestingMachine.opposite direction))
      (NestingMachine.opposite direction) distance := by
  constructor
  · intro i hi
    let j := distance - i - 1
    have hj : j < distance := by
      dsimp [j]
      omega
    have hsum : j + i + 1 = distance := by
      dsimp [j]
      omega
    have hsumInt : (j : Int) + (i : Int) + 1 = (distance : Int) := by
      exact_mod_cast hsum
    have hblank := hgap.blank hj
    cases direction with
    | left =>
      simp only [NestingMachine.opposite, FullTM0.Tape.move_apply_delta,
        FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_left,
        FullTM0.Tape.offset_right, FullTM0.Tape.delta_right] at hblank ⊢
      rw [show -(j : Int) = (i : Int) + 1 + -(distance : Int) by omega]
        at hblank
      exact hblank
    | right =>
      simp only [NestingMachine.opposite, FullTM0.Tape.move_apply_delta,
        FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_left,
        FullTM0.Tape.offset_right, FullTM0.Tape.delta_left] at hblank ⊢
      rw [show (j : Int) = -(i : Int) + -1 + (distance : Int) by omega]
        at hblank
      exact hblank
  · cases direction <;>
      simpa [Target.Matches, FullTM0.Tape.read,
        NestingMachine.opposite, FullTM0.Tape.move_apply_delta,
        FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_left,
        FullTM0.Tape.offset_right, FullTM0.Tape.delta_left,
        FullTM0.Tape.delta_right] using hsource

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
                  have hsource1 :
                      (T3.move (orient growth .right)).read =
                        boundarySymbol 1 := by
                    have hreturn := read_return_of_gap gap2
                    rw [opposite_orient_left] at hreturn
                    simpa [T3] using hreturn
                  have hreverse3 : SearchGap
                      (fun symbol => symbol = blankSymbol)
                      (Target.boundary 1).Matches T4
                      (orient growth .right) d3 := by
                    have hreverse := reverseGap_of_source_boundary
                      (source := (1 : Fin 5)) gap3 (by
                        rw [opposite_orient_left]
                        exact hsource1)
                    rw [opposite_orient_left] at hreverse
                    simpa [T4] using hreverse
                  have hd4 : d4 = d3 := by
                    apply boundaryGap_distance_unique gap4
                    exact hreverse3
                  have hT5 :
                      T5 =
                        (T2.moveN (orient growth .left) d2).move
                          (orient growth .right) := by
                    subst d4
                    have hcontinue := reverseGap_continue
                      (T2.moveN (orient growth .left) d2)
                      (orient growth .left) d3
                    rw [opposite_orient_left] at hcontinue
                    simpa [T3, T4, T5] using hcontinue
                  have hsource2 :
                      (T2.move (orient growth .right)).read =
                        boundarySymbol 2 := by
                    have hreturn := read_return_of_gap gap1
                    rw [opposite_orient_left] at hreturn
                    simpa [T2] using hreturn
                  have hreverse2 : SearchGap
                      (fun symbol => symbol = blankSymbol)
                      (Target.boundary 2).Matches
                      ((T2.moveN (orient growth .left) d2).move
                        (orient growth .right))
                      (orient growth .right) d2 := by
                    have hreverse := reverseGap_of_source_boundary
                      (source := (2 : Fin 5)) gap2 (by
                        rw [opposite_orient_left]
                        exact hsource2)
                    rw [opposite_orient_left] at hreverse
                    exact hreverse
                  have hd5 : d5 = d2 := by
                    apply boundaryGap_distance_unique gap5
                    rw [hT5]
                    simpa using hreverse2
                  have hT6 :
                      T6 =
                        (T1.moveN (orient growth .left) d1).move
                          (orient growth .right) := by
                    subst d5
                    change (T5.moveN (orient growth .right) d2).move
                        (orient growth .right) = _
                    rw [hT5]
                    have hcontinue := reverseGap_continue
                      (T1.moveN (orient growth .left) d1)
                      (orient growth .left) d2
                    rw [opposite_orient_left] at hcontinue
                    simpa [T2] using hcontinue
                  have hsource3 :
                      (T1.move (orient growth .right)).read =
                        boundarySymbol 3 := by
                    have hreturn := read_return_of_gap gap0
                    rw [opposite_orient_left] at hreturn
                    simpa [T1] using hreturn
                  have hreverse1 : SearchGap
                      (fun symbol => symbol = blankSymbol)
                      (Target.boundary 3).Matches
                      ((T1.moveN (orient growth .left) d1).move
                        (orient growth .right))
                      (orient growth .right) d1 := by
                    have hreverse := reverseGap_of_source_boundary
                      (source := (3 : Fin 5)) gap1 (by
                        rw [opposite_orient_left]
                        exact hsource3)
                    rw [opposite_orient_left] at hreverse
                    exact hreverse
                  have hd6 : d6 = d1 := by
                    apply boundaryGap_distance_unique gap6
                    rw [hT6]
                    simpa using hreverse1
                  have hT7 :
                      T7 =
                        (outer.moveN (orient growth .left) d0).move
                          (orient growth .right) := by
                    subst d6
                    change (T6.moveN (orient growth .right) d1).move
                        (orient growth .right) = _
                    rw [hT6]
                    have hcontinue := reverseGap_continue
                      (outer.moveN (orient growth .left) d0)
                      (orient growth .left) d1
                    rw [opposite_orient_left] at hcontinue
                    simpa [T1] using hcontinue
                  have hreverse0 : SearchGap
                      (fun symbol => symbol = blankSymbol)
                      (Target.boundary 4).Matches
                      ((outer.moveN (orient growth .left) d0).move
                        (orient growth .right))
                      (orient growth .right) d0 := by
                    have hreverse := reverseGap_of_source_boundary
                      (source := (4 : Fin 5)) gap0 (by
                        rw [opposite_orient_left]
                        exact hsource)
                    rw [opposite_orient_left] at hreverse
                    exact hreverse
                  have hd7 : d7 = d0 := by
                    apply boundaryGap_distance_unique gap7
                    rw [hT7]
                    simpa using hreverse0
                  subst d7
                  rw [hT7]
                  have hfinish := reverseGap_finish outer
                    (orient growth .left) d0
                  rw [opposite_orient_left] at hfinish
                  exact hfinish

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
    apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
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
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
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
