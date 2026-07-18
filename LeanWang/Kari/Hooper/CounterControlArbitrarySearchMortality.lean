/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlBlankLaunch
import LeanWang.Kari.Hooper.CounterControlLooseFrameMortality

/-!
# Mortality of malformed arbitrary search rays

For a mortal source computation, a least wrong nonblank search symbol cannot
support an immortal run.  Nearby wrong symbols halt in the private scanner.
A farther one bounds a loose nested frame: the mortal canonical computation
either halts there or unwinds, reducing the wrong-gap distance by one.

An entirely blank ray launches a target-free open core.  Consequently, once
the open one-instruction law is supplied, every search entry with no genuine
matching target halts.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlArbitrarySearchMortality

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlSearchSystem
open CounterControlArbitrarySearch CounterControlBlankLaunch
open CounterControlLooseFrameMortality
open CounterControlCanonicalOpenMortality
open CounterControlFrameBacking

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Every nonblank symbol of the tagged controller alphabet is recognized by
some boundary-or-tag target. -/
theorem exists_target_matches_of_ne_blank
    (symbol : Symbol numTags) (hne : symbol ≠ blankSymbol) :
    ∃ target : Target numTags, target.Matches symbol := by
  have hval : symbol.val ≠ 0 := by
    intro hzero
    apply hne
    apply Fin.ext
    simpa [blankSymbol, baseSymbol, MarkerMachine.blankSymbol,
      MarkerMachine.encodeSymbol] using hzero
  by_cases hbase : symbol.val < MarkerMachine.AlphabetSize
  · let label : Fin 5 := ⟨symbol.val - 1, by
      simp only [MarkerMachine.AlphabetSize] at hbase
      omega⟩
    refine ⟨Target.boundary label, ?_⟩
    change symbol = boundarySymbol label
    apply Fin.ext
    simp [label, boundarySymbol, baseSymbol, MarkerMachine.boundarySymbol,
      MarkerMachine.encodeSymbol]
    omega
  · have htagLower : MarkerMachine.AlphabetSize ≤ symbol.val :=
      Nat.le_of_not_gt hbase
    let tag : Fin numTags := ⟨symbol.val - MarkerMachine.AlphabetSize, by
      have hsymbol := symbol.isLt
      simp only [AlphabetSize] at hsymbol
      omega⟩
    refine ⟨Target.anyTag, tag, ?_⟩
    apply Fin.ext
    simp [tag, tagSymbol]
    omega

/-- A blank prefix long enough to exhaust the private scan reaches the exact
initialized loose frame (or the machine has already halted). -/
private theorem search_reaches_initialized_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) (search : Search)
    (outer : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ position ≤
      NestingMachine.bound (CanonicalInitializer.radius c),
      (outer.moveN (command base c search).searchDirection position).read =
        blankSymbol) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ((searchSystem base c).startCfg search outer) ∨
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ((searchSystem base c).startCfg search outer)
        (initializedCfg base c search outer) := by
  have hprefix : ∀ i ≤ NestingMachine.bound
      (CanonicalInitializer.radius c),
      outer (FullTM0.Tape.offset
        (command base c search).searchDirection i) = blankSymbol := by
    intro i hi
    simpa [FullTM0.Tape.read] using hblank i hi
  rcases reaches_exhaustedLaunch_or_haltsFrom base c search outer hprefix with
    hhalts | hlaunch
  · exact Or.inl hhalts
  · right
    exact hlaunch.trans
      (launch_reaches_initialized_of_blankPrefix base c search outer hblank)

/-- Under source mortality, a compiled search whose first nonblank is wrong
halts.  The proof is strong induction on the wrong-gap distance. -/
theorem haltsFrom_search_of_wrongGap
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    ∀ (distance : Nat) (search : Search)
        (outer : FullTM0.Tape (Symbol numTags)),
      WrongGap (fun symbol => symbol = blankSymbol)
        (command base c search).target.Matches outer
        (command base c search).searchDirection distance →
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ((searchSystem base c).startCfg search outer) := by
  intro distance
  induction distance using Nat.strong_induction_on with
  | h distance ih =>
      intro search outer hwrong
      let radius := CanonicalInitializer.radius c
      let bound := NestingMachine.bound radius
      let selected := command base c search
      have hat : CommandAt radius base
          (CounterControlSearchSystem.commandOffset base c search)
          selected (commands base c) := by
        simpa [radius, selected, command,
          CounterControlSearchSystem.commandOffset] using
          (CounterControlWellFormed.compileCommand_commandAt base c search)
      by_cases hnear : distance ≤ bound
      · have hlocal := haltsFrom_scan_of_wrongGap base c hat 0 distance
          (by simpa [bound, radius] using hnear) outer (by
            simpa [selected] using hwrong)
        simpa [searchSystem, SearchSystem.startCfg,
          CounterControlSearchSystem.commandOffset,
          BoundedMarkerProgram.entryState] using hlocal
      · have hfar : bound < distance := Nat.lt_of_not_ge hnear
        have hblankPrefix : ∀ position ≤
            NestingMachine.bound (CanonicalInitializer.radius c),
            (outer.moveN selected.searchDirection position).read =
              blankSymbol := by
          intro position hposition
          have hlt : position < distance := by
            change position ≤ bound at hposition
            omega
          simpa [FullTM0.Tape.read, selected] using hwrong.blank hlt
        rcases search_reaches_initialized_or_haltsFrom base c search outer
            (by simpa [selected] using hblankPrefix) with
          hhalts | hinitialized
        · exact hhalts
        · let observed := outer (FullTM0.Tape.offset
              selected.searchDirection distance)
          have hobservedNonblank : observed ≠ blankSymbol := by
            simpa [observed, selected] using hwrong.nonblank
          rcases exists_target_matches_of_ne_blank observed
              hobservedNonblank with ⟨outerTarget, htarget⟩
          have hlooseGap : SearchGap
              (fun symbol => symbol = blankSymbol) outerTarget.Matches
              outer selected.searchDirection distance := by
            constructor
            · intro i hi
              simpa [selected] using hwrong.blank hi
            · simpa [observed] using htarget
          let frame : LooseFrame base c := {
            growth := selected.searchDirection
            returnTag := selected.returnTag
            outerDistance := distance
            outerTarget := outerTarget
            outer := outer
            returnDirection := by
              dsimp [selected, command]
              rw [compileCommand_returnTag] }
          have hcore : layoutEnd (CanonicalInitializer.registers c) <
              frame.outerDistance := by
            have hend : layoutEnd (CanonicalInitializer.registers c) =
                CanonicalInitializer.span c := by
              simpa [layoutEnd] using
                CanonicalInitializer.clockBoundary_registers c
            change layoutEnd (CanonicalInitializer.registers c) < distance
            rw [hend]
            have hspanBound : CanonicalInitializer.span c < bound := by
              simp [bound, radius, CanonicalInitializer.radius,
                NestingMachine.bound]
            exact hspanBound.trans hfar
          let installed := initializedTape base c search outer
          have hback : BackedBy
              (looseSpec frame (CanonicalInitializer.registers c) hcore)
              installed outer := by
            constructor
            · rfl
            · simpa [looseSpec, frame, selected] using hlooseGap
          have hlogical : LooseLogical base c frame
              (GlobalSourceSemantics.canonicalCounterCfg c)
              (initializedCfg base c search outer) := by
            refine ⟨?_, installed, ?_, ?_,
              CounterControlAbstractTrace.canonicalCounterCfg_state_lt_logicalSpan c⟩
            · simpa [CanonicalInitializer.registers] using hcore
            · simpa [CanonicalInitializer.registers] using hback
            · have hend : layoutEnd
                  (GlobalSourceSemantics.canonicalCounterCfg c).registers =
                    CanonicalInitializer.span c := by
                simpa [CanonicalInitializer.registers, layoutEnd] using
                  CanonicalInitializer.clockBoundary_registers c
              simp [initializedCfg, initializedTape, logicalCfg, frame,
                selected, canonicalEntry, installed, hend]
          rcases not_fixedNonhalting_boundary_or_halts base c hmortal frame
              hlogical with hboundary | hhalts
          · have houterBlank : outer.read = blankSymbol := by
              have hpositive : 0 < distance := by omega
              simpa [FullTM0.Tape.read, selected] using
                hwrong.blank hpositive
            have hresume := BoundedMarkerProgram.machine_resume_reaches
              (coreTable base c) hat outer houterBlank
            have hresume' : FullTM0.Reaches
                (CounterControlNestingBridge.machine base c)
                (boundaryCfg base c frame)
                ((searchSystem base c).startCfg search
                  (outer.move selected.searchDirection)) := by
              simpa [boundaryCfg, frame, selected, searchSystem,
                SearchSystem.startCfg,
                CounterControlSearchSystem.commandOffset,
                CounterControlNestingBridge.machine,
                BoundedMarkerProgram.entryState, radius, command,
                compileCommand_returnTag] using hresume
            have hdistancePositive : 0 < distance := by omega
            obtain ⟨shorter, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
              (Nat.ne_of_gt hdistancePositive)
            have htail : WrongGap (fun symbol => symbol = blankSymbol)
                (command base c search).target.Matches
                (outer.move (command base c search).searchDirection)
                (command base c search).searchDirection shorter := by
              simpa [selected] using hwrong.tail
            have htailHalts := ih shorter (Nat.lt_succ_self shorter)
              search (outer.move (command base c search).searchDirection)
              htail
            apply FullTM0.HaltsFrom.of_reaches hinitialized
            apply FullTM0.HaltsFrom.of_reaches hboundary
            apply FullTM0.HaltsFrom.of_reaches hresume'
            simpa [selected] using htailHalts
          · exact FullTM0.HaltsFrom.of_reaches hinitialized hhalts

/-- On a blank ray, the target-free open instruction law and abstract source
mortality force the search entry to halt. -/
theorem haltsFrom_search_of_blankRay
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : OpenStepContinuesOrHalts base c)
    (search : Search) (outer : FullTM0.Tape (Symbol numTags))
    (hblank : BlankRay (fun symbol => symbol = blankSymbol) outer
      (command base c search).searchDirection) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      ((searchSystem base c).startCfg search outer) := by
  rcases search_reaches_openLogical_or_haltsFrom base c search outer hblank with
    hhalts | ⟨concrete, hreach, hlogical⟩
  · exact hhalts
  · apply FullTM0.HaltsFrom.of_reaches hreach
    exact haltsFrom_openLogical_of_abstract_haltsFrom base c hlaw
      (GlobalSourceMortality.not_fixedNonhalting_haltsFrom hmortal) hlogical

/-- With source mortality and target-free open semantics, absence of a
genuine matching gap makes every compiled search entry halt. -/
theorem haltsFrom_search_of_noGap
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : OpenStepContinuesOrHalts base c)
    (search : Search) (outer : FullTM0.Tape (Symbol numTags))
    (hnoGap : ¬ ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (command base c search).target.Matches outer
        (command base c search).searchDirection distance) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      ((searchSystem base c).startCfg search outer) := by
  rcases searchGap_or_wrongGap_or_blankRay
      (fun symbol : Symbol numTags => symbol = blankSymbol)
      (command base c search).target.Matches outer
      (command base c search).searchDirection with
    hgap | hwrong | hblank
  · exact False.elim (hnoGap hgap)
  · rcases hwrong with ⟨distance, hwrong⟩
    exact haltsFrom_search_of_wrongGap base c hmortal distance search outer
      hwrong
  · exact haltsFrom_search_of_blankRay base c hmortal hlaw search outer
      hblank

/-- Unconditional mortal-source replacement for the earlier launch
obligation: every search reached on an immortal orbit has a genuine target. -/
theorem gap_of_reachable_search_on_immortal_orbit
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : OpenStepContinuesOrHalts base c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    {search : Search} {outer : FullTM0.Tape (Symbol numTags)}
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ((searchSystem base c).startCfg search outer)) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (command base c search).target.Matches outer
        (command base c search).searchDirection distance := by
  classical
  by_contra hgap
  have hhalts := haltsFrom_search_of_noGap base c hmortal hlaw search outer
    hgap
  have hstartHalts := FullTM0.HaltsFrom.of_reaches hreach hhalts
  exact (FullTM0.HaltsFrom.immortalFrom_iff_not
    (CounterControlNestingBridge.machine base c) start).mp himmortal
      hstartHalts

end

end CounterControlArbitrarySearchMortality
end Hooper
end Kari
end LeanWang
