/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlSearchResolution
import LeanWang.Kari.Hooper.CounterControlStepGeometry
import LeanWang.Kari.Hooper.CounterControlTraceSimulation

/-!
# Converse semantics of compiled counter instructions

This file is the halting-aware counterpart of the solved-search instruction
semantics.  A shorter compiled search is only assumed to resolve: it either
finds its marker and continues, or the complete finite controller halts.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlInstructionResolution

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCommandAt CounterControlBridge
open CounterControlScheduleSemantics CounterControlFrameBacking
open CounterControlInstructionSemantics CounterControlSearchResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private theorem reaches_or_halts_trans
    {base : Nat} {c : Nat.Partrec.Code}
    {start middle finish :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (h₁ : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        start middle ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start)
    (h₂ : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        middle finish ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) middle) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        start finish ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start := by
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inr (FullTM0.HaltsFrom.of_reaches h₁ h₂)
  · exact Or.inr h₁

private theorem reaches_trans_or_halts
    {base : Nat} {c : Nat.Partrec.Code}
    {start middle finish :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (h₁ : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start middle)
    (h₂ : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        middle finish ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) middle) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        start finish ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start := by
  exact reaches_or_halts_trans (Or.inl h₁) h₂

private theorem reaches_and_or_halts
    {base : Nat} {c : Nat.Partrec.Code}
    {start finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    {P : Prop}
    (h : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          start finish ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start)
    (hP : P) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          start finish ∧ P) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start := by
  exact h.imp (fun hreach => ⟨hreach, hP⟩) id

/-! ## Resolving cleanup navigation -/

private theorem cleanup_boundary_three_eq_lastGap_two_add_one
    (registers : Registers) :
    boundaryOffset registers 3 = lastGapOffset registers 2 + 1 := by
  simp [boundaryOffset, lastGapOffset]

private theorem cleanup_boundary_two_eq_lastGap_one_add_one
    (registers : Registers) :
    boundaryOffset registers 2 = lastGapOffset registers 1 + 1 := by
  simp [boundaryOffset, lastGapOffset]

private theorem cleanup_boundary_one_eq_lastGap_zero_add_one
    (registers : Registers) :
    boundaryOffset registers 1 = lastGapOffset registers 0 + 1 := by
  simp [boundaryOffset, lastGapOffset]

/-- Resolving-search form of an erasing boundary command.  The exact erase
continuation runs only after the search has found its target. -/
theorem machine_reaches_boundary_erase_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (departure : Option Turing.Dir)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      (.erase departure) ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩
        ⟨resolve base c success,
          match departure with
          | none =>
              (outer.moveN (orient address.growth direction) distance).write
                blankSymbol
          | some departure =>
              ((outer.moveN (orient address.growth direction) distance).write
                blankSymbol).move (orient address.growth departure)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩ := by
  let raw : RawCommand :=
    .boundaryNavigation address expected direction success (.erase departure)
  have hspec := compileRawCommand_spec base c raw hraw
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hspec]
    simpa [raw, compileRawAtTag, Command.target, Command.searchDirection,
      compileNavigationAction] using hgap
  have hsearch := rawSearch_reaches_found_or_halts base c limit hshort raw
    hraw outer distance hdistance hcompiledGap
  rcases hsearch with hfound | hhalts
  · left
    have hfound' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c address),
          outer.moveN (orient address.growth direction) distance⟩ := by
      rw [hspec] at hfound
      simpa [raw, compileRawAtTag, RawCommand.address,
        Command.searchDirection, compileNavigationAction] using hfound
    have hatRaw := CommandAt.compileRawCommand base c raw hraw
    have hat : CommandAt (CanonicalInitializer.radius c) base
        (searchState base c address)
        (.boundaryNavigation expected (orient address.growth direction)
          (resolve base c success) (rawTag raw hraw)
          (.erase (departure.map (orient address.growth))))
        (commands base c) := by
      rw [hspec] at hatRaw
      simpa [raw, compileRawAtTag, RawCommand.address,
        compileNavigationAction] using hatRaw
    have hread :
        (outer.moveN (orient address.growth direction) distance).read =
          boundarySymbol expected := by
      simpa [FullTM0.Tape.read, Target.Matches] using hgap.marked
    have hcontinue : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c address),
          outer.moveN (orient address.growth direction) distance⟩
        ⟨resolve base c success,
          match departure with
          | none =>
              (outer.moveN (orient address.growth direction) distance).write
                blankSymbol
          | some departure =>
              ((outer.moveN (orient address.growth direction) distance).write
                blankSymbol).move (orient address.growth departure)⟩ := by
      have hrun := BoundedMarkerContinuation.machine_reaches_erase_native
        (coreTable base c) expected (orient address.growth direction)
        (resolve base c success) (rawTag raw hraw)
        (departure.map (orient address.growth)) hat
        (outer.moveN (orient address.growth direction) distance) hread
      cases departure <;>
        simpa [CounterControlNestingBridge.machine,
          BoundedMarkerProgram.machine, CounterControlPlan.table] using hrun
    cases departure <;>
      exact hfound'.trans hcontinue
  · right
    simpa [raw, RawCommand.address] using hhalts

/-- Resolving-search form of the cleanup tag command. -/
theorem machine_reaches_tag_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit)
    (address : SearchAddress) (direction : Turing.Dir)
    (success : ControlRef)
    (hraw : RawCommand.tagNavigation address direction success ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.anyTag : Target numTags).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩
        ⟨resolve base c success,
          outer.moveN (orient address.growth direction) distance⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩ := by
  let raw : RawCommand := .tagNavigation address direction success
  have hspec := compileRawCommand_spec base c raw hraw
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hspec]
    simpa [raw, compileRawAtTag, Command.target,
      Command.searchDirection] using hgap
  have hsearch := rawSearch_reaches_found_or_halts base c limit hshort raw
    hraw outer distance hdistance hcompiledGap
  rcases hsearch with hfound | hhalts
  · left
    have hfound' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c address),
          outer.moveN (orient address.growth direction) distance⟩ := by
      rw [hspec] at hfound
      simpa [raw, compileRawAtTag, RawCommand.address,
        Command.searchDirection] using hfound
    have hatRaw := CommandAt.compileRawCommand base c raw hraw
    have hat : CommandAt (CanonicalInitializer.radius c) base
        (searchState base c address)
        (.tagNavigation (orient address.growth direction)
          (resolve base c success) (rawTag raw hraw))
        (commands base c) := by
      rw [hspec] at hatRaw
      simpa [raw, compileRawAtTag, RawCommand.address] using hatRaw
    have hmatch : (Target.anyTag : Target numTags).Matches
        (outer.moveN (orient address.growth direction) distance).read := by
      simpa [FullTM0.Tape.read] using hgap.marked
    have hcontinue :=
      BoundedMarkerContinuation.machine_reaches_navigation_native
        (coreTable base c) (Target.anyTag : Target numTags)
        (orient address.growth direction) (resolve base c success)
        (rawTag raw hraw) hat
        (outer.moveN (orient address.growth direction) distance) hmatch
    exact hfound'.trans hcontinue
  · right
    simpa [raw, RawCommand.address] using hhalts

/-- The four erasing boundary searches either reach the directional return
dispatcher or halt from the cleanup entry.  The last erase lands directly on
the saved tag; no unbounded tag search is needed. -/
theorem machine_reaches_cleanup_return_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit source : Nat)
    (hshort : ShortResolves base c limit)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hlimit : spec.outerDistance = limit)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨controllerReturn base c spec.growth,
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterZero spec T) 0⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩ := by
  let rawThree : RawCommand :=
    .boundaryNavigation ⟨spec.growth, source, cleanupSearchBase⟩ 3 .left
      (searchRef spec.growth source (cleanupSearchBase + 1))
      (.erase (some .left))
  let rawTwo : RawCommand :=
    .boundaryNavigation ⟨spec.growth, source, cleanupSearchBase + 1⟩ 2 .left
      (searchRef spec.growth source (cleanupSearchBase + 2))
      (.erase (some .left))
  let rawOne : RawCommand :=
    .boundaryNavigation ⟨spec.growth, source, cleanupSearchBase + 2⟩ 1 .left
      (searchRef spec.growth source (cleanupSearchBase + 3))
      (.erase (some .left))
  let rawZero : RawCommand :=
    .boundaryNavigation ⟨spec.growth, source, cleanupSearchBase + 3⟩ 0 .left
      (.sharedReturn spec.growth)
      (.erase (some .left))
  have hrawThree : rawThree ∈ rawCommands := hcommands rawThree (by
    simp [rawThree, cleanupCommands])
  have hrawTwo : rawTwo ∈ rawCommands := hcommands rawTwo (by
    simp [rawTwo, cleanupCommands])
  have hrawOne : rawOne ∈ rawCommands := hcommands rawOne (by
    simp [rawOne, cleanupCommands])
  have hrawZero : rawZero ∈ rawCommands := hcommands rawZero (by
    simp [rawZero, cleanupCommands])
  have hdistanceThree : RegisterLayout.values spec.registers 3 + 1 < limit := by
    rw [← hlimit]
    have hcore := spec.core_before_target
    rw [layoutEnd_eq] at hcore
    simp [RegisterLayout.values]
    omega
  have hdistanceTwo : RegisterLayout.values spec.registers 2 < limit := by
    rw [← hlimit]
    exact registerValue_lt_outerDistance h (2 : Fin 4)
  have hdistanceOne : RegisterLayout.values spec.registers 1 < limit := by
    rw [← hlimit]
    exact registerValue_lt_outerDistance h (1 : Fin 4)
  have hdistanceZero : RegisterLayout.values spec.registers 0 < limit := by
    rw [← hlimit]
    exact registerValue_lt_outerDistance h (0 : Fin 4)
  have hrunThree := machine_reaches_boundary_erase_or_halts base c limit
    hshort ⟨spec.growth, source, cleanupSearchBase⟩ 3 .left
    (searchRef spec.growth source (cleanupSearchBase + 1)) (some .left)
    hrawThree
    (atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
      (boundaryOffset spec.registers 4))
    (RegisterLayout.values spec.registers 3 + 1) hdistanceThree
    (CounterControlCleanupSemantics.cleanupGap_three h)
  have hthree :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterFour spec T)
              (layoutEnd spec.registers)⟩
          ⟨searchState base c
              ⟨spec.growth, source, cleanupSearchBase + 1⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterThree spec T)
              (lastGapOffset spec.registers 2)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterFour spec T)
              (layoutEnd spec.registers)⟩ := by
    rcases hrunThree with hrun | hhalts
    · left
      have hstart : boundaryOffset spec.registers 4 =
          boundaryOffset spec.registers 3 +
            (RegisterLayout.values spec.registers 3 + 1) := by
        simp [boundaryOffset, CounterLayout.boundaryPos]
        omega
      have hfound :
          (atLogical spec.growth
              (CounterControlCleanupSemantics.afterFour spec T)
              (boundaryOffset spec.registers 4)).moveN
              (orient spec.growth .left)
              (RegisterLayout.values spec.registers 3 + 1) =
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterFour spec T)
              (boundaryOffset spec.registers 3) := by
        rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
      simp only at hrun
      rw [hfound, orient_eq_orientDirection,
        cleanup_boundary_three_eq_lastGap_two_add_one,
        erase_departLeft_atLogical] at hrun
      rw [← cleanup_boundary_three_eq_lastGap_two_add_one] at hrun
      simpa [rawThree, searchRef, CounterControlPlan.resolve,
        CounterControlCleanupSemantics.afterThree,
        CounterControlCleanupSemantics.clearBoundary] using hrun
    · exact Or.inr hhalts
  have hrunTwo := machine_reaches_boundary_erase_or_halts base c limit
    hshort ⟨spec.growth, source, cleanupSearchBase + 1⟩ 2 .left
    (searchRef spec.growth source (cleanupSearchBase + 2)) (some .left)
    hrawTwo
    (atLogical spec.growth (CounterControlCleanupSemantics.afterThree spec T)
      (lastGapOffset spec.registers 2))
    (RegisterLayout.values spec.registers 2) hdistanceTwo
    (CounterControlCleanupSemantics.cleanupGap_two h)
  have htwo :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨spec.growth, source, cleanupSearchBase + 1⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterThree spec T)
              (lastGapOffset spec.registers 2)⟩
          ⟨searchState base c
              ⟨spec.growth, source, cleanupSearchBase + 2⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterTwo spec T)
              (lastGapOffset spec.registers 1)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨spec.growth, source, cleanupSearchBase + 1⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterThree spec T)
              (lastGapOffset spec.registers 2)⟩ := by
    rcases hrunTwo with hrun | hhalts
    · left
      have hstart : lastGapOffset spec.registers 2 =
          boundaryOffset spec.registers 2 +
            RegisterLayout.values spec.registers 2 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos]
        omega
      have hfound :
          (atLogical spec.growth
              (CounterControlCleanupSemantics.afterThree spec T)
              (lastGapOffset spec.registers 2)).moveN
              (orient spec.growth .left)
              (RegisterLayout.values spec.registers 2) =
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterThree spec T)
              (boundaryOffset spec.registers 2) := by
        rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
      simp only at hrun
      rw [hfound, orient_eq_orientDirection,
        cleanup_boundary_two_eq_lastGap_one_add_one,
        erase_departLeft_atLogical] at hrun
      rw [← cleanup_boundary_two_eq_lastGap_one_add_one] at hrun
      simpa [rawTwo, searchRef, CounterControlPlan.resolve,
        CounterControlCleanupSemantics.afterTwo,
        CounterControlCleanupSemantics.clearBoundary] using hrun
    · exact Or.inr hhalts
  have hrunOne := machine_reaches_boundary_erase_or_halts base c limit
    hshort ⟨spec.growth, source, cleanupSearchBase + 2⟩ 1 .left
    (searchRef spec.growth source (cleanupSearchBase + 3)) (some .left)
    hrawOne
    (atLogical spec.growth (CounterControlCleanupSemantics.afterTwo spec T)
      (lastGapOffset spec.registers 1))
    (RegisterLayout.values spec.registers 1) hdistanceOne
    (CounterControlCleanupSemantics.cleanupGap_one h)
  have hone :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨spec.growth, source, cleanupSearchBase + 2⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterTwo spec T)
              (lastGapOffset spec.registers 1)⟩
          ⟨searchState base c
              ⟨spec.growth, source, cleanupSearchBase + 3⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterOne spec T)
              (lastGapOffset spec.registers 0)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨spec.growth, source, cleanupSearchBase + 2⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterTwo spec T)
              (lastGapOffset spec.registers 1)⟩ := by
    rcases hrunOne with hrun | hhalts
    · left
      have hstart : lastGapOffset spec.registers 1 =
          boundaryOffset spec.registers 1 +
            RegisterLayout.values spec.registers 1 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos]
        omega
      have hfound :
          (atLogical spec.growth
              (CounterControlCleanupSemantics.afterTwo spec T)
              (lastGapOffset spec.registers 1)).moveN
              (orient spec.growth .left)
              (RegisterLayout.values spec.registers 1) =
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterTwo spec T)
              (boundaryOffset spec.registers 1) := by
        rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
      simp only at hrun
      rw [hfound, orient_eq_orientDirection,
        cleanup_boundary_one_eq_lastGap_zero_add_one,
        erase_departLeft_atLogical] at hrun
      rw [← cleanup_boundary_one_eq_lastGap_zero_add_one] at hrun
      simpa [rawOne, searchRef, CounterControlPlan.resolve,
        CounterControlCleanupSemantics.afterOne,
        CounterControlCleanupSemantics.clearBoundary] using hrun
    · exact Or.inr hhalts
  have hrunZero := machine_reaches_boundary_erase_or_halts base c limit
    hshort ⟨spec.growth, source, cleanupSearchBase + 3⟩ 0 .left
    (.sharedReturn spec.growth) (some .left)
    hrawZero
    (atLogical spec.growth (CounterControlCleanupSemantics.afterOne spec T)
      (lastGapOffset spec.registers 0))
    (RegisterLayout.values spec.registers 0) hdistanceZero
    (CounterControlCleanupSemantics.cleanupGap_zero h)
  have hzero :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨spec.growth, source, cleanupSearchBase + 3⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterOne spec T)
              (lastGapOffset spec.registers 0)⟩
          ⟨controllerReturn base c spec.growth,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterZero spec T) 0⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨spec.growth, source, cleanupSearchBase + 3⟩,
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterOne spec T)
              (lastGapOffset spec.registers 0)⟩ := by
    rcases hrunZero with hrun | hhalts
    · left
      have hstart : lastGapOffset spec.registers 0 =
          1 + RegisterLayout.values spec.registers 0 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos]
        omega
      have hfound :
          (atLogical spec.growth
              (CounterControlCleanupSemantics.afterOne spec T)
              (lastGapOffset spec.registers 0)).moveN
              (orient spec.growth .left)
              (RegisterLayout.values spec.registers 0) =
            atLogical spec.growth
              (CounterControlCleanupSemantics.afterOne spec T) 1 := by
        rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
      simp only at hrun
      rw [hfound, orient_eq_orientDirection, erase_departLeft_atLogical] at hrun
      simpa [rawZero, searchRef, CounterControlPlan.resolve,
        CounterControlCleanupSemantics.afterZero,
        CounterControlCleanupSemantics.clearBoundary] using hrun
    · exact Or.inr hhalts
  exact reaches_or_halts_trans hthree
    (reaches_or_halts_trans htwo
      (reaches_or_halts_trans hone hzero))

/-- Resolving cleanup through the shared return dispatcher. -/
theorem machine_reaches_cleanup_resume_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hshort : ShortResolves base c spec.outerDistance)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterTag spec T) 0⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩ := by
  have hreturn := machine_reaches_cleanup_return_or_halts base c
    spec.outerDistance source hshort h rfl hcommands
  have hread :
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterZero spec T) 0).read =
        tagSymbol spec.returnTag := by
    rw [atLogical_read]
    simp only [CounterControlCleanupSemantics.afterZero,
      CounterControlCleanupSemantics.afterOne,
      CounterControlCleanupSemantics.afterTwo,
      CounterControlCleanupSemantics.afterThree,
      CounterControlCleanupSemantics.afterFour,
      CounterControlCleanupSemantics.clearBoundary]
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
    exact h.tag
  have hdispatch :=
    CounterControlCleanupSemantics.machine_sharedReturn_reaches_resume
      base c spec.returnTag
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterZero spec T) 0) hread
  have hdispatch' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c spec.growth,
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterZero spec T) 0⟩
      ⟨resumeState (CanonicalInitializer.radius c)
          (searchState base c (rawCommands.get spec.returnTag).address),
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterTag spec T) 0⟩ := by
    simpa [hreturnDirection, CounterControlCleanupSemantics.afterTag,
      atLogical_write] using hdispatch
  exact reaches_or_halts_trans hreturn (Or.inl hdispatch')

/-- Backed-frame form of resolving cleanup: successful erasure restores the
suspended outer tape exactly. -/
theorem machine_reaches_cleanup_outer_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hshort : ShortResolves base c spec.outerDistance)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address), outer⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩ := by
  have hrun := machine_reaches_cleanup_resume_or_halts base c source
    hback.represents hreturnDirection hshort hcommands
  rw [afterTag_eq_outer hback] at hrun
  simpa [atLogical] using hrun

/-- From the exact outward-collision endpoint, resolving cleanup either
restores the suspended outer configuration or halts. -/
theorem machine_reaches_collisionCleanup_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hshort : ShortResolves base c spec.outerDistance)
    (hentry : CounterControlCleanupSemantics.cleanupEntryRule
      spec.growth source ∈ rawDirectRules)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterFour spec T)
            spec.outerDistance⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address), outer⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterFour spec T)
            spec.outerDistance⟩ := by
  have h := hback.represents
  have htargetRead :
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterFour spec T)
        spec.outerDistance).read =
        logicalTape spec.growth T spec.outerDistance := by
    rw [atLogical_read]
    simp only [CounterControlCleanupSemantics.afterFour,
      CounterControlCleanupSemantics.clearBoundary]
    apply writeLogical_of_ne
    rw [boundaryOffset_four]
    omega
  have htargetNonblank :
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterFour spec T)
        spec.outerDistance).read ≠ blankSymbol := by
    rw [htargetRead]
    intro hblank
    exact target_not_blank spec.outerTarget (hblank ▸ h.target)
  have hentryRunLocal :=
    CounterControlDirectSemantics.reaches_directRule base c
      (CounterControlCleanupSemantics.cleanupEntryRule spec.growth source)
      hentry
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterFour spec T)
        spec.outerDistance) htargetNonblank
  have hmove :
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterFour spec T)
        spec.outerDistance).move (orient spec.growth .left) =
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterFour spec T)
          (layoutEnd spec.registers) := by
    rw [← hcollision, orient_eq_orientDirection, atLogical_move_left]
  have hentryRun : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source testDirectSlot),
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterFour spec T)
          spec.outerDistance⟩
      ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterFour spec T)
          (layoutEnd spec.registers)⟩ := by
    simp only [CounterControlCleanupSemantics.cleanupEntryRule] at hentryRunLocal
    rw [hmove] at hentryRunLocal
    change FullTM0.Reaches
      (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
    simpa [CounterControlCleanupSemantics.cleanupEntryRule, searchRef,
      CounterControlPlan.resolve] using hentryRunLocal
  exact reaches_trans_or_halts hentryRun
    (machine_reaches_cleanup_outer_or_halts base c source hback
      hreturnDirection hshort hcommands)

/-! ## Validation -/

private theorem validationCommand_mem
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) {raw : RawCommand}
    (hraw : raw ∈ validationCommands growth source instruction) :
    raw ∈ commandsForRule growth (source, instruction) := by
  cases instruction <;> simp [commandsForRule, hraw]

private theorem validationRule_mem
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) {raw : RawDirectRule}
    (hraw : raw ∈ validationRules growth source) :
    raw ∈ directRulesForRule growth (source, instruction) := by
  cases instruction <;> simp [directRulesForRule, hraw]

/-- Whole-list wrapper for a nonempty resolving route. -/
theorem route_reaches_or_halts_at_of_ne_nil
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat)
    (source after : ControlRef) (sourceBoundary : Fin 5)
    (legs : List MarkerValidation.Leg) (hne : legs ≠ [])
    (T : FullTM0.Tape (Symbol numTags)) (sourcePosition finishPosition : Nat)
    (hsource : (atLogical growth T sourcePosition).read =
      boundarySymbol sourceBoundary)
    (hexec : RouteExecutesWithin growth T limit legs
      sourcePosition finishPosition)
    (hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth counterState searchSlot directSlot
          after legs → raw ∈ rawCommands)
    (hrules : ∀ rule,
      rule ∈ routeEntryRules growth counterState source sourceBoundary
            searchSlot legs ++
          routeContinuationRules growth counterState searchSlot directSlot
            legs →
        rule ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c source, atLogical growth T sourcePosition⟩
        ⟨resolve base c after, atLogical growth T finishPosition⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c source, atLogical growth T sourcePosition⟩ := by
  cases legs with
  | nil => exact (hne rfl).elim
  | cons first rest =>
      exact route_reaches_or_halts_at base c limit hshort growth counterState
        searchSlot directSlot source after sourceBoundary first rest T
        sourcePosition finishPosition hsource hexec hcommands hrules

/-- The mandatory validation sweep reaches the selected instruction body, or
one of its shorter searches makes the complete controller halt. -/
theorem machine_reaches_validation_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (source : Nat) (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (hgrowth : spec.growth = growth)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (bodyEntry growth source instruction),
          atLogical growth T (layoutEnd spec.registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd spec.registers)⟩ := by
  subst growth
  have hcommands : ∀ raw,
      raw ∈ validationCommands spec.growth source instruction →
        raw ∈ rawCommands := by
    intro raw hraw
    exact command_mem_rawCommands_of_rule spec.growth hrule
      (validationCommand_mem spec.growth source instruction hraw)
  have hrules : ∀ raw,
      raw ∈ validationRules spec.growth source →
        raw ∈ rawDirectRules := by
    intro raw hraw
    exact directRule_mem_rawDirectRules_of_rule spec.growth hrule
      (validationRule_mem spec.growth source instruction hraw)
  have hroute := route_reaches_or_halts_at base c spec.outerDistance hshort
    spec.growth source validationSearchBase validationDirectBase
    (.logical spec.growth source) (bodyEntry spec.growth source instruction)
    4 ⟨3, .left⟩
    [⟨2, .left⟩, ⟨1, .left⟩, ⟨0, .left⟩,
      ⟨1, .right⟩, ⟨2, .right⟩, ⟨3, .right⟩,
      ⟨4, .right⟩]
    T (layoutEnd spec.registers) (layoutEnd spec.registers)
    h.read_boundary_four (by
      simpa only [MarkerValidation.sweep] using validation_executesWithin h)
    (by intro raw hraw; exact hcommands raw hraw)
    (by intro raw hraw; exact hrules raw hraw)
  simpa [validationCommands, validationRules, logicalState,
    CounterControlPlan.resolve] using hroute

/-! ## Halting-aware marker shifts -/

/-- Resolving-search counterpart of the native outward marker shift. -/
theorem machine_reaches_incrementShift_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (growth : Turing.Dir)
    (counterState searchSlot source : Nat) (expected : Fin 5)
    (success : ControlRef) (collision : Option ControlRef)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ expected .left .right success
        (some .left) collision ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches
      (atLogical growth T (source + distance))
      (OrientedMarkerTape.orientDirection growth .left) distance)
    (hblank : logicalTape growth T (source + 1) = blankSymbol) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (source + distance)⟩
        ⟨resolve base c success,
          atLogical growth
            (writeLogical growth
              (writeLogical growth T source blankSymbol) (source + 1)
                (boundarySymbol expected)) source⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (source + distance)⟩ := by
  let raw : RawCommand :=
    .markerShift ⟨growth, counterState, searchSlot⟩ expected .left .right
      success (some .left) collision
  let move : MarkerProgram.Move :=
    ⟨expected, CounterControlPlan.orient growth .left,
      CounterControlPlan.orient growth .right⟩
  have hspec := compileRawCommand_spec base c raw hraw
  have hcommand : compileRawCommand base c raw hraw =
      .markerShift move (resolve base c success) (rawTag raw hraw)
        (some (CounterControlPlan.orient growth .left))
        (collision.map (resolve base c)) := by
    rw [hspec]
    simp [raw, move, compileRawAtTag, CounterControlPlan.orient]
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches
      (atLogical growth T (source + distance))
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hcommand]
    simpa [move, Command.target, Command.searchDirection,
      orient_eq_orientDirection] using hgap
  have hsearch := rawSearch_reaches_found_or_halts base c limit hshort raw hraw
    (atLogical growth T (source + distance)) distance hdistance hcompiledGap
  rcases hsearch with hfound | hhalts
  · left
    have hmove :
        (atLogical growth T (source + distance)).moveN
            (CounterControlPlan.orient growth .left) distance =
          atLogical growth T source := by
      simpa only [orient_eq_orientDirection] using
        atLogical_moveN_left growth T source distance
    have hfound' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (source + distance)⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c ⟨growth, counterState, searchSlot⟩),
          atLogical growth T source⟩ := by
      rw [hcommand] at hfound
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address,
          atLogical growth T (source + distance)⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c raw.address),
          (atLogical growth T (source + distance)).moveN
            move.searchDirection distance⟩ at hfound
      rw [show move.searchDirection =
        CounterControlPlan.orient growth .left from rfl, hmove] at hfound
      simpa [raw, RawCommand.address] using hfound
    have hatRaw := CommandAt.compileRawCommand base c raw hraw
    have hat : CommandAt (CanonicalInitializer.radius c) base
        (searchState base c ⟨growth, counterState, searchSlot⟩)
        (.markerShift move (resolve base c success) (rawTag raw hraw)
          (some (CounterControlPlan.orient growth .left))
          (collision.map (resolve base c)))
        (commands base c) := by
      rw [hspec] at hatRaw
      simpa [raw, move, compileRawAtTag, RawCommand.address] using hatRaw
    have hread :
        (atLogical growth T source).read = boundarySymbol expected := by
      rw [← hmove]
      simpa [Target.Matches] using hgap.marked
    have hblankPhysical :
        ((((atLogical growth T source).write blankSymbol).move
              move.shiftDirection).read = blankSymbol) := by
      change (((atLogical growth T source).write blankSymbol).move
        (CounterControlPlan.orient growth .right)).read = blankSymbol
      rw [atLogical_write]
      rw [show CounterControlPlan.orient growth .right =
        OrientedMarkerTape.orientDirection growth .right by
          exact orient_eq_orientDirection growth .right]
      rw [atLogical_move_right, atLogical_read]
      rw [writeLogical_of_ne growth T source (source + 1) blankSymbol
        (by omega)]
      exact hblank
    have hcontinue :=
      BoundedMarkerContinuation.machine_reaches_shift_success_native
        (coreTable base c) move (resolve base c success) (rawTag raw hraw)
        (some (CounterControlPlan.orient growth .left))
        (collision.map (resolve base c)) hat
        (atLogical growth T source) hread hblankPhysical
    have hrun := hfound'.trans hcontinue
    dsimp only [move] at hrun
    rw [orient_eq_orientDirection growth .right,
      orient_eq_orientDirection growth .left] at hrun
    rw [shiftRight_departLeft_atLogical] at hrun
    exact hrun
  · right
    simpa [raw, RawCommand.address] using hhalts

/-- Resolving-search counterpart of the native inward marker shift. -/
theorem machine_reaches_decrementShift_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (growth : Turing.Dir)
    (counterState searchSlot origin destination distance : Nat)
    (expected : Fin 5) (success : ControlRef)
    (collision : Option ControlRef)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ expected .right .left success
        (some .right) collision ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hposition : origin + distance = destination + 1)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches (atLogical growth T origin)
      (OrientedMarkerTape.orientDirection growth .right) distance)
    (hblank : logicalTape growth T destination = blankSymbol) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T origin⟩
        ⟨resolve base c success,
          atLogical growth
            (writeLogical growth
              (writeLogical growth T (destination + 1) blankSymbol)
                destination (boundarySymbol expected)) (destination + 1)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T origin⟩ := by
  let raw : RawCommand :=
    .markerShift ⟨growth, counterState, searchSlot⟩ expected .right .left
      success (some .right) collision
  let move : MarkerProgram.Move :=
    ⟨expected, CounterControlPlan.orient growth .right,
      CounterControlPlan.orient growth .left⟩
  have hspec := compileRawCommand_spec base c raw hraw
  have hcommand : compileRawCommand base c raw hraw =
      .markerShift move (resolve base c success) (rawTag raw hraw)
        (some (CounterControlPlan.orient growth .right))
        (collision.map (resolve base c)) := by
    rw [hspec]
    simp [raw, move, compileRawAtTag, CounterControlPlan.orient]
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches
      (atLogical growth T origin)
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hcommand]
    simpa [move, Command.target, Command.searchDirection,
      orient_eq_orientDirection] using hgap
  have hsearch := rawSearch_reaches_found_or_halts base c limit hshort raw hraw
    (atLogical growth T origin) distance hdistance hcompiledGap
  rcases hsearch with hfound | hhalts
  · left
    have hmove :
        (atLogical growth T origin).moveN
            (CounterControlPlan.orient growth .right) distance =
          atLogical growth T (destination + 1) := by
      rw [show CounterControlPlan.orient growth .right =
        OrientedMarkerTape.orientDirection growth .right by
          exact orient_eq_orientDirection growth .right]
      rw [atLogical_moveN_right, hposition]
    have hfound' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T origin⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c ⟨growth, counterState, searchSlot⟩),
          atLogical growth T (destination + 1)⟩ := by
      rw [hcommand] at hfound
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address, atLogical growth T origin⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c raw.address),
          (atLogical growth T origin).moveN move.searchDirection distance⟩
        at hfound
      rw [show move.searchDirection =
        CounterControlPlan.orient growth .right from rfl, hmove] at hfound
      simpa [raw, RawCommand.address] using hfound
    have hatRaw := CommandAt.compileRawCommand base c raw hraw
    have hat : CommandAt (CanonicalInitializer.radius c) base
        (searchState base c ⟨growth, counterState, searchSlot⟩)
        (.markerShift move (resolve base c success) (rawTag raw hraw)
          (some (CounterControlPlan.orient growth .right))
          (collision.map (resolve base c)))
        (commands base c) := by
      rw [hspec] at hatRaw
      simpa [raw, move, compileRawAtTag, RawCommand.address] using hatRaw
    have hread :
        (atLogical growth T (destination + 1)).read =
          boundarySymbol expected := by
      rw [← hmove]
      simpa [Target.Matches] using hgap.marked
    have hblankPhysical :
        ((((atLogical growth T (destination + 1)).write blankSymbol).move
              move.shiftDirection).read = blankSymbol) := by
      change (((atLogical growth T (destination + 1)).write blankSymbol).move
        (CounterControlPlan.orient growth .left)).read = blankSymbol
      rw [atLogical_write]
      rw [show CounterControlPlan.orient growth .left =
        OrientedMarkerTape.orientDirection growth .left by
          exact orient_eq_orientDirection growth .left]
      rw [atLogical_move_left, atLogical_read]
      rw [writeLogical_of_ne growth T (destination + 1) destination blankSymbol
        (by omega)]
      exact hblank
    have hcontinue :=
      BoundedMarkerContinuation.machine_reaches_shift_success_native
        (coreTable base c) move (resolve base c success) (rawTag raw hraw)
        (some (CounterControlPlan.orient growth .right))
        (collision.map (resolve base c)) hat
        (atLogical growth T (destination + 1)) hread hblankPhysical
    have hrun := hfound'.trans hcontinue
    dsimp only [move] at hrun
    rw [orient_eq_orientDirection growth .left,
      orient_eq_orientDirection growth .right] at hrun
    rw [shiftLeft_departRight_atLogical] at hrun
    exact hrun
  · right
    simpa [raw, RawCommand.address] using hhalts

/-! ## Canonical shift normalization -/

/-- One internal canonical outward shift resolves to its exact installed
frame update, or halts at the shift's search entry. -/
theorem machine_reaches_incrementInternal_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hdistance : RegisterLayout.values spec.registers i < limit)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hsameEnd : layoutEnd next = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.castSucc) i.castSucc =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.castSucc .left .right
      success (some .left) collision ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (lastGapOffset spec.registers i)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag T)
            (boundaryOffset spec.registers i.castSucc)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (lastGapOffset spec.registers i)⟩ := by
  let source := boundaryOffset spec.registers i.castSucc
  let distance := RegisterLayout.values spec.registers i
  let U := writeLogical spec.growth
    (writeLogical spec.growth T source blankSymbol) (source + 1)
      (boundarySymbol i.castSucc)
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.castSucc).Matches
      (atLogical spec.growth T (lastGapOffset spec.registers i))
      (OrientedMarkerTape.orientDirection spec.growth .left) distance := by
    change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.castSucc) _ _ _
    exact h.searchGap_adjacent_left i
  have hstart : lastGapOffset spec.registers i = source + distance := by
    exact lastGapOffset_eq_boundaryOffset_add_value spec.registers i
  have hblank : logicalTape spec.growth T (source + 1) = blankSymbol := by
    have hgapBlank := h.gap_blank i 0 hpositive
    have hcoordinate : source + 1 = firstGapOffset spec.registers i := by
      simp [source, firstGapOffset, boundaryOffset]
    have hcoordinateInt : (source : Int) + 1 =
        firstGapOffset spec.registers i := by
      exact_mod_cast hcoordinate
    rw [hcoordinateInt]
    simpa using hgapBlank
  have hrun := machine_reaches_incrementShift_or_halts base c limit hshort
    spec.growth counterState searchSlot source i.castSucc success collision
    hraw T distance hdistance (by simpa [hstart] using hgap) hblank
  rcases hrun with hrun | hhalts
  · left
    have hsourceBound : source ≤ layoutEnd spec.registers := by
      change CounterLayout.boundaryPos
          (RegisterLayout.values spec.registers) i + 1 ≤
        CounterLayout.boundaryPos (RegisterLayout.values spec.registers) 4 + 1
      apply Nat.add_le_add_right
      exact CounterLayout.boundaryPos_mono
        (RegisterLayout.values spec.registers) (show (i : Nat) ≤ 4 by omega)
    have htargetBound : source + 1 ≤ layoutEnd next := by
      rw [hsameEnd]
      have hnext := CounterLayout.boundaryPos_succ
        (RegisterLayout.values spec.registers) i
      change CounterLayout.boundaryPos
          (RegisterLayout.values spec.registers) i + 1 + 1 ≤
        CounterLayout.boundaryPos (RegisterLayout.values spec.registers) 4 + 1
      have hmono := CounterLayout.boundaryPos_mono
        (RegisterLayout.values spec.registers)
        (show (i : Nat) + 1 ≤ 4 by omega)
      omega
    have hrep : Represents (updateSpec spec next hnextCore) U := by
      apply moveRight_represents h next i.castSucc hnextCore
      · omega
      · omega
      · exact hsourceBound
      · exact htargetBound
      · intro hlt
        omega
      · exact hmove
    have hU : U = install next spec.growth spec.returnTag T := by
      apply moveRight_eq_install next i.castSucc hnextCore
      · simp [boundaryOffset]
      · exact hsourceBound.trans (by omega)
      · exact htargetBound
      · exact hrep
    simpa [U, hU, hstart] using hrun
  · right
    simpa [hstart] using hhalts

/-- One canonical inward shift resolves to the normalized installed frame, or
halts at the shift's search entry. -/
theorem machine_reaches_decrementCanonical_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (label : Fin 5)
    (origin distance : Nat)
    (hsourcePositive : 1 < boundaryOffset spec.registers label)
    (horigin : origin + distance = boundaryOffset spec.registers label)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary label).Matches (atLogical spec.growth T origin)
      (OrientedMarkerTape.orientDirection spec.growth .right) distance)
    (hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers label - 1 : Nat) : Int) = blankSymbol)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers label ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers label - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers label = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers label) label =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ label .right .left success
      (some .right) collision ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T origin⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers label) blankSymbol))
            (boundaryOffset spec.registers label)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T origin⟩ := by
  let source := boundaryOffset spec.registers label
  let destination := source - 1
  let U := writeLogical spec.growth
    (writeLogical spec.growth T source blankSymbol) destination
      (boundarySymbol label)
  have hposition : origin + distance = destination + 1 := by
    simp only [destination]
    omega
  have hsourceEq : destination + 1 = source := by
    simp only [destination]
    omega
  have hrun := machine_reaches_decrementShift_or_halts base c limit hshort
    spec.growth counterState searchSlot origin destination distance label
    success collision hraw T hposition hdistance hgap
    (by simpa [source, destination] using hblank)
  rcases hrun with hrun | hhalts
  · left
    have hrep : Represents (updateSpec spec next hnextCore) U := by
      apply moveLeft_represents h next label hnextCore hlower hupper
        hsourcePositive hsource hdestination hshrink hmove
    have hU : U = install next spec.growth spec.returnTag
        (writeLogical spec.growth T source blankSymbol) := by
      apply moveLeft_eq_install_cleared next label hnextCore
      · omega
      · exact hdestination
      · exact hrep
    rw [hsourceEq] at hrun
    change FullTM0.Reaches _ _
      ⟨resolve base c success, atLogical spec.growth U source⟩ at hrun
    rw [hU] at hrun
    exact hrun
  · exact Or.inr hhalts

/-- The outward clock shift resolves to the exact incremented tape, or halts
at its search entry. -/
theorem machine_reaches_incrementClock_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment .clock) <
      spec.outerDistance)
    (hlimit : 0 < limit)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ 4 .left .right
      success (some .left) collision ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c success,
          atLogical spec.growth (incrementTape spec .clock T)
            (layoutEnd spec.registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  let next := spec.registers.increment .clock
  let U := writeLogical spec.growth
    (writeLogical spec.growth T (layoutEnd spec.registers) blankSymbol)
    (layoutEnd spec.registers + 1) (boundarySymbol 4)
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary 4).Matches
      (atLogical spec.growth T (layoutEnd spec.registers))
      (OrientedMarkerTape.orientDirection spec.growth .left) 0 := by
    rw [SearchGap.zero]
    change (atLogical spec.growth T (layoutEnd spec.registers)).read =
      boundarySymbol 4
    exact h.read_boundary_four
  have hblank : logicalTape spec.growth T
      (layoutEnd spec.registers + 1) = blankSymbol := by
    simpa [next, layoutEnd_increment] using
      increment_destination_blank h .clock hroom
  have hrun := machine_reaches_incrementShift_or_halts base c limit hshort
    spec.growth counterState searchSlot (layoutEnd spec.registers) 4
    success collision hraw T 0 hlimit hgap hblank
  rcases hrun with hrun | hhalts
  · left
    have hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers 4) 4 =
        MarkerTape.canonicalTape next := by
      rw [MarkerMachine.moveAt_clock_eq_incrementTape]
      exact MarkerShift.incrementTape_canonical spec.registers .clock
    have hrep : Represents (updateSpec spec next hroom) U := by
      apply moveRight_represents h next 4 hroom
      · dsimp only [next]
        rw [layoutEnd_increment]
        omega
      · dsimp only [next]
        rw [layoutEnd_increment]
      · exact boundaryOffset_four spec.registers |>.le
      · simp only [boundaryOffset_four]
        dsimp only [next]
        rw [layoutEnd_increment]
      · intro _
        simp only [boundaryOffset_four]
        dsimp only [next]
        rw [layoutEnd_increment]
      · exact hmove
    have hU : U = incrementTape spec .clock T := by
      change U = install next spec.growth spec.returnTag T
      apply moveRight_eq_install next 4 hroom
      · simp [boundaryOffset]
      · simp only [boundaryOffset_four]
        dsimp only [next]
        rw [layoutEnd_increment]
        omega
      · simp only [boundaryOffset_four]
        dsimp only [next]
        rw [layoutEnd_increment]
      · exact hrep
    simpa [U, hU] using hrun
  · exact Or.inr hhalts

/-! ## Collision-free increment schedule -/

/-- All collision-free shifts of one generated increment resolve to the
blank old source cell of the final shifted boundary, or a constituent search
halts the complete controller. -/
theorem machine_reaches_incrementSchedule_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : ShortResolves base c spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source bodyDirectBase),
          atLogical spec.growth (incrementTape spec register T)
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have hlimit : 0 < spec.outerDistance := by
    have := hroom
    omega
  have hclockRoom : layoutEnd (spec.registers.increment .clock) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  have htempRoom : layoutEnd (spec.registers.increment .temp) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  have hrightRoom : layoutEnd (spec.registers.increment .right) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  have hleftRoom : layoutEnd (spec.registers.increment .left) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  cases register with
  | clock =>
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (directRef spec.growth source bodyDirectBase) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      simpa [MarkerSchedule.decrementStartBoundary] using
        machine_reaches_incrementClock_or_halts base c spec.outerDistance
          hshort source bodySearchBase
          (directRef spec.growth source bodyDirectBase)
          (some (directRef spec.growth source testDirectSlot)) h hclockRoom
          hlimit hraw
  | temp =>
      let clockTape := incrementTape spec .clock T
      let clockSpec := incrementSpec spec .clock hclockRoom
      have hclockRep : Represents clockSpec clockTape :=
        incrementTape_represents h .clock hclockRoom
      have hrawFour : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hfour := machine_reaches_incrementClock_or_halts base c
        spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hrawThree : RawCommand.markerShift
          ⟨clockSpec.growth, source, bodySearchBase + 1⟩ 3 .left .right
          (directRef clockSpec.growth source bodyDirectBase) (some .left)
          none ∈ rawCommands := by
        simpa [clockSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 1⟩ 3 .left .right
            (directRef spec.growth source bodyDirectBase) (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hthree := machine_reaches_incrementInternal_or_halts base c
        spec.outerDistance hshort source (bodySearchBase + 1)
        (directRef clockSpec.growth source bodyDirectBase) none hclockRep
        (spec.registers.increment .temp) (3 : Fin 4)
        (by simp [clockSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        (by simpa [clockSpec, incrementSpec, updateSpec] using htempRoom)
        (by simp [clockSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveTempBoundary_after_clock spec.registers)
        hrawThree
      have hhead : layoutEnd spec.registers =
          lastGapOffset (spec.registers.increment .clock) 3 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          layoutEnd, RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have htape : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = incrementTape spec .temp T := by
        change install (spec.registers.increment .temp) spec.growth
            spec.returnTag
            (install (spec.registers.increment .clock) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .temp) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htape] at hthree
      have hfinish : boundaryOffset (spec.registers.increment .clock)
          ((3 : Fin 4).castSucc) = boundaryOffset spec.registers 3 := by
        simp [boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      rw [← hhead, hfinish] at hthree
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree
      exact reaches_or_halts_trans hfour hthree
  | right =>
      let clockTape := incrementTape spec .clock T
      let clockSpec := incrementSpec spec .clock hclockRoom
      let tempTape := incrementTape spec .temp T
      let tempSpec := incrementSpec spec .temp htempRoom
      have hclockRep : Represents clockSpec clockTape :=
        incrementTape_represents h .clock hclockRoom
      have htempRep : Represents tempSpec tempTape :=
        incrementTape_represents h .temp htempRoom
      have hrawFour : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawThree : RawCommand.markerShift
          ⟨clockSpec.growth, source, bodySearchBase + 1⟩ 3 .left .right
          (searchRef clockSpec.growth source (bodySearchBase + 2))
          (some .left) none ∈ rawCommands := by
        simpa [clockSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 1⟩ 3 .left .right
            (searchRef spec.growth source (bodySearchBase + 2))
            (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hrawTwo : RawCommand.markerShift
          ⟨tempSpec.growth, source, bodySearchBase + 2⟩ 2 .left .right
          (directRef tempSpec.growth source bodyDirectBase) (some .left)
          none ∈ rawCommands := by
        simpa [tempSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 2⟩ 2 .left .right
            (directRef spec.growth source bodyDirectBase) (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hfour := machine_reaches_incrementClock_or_halts base c
        spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hthree := machine_reaches_incrementInternal_or_halts base c
        spec.outerDistance hshort source (bodySearchBase + 1)
        (searchRef clockSpec.growth source (bodySearchBase + 2)) none
        hclockRep (spec.registers.increment .temp) (3 : Fin 4)
        (by simp [clockSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        (by simpa [clockSpec, incrementSpec, updateSpec] using htempRoom)
        (by simp [clockSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveTempBoundary_after_clock spec.registers)
        hrawThree
      have htwo := machine_reaches_incrementInternal_or_halts base c
        spec.outerDistance hshort source (bodySearchBase + 2)
        (directRef tempSpec.growth source bodyDirectBase) none htempRep
        (spec.registers.increment .right) (2 : Fin 4)
        (by simp [tempSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance htempRep (2 : Fin 4))
        (by simpa [tempSpec, incrementSpec, updateSpec] using hrightRoom)
        (by simp [tempSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveRightBoundary_after_temp spec.registers)
        hrawTwo
      have hheadFour : layoutEnd spec.registers =
          lastGapOffset (spec.registers.increment .clock) 3 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          layoutEnd, RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have hheadThree : boundaryOffset (spec.registers.increment .clock) 3 =
          lastGapOffset (spec.registers.increment .temp) 2 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have htapeThree : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = tempTape := by
        change install (spec.registers.increment .temp) spec.growth
            spec.returnTag
            (install (spec.registers.increment .clock) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .temp) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htapeThree] at hthree
      have htapeTwo : install (spec.registers.increment .right) spec.growth
          spec.returnTag tempTape = incrementTape spec .right T := by
        change install (spec.registers.increment .right) spec.growth
            spec.returnTag
            (install (spec.registers.increment .temp) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .right) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [tempSpec, incrementSpec, updateSpec] at htwo
      rw [htapeTwo] at htwo
      have hhandoffThree :
          boundaryOffset (spec.registers.increment .clock)
              ((3 : Fin 4).castSucc) =
            lastGapOffset (spec.registers.increment .temp) 2 := by
        simpa using hheadThree
      have hfinish : boundaryOffset (spec.registers.increment .temp)
          ((2 : Fin 4).castSucc) = boundaryOffset spec.registers 2 := by
        simp [boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      rw [← hheadFour, hhandoffThree] at hthree
      rw [hfinish] at htwo
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree
      exact reaches_or_halts_trans hfour
        (reaches_or_halts_trans hthree htwo)
  | left =>
      let clockTape := incrementTape spec .clock T
      let clockSpec := incrementSpec spec .clock hclockRoom
      let tempTape := incrementTape spec .temp T
      let tempSpec := incrementSpec spec .temp htempRoom
      let rightTape := incrementTape spec .right T
      let rightSpec := incrementSpec spec .right hrightRoom
      have hclockRep : Represents clockSpec clockTape :=
        incrementTape_represents h .clock hclockRoom
      have htempRep : Represents tempSpec tempTape :=
        incrementTape_represents h .temp htempRoom
      have hrightRep : Represents rightSpec rightTape :=
        incrementTape_represents h .right hrightRoom
      have hrawFour : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawThree : RawCommand.markerShift
          ⟨clockSpec.growth, source, bodySearchBase + 1⟩ 3 .left .right
          (searchRef clockSpec.growth source (bodySearchBase + 2))
          (some .left) none ∈ rawCommands := by
        simpa [clockSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 1⟩ 3 .left .right
            (searchRef spec.growth source (bodySearchBase + 2))
            (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hrawTwo : RawCommand.markerShift
          ⟨tempSpec.growth, source, bodySearchBase + 2⟩ 2 .left .right
          (searchRef tempSpec.growth source (bodySearchBase + 3))
          (some .left) none ∈ rawCommands := by
        simpa [tempSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 2⟩ 2 .left .right
            (searchRef spec.growth source (bodySearchBase + 3))
            (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hrawOne : RawCommand.markerShift
          ⟨rightSpec.growth, source, bodySearchBase + 3⟩ 1 .left .right
          (directRef rightSpec.growth source bodyDirectBase) (some .left)
          none ∈ rawCommands := by
        simpa [rightSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 3⟩ 1 .left .right
            (directRef spec.growth source bodyDirectBase) (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hfour := machine_reaches_incrementClock_or_halts base c
        spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hthree := machine_reaches_incrementInternal_or_halts base c
        spec.outerDistance hshort source (bodySearchBase + 1)
        (searchRef clockSpec.growth source (bodySearchBase + 2)) none
        hclockRep (spec.registers.increment .temp) (3 : Fin 4)
        (by simp [clockSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        (by simpa [clockSpec, incrementSpec, updateSpec] using htempRoom)
        (by simp [clockSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveTempBoundary_after_clock spec.registers)
        hrawThree
      have htwo := machine_reaches_incrementInternal_or_halts base c
        spec.outerDistance hshort source (bodySearchBase + 2)
        (searchRef tempSpec.growth source (bodySearchBase + 3)) none
        htempRep (spec.registers.increment .right) (2 : Fin 4)
        (by simp [tempSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance htempRep (2 : Fin 4))
        (by simpa [tempSpec, incrementSpec, updateSpec] using hrightRoom)
        (by simp [tempSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveRightBoundary_after_temp spec.registers)
        hrawTwo
      have hone := machine_reaches_incrementInternal_or_halts base c
        spec.outerDistance hshort source (bodySearchBase + 3)
        (directRef rightSpec.growth source bodyDirectBase) none hrightRep
        (spec.registers.increment .left) (1 : Fin 4)
        (by simp [rightSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [rightSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hrightRep (1 : Fin 4))
        (by simpa [rightSpec, incrementSpec, updateSpec] using hleftRoom)
        (by simp [rightSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [rightSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveLeftBoundary_after_right spec.registers)
        hrawOne
      have hheadFour : layoutEnd spec.registers =
          lastGapOffset (spec.registers.increment .clock) 3 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          layoutEnd, RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have hheadThree : boundaryOffset (spec.registers.increment .clock) 3 =
          lastGapOffset (spec.registers.increment .temp) 2 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have hheadTwo : boundaryOffset (spec.registers.increment .temp) 2 =
          lastGapOffset (spec.registers.increment .right) 1 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have htapeThree : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = tempTape := by
        change install (spec.registers.increment .temp) spec.growth
            spec.returnTag
            (install (spec.registers.increment .clock) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .temp) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htapeThree] at hthree
      have htapeTwo : install (spec.registers.increment .right) spec.growth
          spec.returnTag tempTape = rightTape := by
        change install (spec.registers.increment .right) spec.growth
            spec.returnTag
            (install (spec.registers.increment .temp) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .right) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [tempSpec, incrementSpec, updateSpec] at htwo
      rw [htapeTwo] at htwo
      have htapeOne : install (spec.registers.increment .left) spec.growth
          spec.returnTag rightTape = incrementTape spec .left T := by
        change install (spec.registers.increment .left) spec.growth
            spec.returnTag
            (install (spec.registers.increment .right) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .left) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [rightSpec, incrementSpec, updateSpec] at hone
      rw [htapeOne] at hone
      have hhandoffThree :
          boundaryOffset (spec.registers.increment .clock)
              ((3 : Fin 4).castSucc) =
            lastGapOffset (spec.registers.increment .temp) 2 := by
        simpa using hheadThree
      have hhandoffTwo :
          boundaryOffset (spec.registers.increment .temp)
              ((2 : Fin 4).castSucc) =
            lastGapOffset (spec.registers.increment .right) 1 := by
        simpa using hheadTwo
      have hfinish : boundaryOffset (spec.registers.increment .right)
          ((1 : Fin 4).castSucc) = boundaryOffset spec.registers 1 := by
        simp [boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      rw [← hheadFour, hhandoffThree] at hthree
      rw [hhandoffTwo] at htwo
      rw [hfinish] at hone
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree htwo
      exact reaches_or_halts_trans hfour
        (reaches_or_halts_trans hthree
          (reaches_or_halts_trans htwo hone))

/-! ## Increment handoff and recovery -/

/-- The post-increment recovery route reaches boundary `4`, or one of its
shorter searches halts the complete controller. -/
theorem machine_reaches_incrementRecovery_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (match AnchoredCounterGeometry.routeFromIncrement register with
            | [] => .logical spec.growth next
            | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩
        ⟨logicalState base c spec.growth next,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (match AnchoredCounterGeometry.routeFromIncrement register with
            | [] => .logical spec.growth next
            | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩ := by
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux spec.growth source secondarySearchBase
          (bodyDirectBase + 2) (.logical spec.growth next)
          (AnchoredCounterGeometry.routeFromIncrement register) →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules spec.growth source
            (directRef spec.growth source (bodyDirectBase + 1))
            (MarkerSchedule.decrementStartBoundary register)
            secondarySearchBase
            (AnchoredCounterGeometry.routeFromIncrement register) ++
          routeContinuationRules spec.growth source secondarySearchBase
            (bodyDirectBase + 2)
            (AnchoredCounterGeometry.routeFromIncrement register) →
        raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      incrementRules spec.growth source next register
    apply List.mem_append_right
    rcases List.mem_append.mp hraw with hentry | hcontinuation
    · simp only [incrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hentry))
    · simp only [incrementRules, List.mem_append]
      exact Or.inl (Or.inr hcontinuation)
  cases register with
  | clock => exact Or.inl Relation.ReflTransGen.refl
  | temp =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
        spec.outerDistance hshort
        spec.growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef spec.growth source (bodyDirectBase + 1))
        (.logical spec.growth next) 3
        (AnchoredCounterGeometry.routeFromIncrement .temp)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset spec.registers 3) (layoutEnd spec.registers)
        (by rw [atLogical_read]; exact h.boundary 3)
        (routeFromIncrement_executesWithin h .temp)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun
  | right =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
        spec.outerDistance hshort
        spec.growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef spec.growth source (bodyDirectBase + 1))
        (.logical spec.growth next) 2
        (AnchoredCounterGeometry.routeFromIncrement .right)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset spec.registers 2) (layoutEnd spec.registers)
        (by rw [atLogical_read]; exact h.boundary 2)
        (routeFromIncrement_executesWithin h .right)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun
  | left =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
        spec.outerDistance hshort
        spec.growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef spec.growth source (bodyDirectBase + 1))
        (.logical spec.growth next) 1
        (AnchoredCounterGeometry.routeFromIncrement .left)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset spec.registers 1) (layoutEnd spec.registers)
        (by rw [atLogical_read]; exact h.boundary 1)
        (routeFromIncrement_executesWithin h .left)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun

/-- Exact collision-free increment semantics on a backed frame: either the
logical successor frame is reached and remains backed by the same outer tape,
or the complete controller halts from the instruction's logical entry. -/
theorem machine_reaches_incrementInstruction_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : ShortResolves base c spec.outerDistance) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth next,
          atLogical spec.growth (incrementTape spec register T)
            (layoutEnd (spec.registers.increment register))⟩ ∧
      BackedBy (incrementSpec spec register hroom)
        (incrementTape spec register T) outer) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_or_halts base c spec.growth
    source (.increment register next) hrule h rfl hshort
  have hcommands : ∀ raw,
      raw ∈ incrementShiftCommands spec.growth source register →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hschedule := machine_reaches_incrementSchedule_or_halts base c source
    register h hroom hshort hcommands
  have hhandoff := machine_reaches_incrementHandoff base c source next
    register hrule h hroom
  let nextSpec := incrementSpec spec register hroom
  have hnext : Represents nextSpec (incrementTape spec register T) :=
    incrementTape_represents h register hroom
  have hrecovery := machine_reaches_incrementRecovery_or_halts base c
    source next register hrule hnext (by
      simpa [nextSpec, incrementSpec, updateSpec] using hshort)
  have hvalidation' :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve] using hvalidation
  have hrecovery' :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (match AnchoredCounterGeometry.routeFromIncrement register with
              | [] => .logical spec.growth next
              | _ :: _ => directRef spec.growth source
                  (bodyDirectBase + 1)),
            atLogical spec.growth (incrementTape spec register T)
              (boundaryOffset (spec.registers.increment register)
                (MarkerSchedule.decrementStartBoundary register))⟩
          ⟨logicalState base c spec.growth next,
            atLogical spec.growth (incrementTape spec register T)
              (layoutEnd (spec.registers.increment register))⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (match AnchoredCounterGeometry.routeFromIncrement register with
              | [] => .logical spec.growth next
              | _ :: _ => directRef spec.growth source
                  (bodyDirectBase + 1)),
            atLogical spec.growth (incrementTape spec register T)
              (boundaryOffset (spec.registers.increment register)
                (MarkerSchedule.decrementStartBoundary register))⟩ := by
    simpa [nextSpec, incrementSpec, updateSpec] using hrecovery
  have hrun := reaches_or_halts_trans hvalidation'
    (reaches_or_halts_trans hschedule
      (reaches_or_halts_trans (Or.inl hhandoff) hrecovery'))
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨hrun, incrementTape_backedBy hback register hroom⟩
  · exact Or.inr hhalts

/-- If the outward increment destination is the suspended target cell, the
instruction reaches the generated collision-cleanup entry, unless validation
has already halted the complete controller. -/
theorem machine_reaches_incrementCollisionInstruction_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterFour spec T)
            spec.outerDistance⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have hvalidation := machine_reaches_validation_or_halts base c spec.growth
    source (.increment register next) hrule h rfl hshort
  let success : ControlRef := match register with
    | .clock => directRef spec.growth source bodyDirectBase
    | _ => searchRef spec.growth source (bodySearchBase + 1)
  have hraw : RawCommand.markerShift
      ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
      success (some .left)
      (some (directRef spec.growth source testDirectSlot)) ∈ rawCommands := by
    apply command_mem_rawCommands_of_rule spec.growth hrule
    cases register <;>
      simp [success, commandsForRule, incrementCommands, incrementShiftCommands,
        incrementShiftCommandsAux, MarkerShift.incrementOrder]
  have hcollisionReach := machine_reaches_incrementCollision base c source
    success h hcollision hraw
  have hvalidation' :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve] using hvalidation
  exact reaches_or_halts_trans hvalidation' (Or.inl hcollisionReach)

/-- Complete collision branch of an increment instruction.  Successful
cleanup restores the suspended outer tape at its exact resume state; any
failed validation or cleanup search is propagated back to the logical
instruction entry. -/
theorem machine_reaches_incrementCollisionCleanup_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address), outer⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have hcollisionEntry :=
    machine_reaches_incrementCollisionInstruction_or_halts base c source next
      register hrule hback.represents hcollision hshort
  have hentry : CounterControlCleanupSemantics.cleanupEntryRule
      spec.growth source ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change CounterControlCleanupSemantics.cleanupEntryRule spec.growth source ∈
      validationRules spec.growth source ++
        incrementRules spec.growth source next register
    apply List.mem_append_right
    simp [CounterControlCleanupSemantics.cleanupEntryRule, incrementRules]
  have hcleanupCommands : ∀ raw,
      raw ∈ cleanupCommands spec.growth source → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hcleanup := machine_reaches_collisionCleanup_or_halts base c source
    hback hreturnDirection hcollision hshort hentry hcleanupCommands
  exact reaches_or_halts_trans hcollisionEntry hcleanup

/-! ## Conditional-decrement routing and zero branch -/

/-- Navigate from boundary `4` to the selected register test, or halt in a
shorter route search.  Clock requires no navigation. -/
theorem machine_reaches_decrementToTest_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry spec.growth source
              (.decrement register ifZero ifPositive)),
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry spec.growth source
              (.decrement register ifZero ifPositive)),
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  let route := AnchoredCounterGeometry.routeToDecrementStart register
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux spec.growth source bodySearchBase
          (bodyDirectBase + 1) (directRef spec.growth source testDirectSlot)
          route → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, decrementCommands, route, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules spec.growth source
            (directRef spec.growth source bodyDirectBase) 4 bodySearchBase
            route ++
          routeContinuationRules spec.growth source bodySearchBase
            (bodyDirectBase + 1) route →
        raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    have hraw' : raw ∈
        routeEntryRules spec.growth source
            (directRef spec.growth source bodyDirectBase) 4 bodySearchBase
            (AnchoredCounterGeometry.routeToDecrementStart register) ++
          routeContinuationRules spec.growth source bodySearchBase
            (bodyDirectBase + 1)
            (AnchoredCounterGeometry.routeToDecrementStart register) := by
      simpa [route] using hraw
    rcases List.mem_append.mp hraw' with hentry | hcontinuation
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hentry))
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hcontinuation))
  cases register with
  | clock => exact Or.inl Relation.ReflTransGen.refl
  | temp =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .temp)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 3)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .temp)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .temp ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨resolve base c (directRef spec.growth source testDirectSlot),
            atLogical spec.growth T (boundaryOffset spec.registers 3)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .temp ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩) at hrun
      exact hrun
  | right =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .right)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 2)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .right)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .right ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨resolve base c (directRef spec.growth source testDirectSlot),
            atLogical spec.growth T (boundaryOffset spec.registers 2)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .right ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩) at hrun
      exact hrun
  | left =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .left)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 1)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .left)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .left ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨resolve base c (directRef spec.growth source testDirectSlot),
            atLogical spec.growth T (boundaryOffset spec.registers 1)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .left ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩) at hrun
      exact hrun

/-- From the predecessor boundary of an empty tested gap, the generated zero
route reaches the zero successor, or a route search halts. -/
theorem machine_reaches_decrementZeroRecovery_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hzero : spec.registers.get register = 0)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source branchDirectSlot),
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register) - 1)⟩
        ⟨logicalState base c spec.growth ifZero,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source branchDirectSlot),
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register) - 1)⟩ := by
  let route := AnchoredCounterGeometry.routeFromZero register
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux spec.growth source zeroSearchBase zeroDirectBase
          (.logical spec.growth ifZero) route → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, decrementCommands, route, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules spec.growth source
            (directRef spec.growth source branchDirectSlot)
            (AnchoredCounterGeometry.registerGap register).castSucc
            zeroSearchBase route ++
          routeContinuationRules spec.growth source zeroSearchBase
            zeroDirectBase route → raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    rcases List.mem_append.mp hraw with hentry | hcontinuation
    · have hentryOriginal : raw ∈ routeEntryRules spec.growth source
          (directRef spec.growth source branchDirectSlot)
          (AnchoredCounterGeometry.registerGap register).castSucc
          zeroSearchBase
          (AnchoredCounterGeometry.routeFromZero register) := by
        simpa [route] using hentry
      have hentryRules : routeEntryRules spec.growth source
          (directRef spec.growth source branchDirectSlot)
          (AnchoredCounterGeometry.registerGap register).castSucc
          zeroSearchBase
          (AnchoredCounterGeometry.routeFromZero register) =
          [⟨spec.growth, directRef spec.growth source branchDirectSlot,
            .boundary
              (AnchoredCounterGeometry.registerGap register).castSucc,
            searchRef spec.growth source zeroSearchBase, .right⟩] := by
        cases register <;> rfl
      rw [hentryRules] at hentryOriginal
      have heq : raw =
          ⟨spec.growth, directRef spec.growth source branchDirectSlot,
            .boundary
              (AnchoredCounterGeometry.registerGap register).castSucc,
            searchRef spec.growth source zeroSearchBase, .right⟩ := by
        simpa using hentryOriginal
      have hfour : raw ∈
          [⟨spec.growth, directRef spec.growth source testDirectSlot,
              .boundary (MarkerSchedule.decrementStartBoundary register),
              directRef spec.growth source branchDirectSlot, .left⟩,
            ⟨spec.growth, directRef spec.growth source branchDirectSlot,
              .blank, searchRef spec.growth source secondarySearchBase,
              .right⟩,
            ⟨spec.growth, directRef spec.growth source branchDirectSlot,
              .boundary
                (AnchoredCounterGeometry.registerGap register).castSucc,
              searchRef spec.growth source zeroSearchBase, .right⟩,
            ⟨spec.growth, directRef spec.growth source finishDirectSlot,
              .blank, .logical spec.growth ifPositive, .left⟩] := by
        simp only [List.mem_cons]
        exact Or.inr (Or.inr (Or.inl heq))
      simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inr hfour)
    · simp only [decrementRules, List.mem_append]
      exact Or.inr (by simpa [route] using hcontinuation)
  have hsourcePosition : boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1 =
      boundaryOffset spec.registers
        (AnchoredCounterGeometry.registerGap register).castSucc := by
    cases register with
    | left =>
        have hz : spec.registers.left = 0 := by
          simpa [Registers.get] using hzero
        simp [MarkerSchedule.decrementStartBoundary,
          AnchoredCounterGeometry.registerGap, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values, hz]
    | right =>
        have hz : spec.registers.right = 0 := by
          simpa [Registers.get] using hzero
        simp [MarkerSchedule.decrementStartBoundary,
          AnchoredCounterGeometry.registerGap, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values, hz]
    | temp =>
        have hz : spec.registers.temp = 0 := by
          simpa [Registers.get] using hzero
        simp [MarkerSchedule.decrementStartBoundary,
          AnchoredCounterGeometry.registerGap, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values, hz]
    | clock =>
        have hz : spec.registers.clock = 0 := by
          simpa [Registers.get] using hzero
        simp [MarkerSchedule.decrementStartBoundary,
          AnchoredCounterGeometry.registerGap, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values, hz]
  have hrun := route_reaches_or_halts_at_of_ne_nil base c
    spec.outerDistance hshort spec.growth source zeroSearchBase zeroDirectBase
    (directRef spec.growth source branchDirectSlot)
    (.logical spec.growth ifZero)
    (AnchoredCounterGeometry.registerGap register).castSucc route
    (by cases register <;> simp [route,
      AnchoredCounterGeometry.routeFromZero]) T
    (boundaryOffset spec.registers
      (AnchoredCounterGeometry.registerGap register).castSucc)
    (layoutEnd spec.registers)
    (by rw [atLogical_read]; exact h.boundary _)
    (routeFromZero_executesWithin h register)
    (by intro raw hraw; exact hcommands raw hraw)
    (by intro raw hraw; exact hrules raw hraw)
  rw [hsourcePosition]
  simpa [route, logicalState, CounterControlPlan.resolve] using hrun

/-- Exact zero branch of one compiled conditional decrement, with the
unchanged backed-frame invariant returned in the successful branch. -/
theorem machine_reaches_decrementZeroInstruction_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hzero : spec.registers.get register = 0)
    (hshort : ShortResolves base c spec.outerDistance) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth ifZero,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ ∧
      BackedBy spec T outer) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_or_halts base c spec.growth
    source (.decrement register ifZero ifPositive) hrule h rfl hshort
  have hroute := machine_reaches_decrementToTest_or_halts base c source
    ifZero ifPositive register hrule h hshort
  have htest := machine_reaches_decrementTest base c source ifZero ifPositive
    register hrule T (by rw [atLogical_read]; exact h.boundary _)
  have hzeroRoute := machine_reaches_decrementZeroRecovery_or_halts base c
    source ifZero ifPositive register hrule h hzero hshort
  have hrun := reaches_or_halts_trans hvalidation
    (reaches_or_halts_trans hroute
      (reaches_or_halts_trans (Or.inl htest) hzeroRoute))
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨hrun, hback⟩
  · exact Or.inr hhalts

/-! ## Positive conditional-decrement shifts -/

/-- The first positive-decrement shift has search distance zero and either
installs its exact next canonical core or halts. -/
theorem machine_reaches_decrementFirst_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (counterState searchSlot : Nat)
    (success : ControlRef) (hlimit : 0 < limit)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers i.succ ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers i.succ - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (boundaryOffset spec.registers i.succ)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers i.succ) blankSymbol))
            (boundaryOffset spec.registers i.succ)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (boundaryOffset spec.registers i.succ)⟩ := by
  have hsourcePositive : 1 < boundaryOffset spec.registers i.succ := by
    simp [boundaryOffset]
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches
      (atLogical spec.growth T (boundaryOffset spec.registers i.succ))
      (OrientedMarkerTape.orientDirection spec.growth .right) 0 := by
    rw [SearchGap.zero]
    change (atLogical spec.growth T
      (boundaryOffset spec.registers i.succ)).read = boundarySymbol i.succ
    rw [atLogical_read]
    exact h.boundary i.succ
  have hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers i.succ - 1 : Nat) : Int) =
        blankSymbol := by
    have hb := h.gap_blank i (RegisterLayout.values spec.registers i - 1)
      (by omega)
    have hcoord : (firstGapOffset spec.registers i : Int) +
        (RegisterLayout.values spec.registers i - 1 : Nat) =
        (boundaryOffset spec.registers i.succ - 1 : Nat) := by
      simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
      omega
    rw [hcoord] at hb
    exact hb
  apply machine_reaches_decrementCanonical_or_halts base c limit hshort
    counterState searchSlot success none h next i.succ
    (boundaryOffset spec.registers i.succ) 0 hsourcePositive
    (by simp) hlimit hgap hblank hnextCore hlower hupper hsource hdestination
      hshrink hmove hraw

/-- Every later positive-decrement shift searches one represented gap before
installing its exact next canonical core, or halts. -/
theorem machine_reaches_decrementFollowing_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (counterState searchSlot : Nat)
    (success : ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hdistance : RegisterLayout.values spec.registers i < limit)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers i.succ ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers i.succ - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (firstGapOffset spec.registers i)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers i.succ) blankSymbol))
            (boundaryOffset spec.registers i.succ)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (firstGapOffset spec.registers i)⟩ := by
  have hsourcePositive : 1 < boundaryOffset spec.registers i.succ := by
    simp [boundaryOffset]
  have horigin : firstGapOffset spec.registers i +
      RegisterLayout.values spec.registers i =
      boundaryOffset spec.registers i.succ := by
    simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
    omega
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches
      (atLogical spec.growth T (firstGapOffset spec.registers i))
      (OrientedMarkerTape.orientDirection spec.growth .right)
      (RegisterLayout.values spec.registers i) := by
    change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ) _ _ _
    exact h.searchGap_adjacent_right i
  have hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers i.succ - 1 : Nat) : Int) =
        blankSymbol := by
    have hb := h.gap_blank i (RegisterLayout.values spec.registers i - 1)
      (by omega)
    have hcoord : (firstGapOffset spec.registers i : Int) +
        (RegisterLayout.values spec.registers i - 1 : Nat) =
        (boundaryOffset spec.registers i.succ - 1 : Nat) := by
      simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
      omega
    rw [hcoord] at hb
    exact hb
  exact machine_reaches_decrementCanonical_or_halts base c limit hshort
    counterState searchSlot success none h next i.succ
    (firstGapOffset spec.registers i)
    (RegisterLayout.values spec.registers i) hsourcePositive horigin
    hdistance hgap hblank hnextCore hlower hupper hsource hdestination
    hshrink hmove hraw

/-! ## Positive conditional-decrement schedule -/

/-- Every shift in a positive-decrement suffix resolves.  A successful
suffix returns the exact decremented tape together with its unchanged outer
backing; a failed constituent search halts the complete controller from the
schedule entry. -/
theorem machine_reaches_decrementSchedule_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hpositive : 0 < spec.registers.get register)
    (hshort : ShortResolves base c spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩
        ⟨resolve base c (directRef spec.growth source finishDirectSlot),
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd spec.registers)⟩ ∧
      BackedBy (decrementSpec spec register hpositive)
        (decrementTape spec register T) outer) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩ := by
  have h := hback.represents
  have hlimit : 0 < spec.outerDistance := by
    exact Nat.zero_lt_of_lt spec.core_before_target
  have hdesired := decrementTape_backedBy hback register hpositive
  cases register with
  | clock =>
      have hp : 0 < spec.registers.clock := by
        simpa [Registers.get] using hpositive
      let next := spec.registers.decrement .clock
      have hnextCore : layoutEnd next < spec.outerDistance :=
        (layoutEnd_decrement_lt spec.registers .clock hpositive).trans
          spec.core_before_target
      have hend : layoutEnd next + 1 = layoutEnd spec.registers :=
        layoutEnd_decrement_add_one spec.registers .clock hpositive
      have hmove : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers 4) 4 =
        MarkerTape.canonicalTape next := by
        have hm := MarkerSchedule.moveClockBoundary_after_increment next
        have hinv := MarkerSchedule.increment_decrement_registers
          spec.registers .clock hpositive
        rw [hinv] at hm
        exact hm
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 4 .right .left
          (directRef spec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have hrun := machine_reaches_decrementFirst_or_halts base c
        spec.outerDistance hshort source secondarySearchBase
        (directRef spec.growth source finishDirectSlot) hlimit h next
        (3 : Fin 4) (by simpa [RegisterLayout.values] using hp)
        hnextCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 4)
        (by
          change layoutEnd spec.registers - 1 ≤ layoutEnd next
          omega)
        (by intro _; rfl) hmove hraw
      apply reaches_and_or_halts ?_ hdesired
      simpa [next, decrementTape, clearOldLayoutEnd,
        MarkerSchedule.decrementStartBoundary,
        boundaryOffset_four] using hrun
  | temp =>
      have hp : 0 < spec.registers.temp := by
        simpa [Registers.get] using hpositive
      let final := spec.registers.decrement .temp
      have hinv : final.increment .temp = spec.registers := by
        exact MarkerSchedule.increment_decrement_registers
          spec.registers .temp hpositive
      let clockRegs := final.increment .clock
      have hclockEnd : layoutEnd clockRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [clockRegs, layoutEnd_increment]
      have hclockCore : layoutEnd clockRegs < spec.outerDistance := by
        rw [hclockEnd]
        exact spec.core_before_target
      have hmoveThree : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers 3) 3 =
        MarkerTape.canonicalTape clockRegs := by
        have hm := MarkerSchedule.moveTempBoundary_before_clock final
        rw [hinv] at hm
        exact hm
      have hrawThree : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 3 .right .left
          (searchRef spec.growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have hthree := machine_reaches_decrementFirst_or_halts base c
        spec.outerDistance hshort source secondarySearchBase
        (searchRef spec.growth source (secondarySearchBase + 1)) hlimit h
        clockRegs (2 : Fin 4) (by simpa [RegisterLayout.values] using hp)
        hclockCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 3)
        (by
          change boundaryOffset spec.registers 3 - 1 ≤ layoutEnd clockRegs
          rw [hclockEnd]
          have hbound := boundaryOffset_le_layoutEnd spec.registers (3 : Fin 5)
          omega)
        (by
          intro hlt
          rw [hclockEnd] at hlt
          omega)
        hmoveThree hrawThree
      let Uclock := install clockRegs spec.growth spec.returnTag
        (writeLogical spec.growth T (boundaryOffset spec.registers 3)
          blankSymbol)
      let clockSpec := updateSpec spec clockRegs hclockCore
      have hclockBack : BackedBy clockSpec Uclock outer := by
        exact install_clear_inside_backedBy hback clockRegs hclockCore
          (boundaryOffset spec.registers 3) (by simp [boundaryOffset])
          (by rw [hclockEnd]; exact boundaryOffset_le_layoutEnd _ 3)
          (by omega)
      have hclockRep := hclockBack.represents
      have hfinalCore : layoutEnd final < clockSpec.outerDistance := by
        have hlt := layoutEnd_decrement_lt spec.registers .temp hpositive
        simpa [clockSpec, updateSpec, final] using
          hlt.trans spec.core_before_target
      have hfinalEnd : layoutEnd final + 1 = layoutEnd clockRegs := by
        rw [hclockEnd]
        exact layoutEnd_decrement_add_one spec.registers .temp hpositive
      have hmoveFour : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape clockSpec.registers)
          (MarkerTape.boundaryPosition clockSpec.registers 4) 4 =
        MarkerTape.canonicalTape final := by
        simpa [clockSpec, updateSpec, clockRegs] using
          MarkerSchedule.moveClockBoundary_after_increment final
      have hrawFour : RawCommand.markerShift
          ⟨clockSpec.growth, source, secondarySearchBase + 1⟩ 4 .right .left
          (directRef clockSpec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        simpa [clockSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 1⟩ 4 .right .left
            (directRef spec.growth source finishDirectSlot) (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hfour := machine_reaches_decrementFollowing_or_halts base c
        spec.outerDistance (by simpa [clockSpec, updateSpec] using hshort)
        source (secondarySearchBase + 1)
        (directRef clockSpec.growth source finishDirectSlot) hclockRep final
        (3 : Fin 4)
        (by simp [clockSpec, updateSpec, clockRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [clockSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        hfinalCore
        (by
          dsimp only [clockSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by
          dsimp only [clockSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (boundaryOffset_le_layoutEnd clockSpec.registers 4)
        (by
          change layoutEnd clockSpec.registers - 1 ≤ layoutEnd final
          dsimp only [clockSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by intro _; rfl) hmoveFour hrawFour
      have hhead : boundaryOffset spec.registers (Fin.succ (2 : Fin 4)) =
          firstGapOffset clockSpec.registers 3 := by
        change boundaryOffset spec.registers 3 =
          firstGapOffset clockSpec.registers 3
        simp [clockSpec, updateSpec, clockRegs, final, firstGapOffset,
          boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hfourBack := decrementTape_backedBy hclockBack .clock (by
        simp [clockSpec, updateSpec, clockRegs, final, Registers.get,
          Registers.increment, Registers.decrement, Registers.set])
      have hfinalRegs : (decrementSpec clockSpec .clock (by
          simp [clockSpec, updateSpec, clockRegs, final, Registers.get,
            Registers.increment, Registers.decrement, Registers.set])).registers =
          (decrementSpec spec .temp hpositive).registers := by
        simp [decrementSpec, updateSpec, clockSpec, clockRegs, final,
          Registers.increment, Registers.decrement, Registers.set,
          Registers.get]
      have hfinalTape : decrementTape clockSpec .clock Uclock =
          decrementTape spec .temp T := by
        calc
          decrementTape clockSpec .clock Uclock =
              install (decrementSpec clockSpec .clock (by
                simp [clockSpec, updateSpec, clockRegs, final, Registers.get,
                  Registers.increment, Registers.decrement,
                  Registers.set])).registers spec.growth spec.returnTag outer :=
            hfourBack.installed
          _ = install (decrementSpec spec .temp hpositive).registers
              spec.growth spec.returnTag outer := by rw [hfinalRegs]
          _ = decrementTape spec .temp T := hdesired.installed.symm
      have hclockDecrement : clockSpec.registers.decrement .clock = final := by
        simp [clockSpec, updateSpec, clockRegs, final, Registers.decrement,
          Registers.increment, Registers.set, Registers.get]
      have hresultTape :
          install final clockSpec.growth clockSpec.returnTag
              (writeLogical clockSpec.growth Uclock
                (boundaryOffset clockSpec.registers (Fin.succ (3 : Fin 4)))
                blankSymbol) =
            decrementTape clockSpec .clock Uclock := by
        rw [decrementTape, clearOldLayoutEnd, hclockDecrement]
        rw [show boundaryOffset clockSpec.registers
          (Fin.succ (3 : Fin 4)) = layoutEnd clockSpec.registers by rfl]
      rw [hhead] at hthree
      rw [hresultTape, hfinalTape] at hfour
      simp only [clockSpec, updateSpec] at hthree hfour
      have hhead' : boundaryOffset spec.registers (3 : Fin 5) =
          firstGapOffset clockRegs 3 := by
        simpa [clockSpec, updateSpec] using hhead
      have hUclock :
          install clockRegs spec.growth spec.returnTag
              (writeLogical spec.growth T (firstGapOffset clockRegs 3)
                blankSymbol) = Uclock := by
        dsimp only [Uclock]
        rw [← hhead']
      rw [hUclock] at hthree
      rw [show boundaryOffset clockRegs (Fin.succ (3 : Fin 4)) =
        layoutEnd clockRegs by rfl, hclockEnd] at hfour
      simp only [searchRef, CounterControlPlan.resolve] at hthree
      apply reaches_and_or_halts ?_ hdesired
      simpa only [MarkerSchedule.decrementStartBoundary, hhead'] using
        reaches_or_halts_trans hthree hfour
  | right =>
      have hp : 0 < spec.registers.right := by
        simpa [Registers.get] using hpositive
      let final := spec.registers.decrement .right
      have hinv : final.increment .right = spec.registers :=
        MarkerSchedule.increment_decrement_registers spec.registers .right
          hpositive
      let tempRegs := final.increment .temp
      let clockRegs := final.increment .clock
      have htempEnd : layoutEnd tempRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [tempRegs, layoutEnd_increment]
      have hclockEnd : layoutEnd clockRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [clockRegs, layoutEnd_increment]
      have htempCore : layoutEnd tempRegs < spec.outerDistance := by
        rw [htempEnd]
        exact spec.core_before_target
      have hmoveTwo := MarkerSchedule.moveRightBoundary_before_temp final
      rw [hinv] at hmoveTwo
      have hrawTwo : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 2 .right .left
          (searchRef spec.growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have htwo := machine_reaches_decrementFirst_or_halts base c
        spec.outerDistance hshort source secondarySearchBase
        (searchRef spec.growth source (secondarySearchBase + 1)) hlimit h
        tempRegs (1 : Fin 4)
        (by simpa [RegisterLayout.values, Registers.get] using hpositive)
        htempCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 2)
        (by
          change boundaryOffset spec.registers 2 - 1 ≤ layoutEnd tempRegs
          rw [htempEnd]
          have hbound := boundaryOffset_le_layoutEnd spec.registers (2 : Fin 5)
          omega)
        (by
          intro hlt
          rw [htempEnd] at hlt
          omega)
        hmoveTwo hrawTwo
      let Utemp := install tempRegs spec.growth spec.returnTag
        (writeLogical spec.growth T (boundaryOffset spec.registers 2)
          blankSymbol)
      let tempSpec := updateSpec spec tempRegs htempCore
      have htempBack : BackedBy tempSpec Utemp outer :=
        install_clear_inside_backedBy hback tempRegs htempCore
          (boundaryOffset spec.registers 2) (by simp [boundaryOffset])
          (by rw [htempEnd]; exact boundaryOffset_le_layoutEnd _ 2)
          (by omega)
      have hclockCore : layoutEnd clockRegs < tempSpec.outerDistance := by
        simpa [tempSpec, updateSpec, hclockEnd] using spec.core_before_target
      have hmoveThree : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape tempSpec.registers)
          (MarkerTape.boundaryPosition tempSpec.registers 3) 3 =
        MarkerTape.canonicalTape clockRegs := by
        simpa [tempSpec, updateSpec, tempRegs, clockRegs] using
          MarkerSchedule.moveTempBoundary_before_clock final
      have hrawThree : RawCommand.markerShift
          ⟨tempSpec.growth, source, secondarySearchBase + 1⟩ 3 .right .left
          (searchRef tempSpec.growth source (secondarySearchBase + 2))
          (some .right) none ∈ rawCommands := by
        simpa [tempSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 1⟩ 3 .right .left
            (searchRef spec.growth source (secondarySearchBase + 2))
            (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hthree := machine_reaches_decrementFollowing_or_halts base c
        spec.outerDistance (by simpa [tempSpec, updateSpec] using hshort)
        source (secondarySearchBase + 1)
        (searchRef tempSpec.growth source (secondarySearchBase + 2))
        htempBack.represents clockRegs (2 : Fin 4)
        (by simp [tempSpec, updateSpec, tempRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [tempSpec, updateSpec] using
          registerValue_lt_outerDistance htempBack.represents (2 : Fin 4))
        hclockCore
        (by
          dsimp only [tempSpec, updateSpec]
          rw [hclockEnd, htempEnd])
        (by
          dsimp only [tempSpec, updateSpec]
          rw [hclockEnd, htempEnd]
          omega)
        (boundaryOffset_le_layoutEnd tempSpec.registers 3)
        (by
          dsimp only [tempSpec, updateSpec]
          have hbound := boundaryOffset_le_layoutEnd tempRegs
            (Fin.succ (2 : Fin 4))
          rw [htempEnd] at hbound
          omega)
        (by
          dsimp only [tempSpec, updateSpec]
          intro hlt
          rw [hclockEnd, htempEnd] at hlt
          omega)
        hmoveThree hrawThree
      let Uclock := install clockRegs tempSpec.growth tempSpec.returnTag
        (writeLogical tempSpec.growth Utemp
          (boundaryOffset tempSpec.registers 3) blankSymbol)
      let clockSpec := updateSpec tempSpec clockRegs hclockCore
      have hclockBack : BackedBy clockSpec Uclock outer :=
        install_clear_inside_backedBy htempBack clockRegs hclockCore
          (boundaryOffset tempSpec.registers 3) (by simp [boundaryOffset])
          (by
            dsimp only [tempSpec, updateSpec]
            have hbound := boundaryOffset_le_layoutEnd tempRegs (3 : Fin 5)
            rw [htempEnd] at hbound
            rw [hclockEnd]
            exact hbound)
          (by
            dsimp only [tempSpec, updateSpec]
            rw [hclockEnd, htempEnd])
      have hfinalCore : layoutEnd final < clockSpec.outerDistance := by
        have hlt := layoutEnd_decrement_lt spec.registers .right hpositive
        simpa [clockSpec, tempSpec, updateSpec, final] using
          hlt.trans spec.core_before_target
      have hfinalEnd : layoutEnd final + 1 = layoutEnd spec.registers := by
        exact layoutEnd_decrement_add_one spec.registers .right hpositive
      have hmoveFour : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape clockSpec.registers)
          (MarkerTape.boundaryPosition clockSpec.registers 4) 4 =
        MarkerTape.canonicalTape final := by
        simpa [clockSpec, tempSpec, updateSpec, clockRegs] using
          MarkerSchedule.moveClockBoundary_after_increment final
      have hrawFour : RawCommand.markerShift
          ⟨clockSpec.growth, source, secondarySearchBase + 2⟩ 4 .right .left
          (directRef clockSpec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        simpa [clockSpec, tempSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 2⟩ 4 .right .left
            (directRef spec.growth source finishDirectSlot) (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hfour := machine_reaches_decrementFollowing_or_halts base c
        spec.outerDistance
        (by simpa [clockSpec, tempSpec, updateSpec] using hshort)
        source (secondarySearchBase + 2)
        (directRef clockSpec.growth source finishDirectSlot)
        hclockBack.represents final (3 : Fin 4)
        (by simp [clockSpec, tempSpec, updateSpec, clockRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [clockSpec, tempSpec, updateSpec] using
          registerValue_lt_outerDistance hclockBack.represents (3 : Fin 4))
        hfinalCore
        (by
          dsimp only [clockSpec, tempSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by
          dsimp only [clockSpec, tempSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (boundaryOffset_le_layoutEnd clockSpec.registers 4)
        (by
          change layoutEnd clockSpec.registers - 1 ≤ layoutEnd final
          dsimp only [clockSpec, tempSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by intro _; rfl) hmoveFour hrawFour
      have hheadTwo :
          boundaryOffset spec.registers (Fin.succ (1 : Fin 4)) =
          firstGapOffset tempSpec.registers 2 := by
        change boundaryOffset spec.registers 2 =
          firstGapOffset tempSpec.registers 2
        rw [← hinv]
        simp [tempSpec, updateSpec, tempRegs, final, firstGapOffset,
          boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hheadThree :
          boundaryOffset tempSpec.registers (Fin.succ (2 : Fin 4)) =
          firstGapOffset clockSpec.registers 3 := by
        change boundaryOffset tempSpec.registers 3 =
          firstGapOffset clockSpec.registers 3
        simp [clockSpec, tempSpec, updateSpec, clockRegs, tempRegs, final,
          firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hfourBack := decrementTape_backedBy hclockBack .clock (by
        simp [clockSpec, tempSpec, updateSpec, clockRegs, final,
          Registers.get, Registers.increment, Registers.decrement,
          Registers.set])
      have hfinalTape : decrementTape clockSpec .clock Uclock =
          decrementTape spec .right T := by
        calc
          _ = install final spec.growth spec.returnTag outer := by
            simpa [clockSpec, tempSpec, updateSpec, clockRegs, final,
              decrementSpec, Registers.increment, Registers.decrement,
              Registers.set, Registers.get] using hfourBack.installed
          _ = _ := by
            simpa [final, decrementSpec, updateSpec] using hdesired.installed.symm
      have hclockDecrement : clockSpec.registers.decrement .clock = final := by
        simp [clockSpec, tempSpec, updateSpec, clockRegs, final,
          Registers.decrement, Registers.increment, Registers.set,
          Registers.get]
      have hresultTape :
          install final clockSpec.growth clockSpec.returnTag
              (writeLogical clockSpec.growth Uclock
                (boundaryOffset clockSpec.registers (Fin.succ (3 : Fin 4)))
                blankSymbol) =
            decrementTape clockSpec .clock Uclock := by
        rw [decrementTape, clearOldLayoutEnd, hclockDecrement]
        rw [show boundaryOffset clockSpec.registers
          (Fin.succ (3 : Fin 4)) = layoutEnd clockSpec.registers by rfl]
      rw [hresultTape, hfinalTape] at hfour
      have hheadTwo' : boundaryOffset spec.registers (2 : Fin 5) =
          firstGapOffset tempRegs 2 := by
        simpa [tempSpec, updateSpec] using hheadTwo
      have hheadThree' : boundaryOffset tempRegs (3 : Fin 5) =
          firstGapOffset clockRegs 3 := by
        simpa [clockSpec, tempSpec, updateSpec] using hheadThree
      rw [hheadTwo] at htwo
      rw [hheadThree] at hthree
      simp only [tempSpec, clockSpec, updateSpec] at htwo hthree hfour
      have hUtemp :
          install tempRegs spec.growth spec.returnTag
              (writeLogical spec.growth T (firstGapOffset tempRegs 2)
                blankSymbol) = Utemp := by
        dsimp only [Utemp]
        rw [← hheadTwo']
      have hUclock :
          install clockRegs spec.growth spec.returnTag
              (writeLogical spec.growth Utemp (firstGapOffset clockRegs 3)
                blankSymbol) = Uclock := by
        dsimp only [Uclock, tempSpec, updateSpec]
        rw [← hheadThree']
      rw [hUtemp] at htwo
      rw [hUclock] at hthree
      rw [show boundaryOffset clockRegs (Fin.succ (3 : Fin 4)) =
        layoutEnd clockRegs by rfl, hclockEnd] at hfour
      simp only [searchRef, CounterControlPlan.resolve] at htwo hthree
      apply reaches_and_or_halts ?_ hdesired
      simpa only [MarkerSchedule.decrementStartBoundary, hheadTwo'] using
        reaches_or_halts_trans htwo (reaches_or_halts_trans hthree hfour)
  | left =>
      have hp : 0 < spec.registers.left := by
        simpa [Registers.get] using hpositive
      let final := spec.registers.decrement .left
      have hinv : final.increment .left = spec.registers :=
        MarkerSchedule.increment_decrement_registers spec.registers .left
          hpositive
      let rightRegs := final.increment .right
      let tempRegs := final.increment .temp
      let clockRegs := final.increment .clock
      have hrightEnd : layoutEnd rightRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [rightRegs, layoutEnd_increment]
      have htempEnd : layoutEnd tempRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [tempRegs, layoutEnd_increment]
      have hclockEnd : layoutEnd clockRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [clockRegs, layoutEnd_increment]
      have hrightCore : layoutEnd rightRegs < spec.outerDistance := by
        rw [hrightEnd]
        exact spec.core_before_target
      have hmoveOne := MarkerSchedule.moveLeftBoundary_before_right final
      rw [hinv] at hmoveOne
      have hrawOne : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 1 .right .left
          (searchRef spec.growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have hone := machine_reaches_decrementFirst_or_halts base c
        spec.outerDistance hshort source secondarySearchBase
        (searchRef spec.growth source (secondarySearchBase + 1)) hlimit h
        rightRegs (0 : Fin 4)
        (by simpa [RegisterLayout.values, Registers.get] using hpositive)
        hrightCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 1)
        (by
          change boundaryOffset spec.registers 1 - 1 ≤ layoutEnd rightRegs
          rw [hrightEnd]
          have hbound := boundaryOffset_le_layoutEnd spec.registers (1 : Fin 5)
          omega)
        (by
          intro hlt
          rw [hrightEnd] at hlt
          omega)
        hmoveOne hrawOne
      let Uright := install rightRegs spec.growth spec.returnTag
        (writeLogical spec.growth T (boundaryOffset spec.registers 1)
          blankSymbol)
      let rightSpec := updateSpec spec rightRegs hrightCore
      have hrightBack : BackedBy rightSpec Uright outer :=
        install_clear_inside_backedBy hback rightRegs hrightCore
          (boundaryOffset spec.registers 1) (by simp [boundaryOffset])
          (by rw [hrightEnd]; exact boundaryOffset_le_layoutEnd _ 1)
          (by omega)
      have htempCore : layoutEnd tempRegs < rightSpec.outerDistance := by
        simpa [rightSpec, updateSpec, htempEnd] using spec.core_before_target
      have hmoveTwo : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape rightSpec.registers)
          (MarkerTape.boundaryPosition rightSpec.registers 2) 2 =
        MarkerTape.canonicalTape tempRegs := by
        simpa [rightSpec, updateSpec, rightRegs, tempRegs] using
          MarkerSchedule.moveRightBoundary_before_temp final
      have hrawTwo : RawCommand.markerShift
          ⟨rightSpec.growth, source, secondarySearchBase + 1⟩ 2 .right .left
          (searchRef rightSpec.growth source (secondarySearchBase + 2))
          (some .right) none ∈ rawCommands := by
        simpa [rightSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 1⟩ 2 .right .left
            (searchRef spec.growth source (secondarySearchBase + 2))
            (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have htwo := machine_reaches_decrementFollowing_or_halts base c
        spec.outerDistance (by simpa [rightSpec, updateSpec] using hshort)
        source (secondarySearchBase + 1)
        (searchRef rightSpec.growth source (secondarySearchBase + 2))
        hrightBack.represents tempRegs (1 : Fin 4)
        (by simp [rightSpec, updateSpec, rightRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [rightSpec, updateSpec] using
          registerValue_lt_outerDistance hrightBack.represents (1 : Fin 4))
        htempCore
        (by
          dsimp only [rightSpec, updateSpec]
          rw [htempEnd, hrightEnd])
        (by
          dsimp only [rightSpec, updateSpec]
          rw [htempEnd, hrightEnd]
          omega)
        (boundaryOffset_le_layoutEnd rightSpec.registers 2)
        (by
          dsimp only [rightSpec, updateSpec]
          have hbound := boundaryOffset_le_layoutEnd rightRegs
            (Fin.succ (1 : Fin 4))
          rw [hrightEnd] at hbound
          omega)
        (by
          dsimp only [rightSpec, updateSpec]
          intro hlt
          rw [htempEnd, hrightEnd] at hlt
          omega)
        hmoveTwo hrawTwo
      let Utemp := install tempRegs rightSpec.growth rightSpec.returnTag
        (writeLogical rightSpec.growth Uright
          (boundaryOffset rightSpec.registers 2) blankSymbol)
      let tempSpec := updateSpec rightSpec tempRegs htempCore
      have htempBack : BackedBy tempSpec Utemp outer :=
        install_clear_inside_backedBy hrightBack tempRegs htempCore
          (boundaryOffset rightSpec.registers 2) (by simp [boundaryOffset])
          (by
            dsimp only [rightSpec, updateSpec]
            have hbound := boundaryOffset_le_layoutEnd rightRegs (2 : Fin 5)
            rw [hrightEnd] at hbound
            rw [htempEnd]
            exact hbound)
          (by
            dsimp only [rightSpec, updateSpec]
            rw [htempEnd, hrightEnd])
      have hclockCore : layoutEnd clockRegs < tempSpec.outerDistance := by
        simpa [tempSpec, rightSpec, updateSpec, hclockEnd] using
          spec.core_before_target
      have hmoveThree : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape tempSpec.registers)
          (MarkerTape.boundaryPosition tempSpec.registers 3) 3 =
        MarkerTape.canonicalTape clockRegs := by
        simpa [tempSpec, rightSpec, updateSpec, tempRegs, clockRegs] using
          MarkerSchedule.moveTempBoundary_before_clock final
      have hrawThree : RawCommand.markerShift
          ⟨tempSpec.growth, source, secondarySearchBase + 2⟩ 3 .right .left
          (searchRef tempSpec.growth source (secondarySearchBase + 3))
          (some .right) none ∈ rawCommands := by
        simpa [tempSpec, rightSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 2⟩ 3 .right .left
            (searchRef spec.growth source (secondarySearchBase + 3))
            (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hthree := machine_reaches_decrementFollowing_or_halts base c
        spec.outerDistance
        (by simpa [tempSpec, rightSpec, updateSpec] using hshort)
        source (secondarySearchBase + 2)
        (searchRef tempSpec.growth source (secondarySearchBase + 3))
        htempBack.represents clockRegs (2 : Fin 4)
        (by simp [tempSpec, rightSpec, updateSpec, tempRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [tempSpec, rightSpec, updateSpec] using
          registerValue_lt_outerDistance htempBack.represents (2 : Fin 4))
        hclockCore
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          rw [hclockEnd, htempEnd])
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          rw [hclockEnd, htempEnd]
          omega)
        (boundaryOffset_le_layoutEnd tempSpec.registers 3)
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          have hbound := boundaryOffset_le_layoutEnd tempRegs
            (Fin.succ (2 : Fin 4))
          rw [htempEnd] at hbound
          omega)
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          intro hlt
          rw [hclockEnd, htempEnd] at hlt
          omega)
        hmoveThree hrawThree
      let Uclock := install clockRegs tempSpec.growth tempSpec.returnTag
        (writeLogical tempSpec.growth Utemp
          (boundaryOffset tempSpec.registers 3) blankSymbol)
      let clockSpec := updateSpec tempSpec clockRegs hclockCore
      have hclockBack : BackedBy clockSpec Uclock outer :=
        install_clear_inside_backedBy htempBack clockRegs hclockCore
          (boundaryOffset tempSpec.registers 3) (by simp [boundaryOffset])
          (by
            dsimp only [tempSpec, rightSpec, updateSpec]
            have hbound := boundaryOffset_le_layoutEnd tempRegs (3 : Fin 5)
            rw [htempEnd] at hbound
            rw [hclockEnd]
            exact hbound)
          (by
            dsimp only [tempSpec, rightSpec, updateSpec]
            rw [hclockEnd, htempEnd])
      have hfinalCore : layoutEnd final < clockSpec.outerDistance := by
        have hlt := layoutEnd_decrement_lt spec.registers .left hpositive
        simpa [clockSpec, tempSpec, rightSpec, updateSpec, final] using
          hlt.trans spec.core_before_target
      have hfinalEnd : layoutEnd final + 1 = layoutEnd spec.registers := by
        exact layoutEnd_decrement_add_one spec.registers .left hpositive
      have hmoveFour : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape clockSpec.registers)
          (MarkerTape.boundaryPosition clockSpec.registers 4) 4 =
        MarkerTape.canonicalTape final := by
        simpa [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs] using
          MarkerSchedule.moveClockBoundary_after_increment final
      have hrawFour : RawCommand.markerShift
          ⟨clockSpec.growth, source, secondarySearchBase + 3⟩ 4 .right .left
          (directRef clockSpec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        simpa [clockSpec, tempSpec, rightSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 3⟩ 4 .right .left
            (directRef spec.growth source finishDirectSlot) (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hfour := machine_reaches_decrementFollowing_or_halts base c
        spec.outerDistance
        (by simpa [clockSpec, tempSpec, rightSpec, updateSpec] using hshort)
        source (secondarySearchBase + 3)
        (directRef clockSpec.growth source finishDirectSlot)
        hclockBack.represents final (3 : Fin 4)
        (by simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [clockSpec, tempSpec, rightSpec, updateSpec] using
          registerValue_lt_outerDistance hclockBack.represents (3 : Fin 4))
        hfinalCore
        (by
          dsimp only [clockSpec, tempSpec, rightSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by
          dsimp only [clockSpec, tempSpec, rightSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (boundaryOffset_le_layoutEnd clockSpec.registers 4)
        (by
          change layoutEnd clockSpec.registers - 1 ≤ layoutEnd final
          dsimp only [clockSpec, tempSpec, rightSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by intro _; rfl) hmoveFour hrawFour
      have hheadOne :
          boundaryOffset spec.registers (Fin.succ (0 : Fin 4)) =
          firstGapOffset rightSpec.registers 1 := by
        change boundaryOffset spec.registers 1 =
          firstGapOffset rightSpec.registers 1
        rw [← hinv]
        simp [rightSpec, updateSpec, rightRegs, final, firstGapOffset,
          boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
          Registers.increment, Registers.decrement, Registers.set,
          Registers.get]
      have hheadTwo :
          boundaryOffset rightSpec.registers (Fin.succ (1 : Fin 4)) =
          firstGapOffset tempSpec.registers 2 := by
        change boundaryOffset rightSpec.registers 2 =
          firstGapOffset tempSpec.registers 2
        simp [tempSpec, rightSpec, updateSpec, tempRegs, rightRegs, final,
          firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hheadThree :
          boundaryOffset tempSpec.registers (Fin.succ (2 : Fin 4)) =
          firstGapOffset clockSpec.registers 3 := by
        change boundaryOffset tempSpec.registers 3 =
          firstGapOffset clockSpec.registers 3
        simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, tempRegs,
          final, firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hfourBack := decrementTape_backedBy hclockBack .clock (by
        simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, final,
          Registers.get, Registers.increment, Registers.decrement,
          Registers.set])
      have hfinalTape : decrementTape clockSpec .clock Uclock =
          decrementTape spec .left T := by
        calc
          _ = install final spec.growth spec.returnTag outer := by
            simpa [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs,
              final, decrementSpec, Registers.increment, Registers.decrement,
              Registers.set, Registers.get] using hfourBack.installed
          _ = _ := by
            simpa [final, decrementSpec, updateSpec] using hdesired.installed.symm
      have hclockDecrement : clockSpec.registers.decrement .clock = final := by
        simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, final,
          Registers.decrement, Registers.increment, Registers.set,
          Registers.get]
      have hresultTape :
          install final clockSpec.growth clockSpec.returnTag
              (writeLogical clockSpec.growth Uclock
                (boundaryOffset clockSpec.registers (Fin.succ (3 : Fin 4)))
                blankSymbol) =
            decrementTape clockSpec .clock Uclock := by
        rw [decrementTape, clearOldLayoutEnd, hclockDecrement]
        rw [show boundaryOffset clockSpec.registers
          (Fin.succ (3 : Fin 4)) = layoutEnd clockSpec.registers by rfl]
      rw [hresultTape, hfinalTape] at hfour
      have hheadOne' : boundaryOffset spec.registers (1 : Fin 5) =
          firstGapOffset rightRegs 1 := by
        simpa [rightSpec, updateSpec] using hheadOne
      have hheadTwo' : boundaryOffset rightRegs (2 : Fin 5) =
          firstGapOffset tempRegs 2 := by
        simpa [tempSpec, rightSpec, updateSpec] using hheadTwo
      have hheadThree' : boundaryOffset tempRegs (3 : Fin 5) =
          firstGapOffset clockRegs 3 := by
        simpa [clockSpec, tempSpec, rightSpec, updateSpec] using hheadThree
      rw [hheadOne] at hone
      rw [hheadTwo] at htwo
      rw [hheadThree] at hthree
      simp only [rightSpec, tempSpec, clockSpec, updateSpec] at hone htwo hthree hfour
      have hUright :
          install rightRegs spec.growth spec.returnTag
              (writeLogical spec.growth T (firstGapOffset rightRegs 1)
                blankSymbol) = Uright := by
        dsimp only [Uright]
        rw [← hheadOne']
      have hUtemp :
          install tempRegs spec.growth spec.returnTag
              (writeLogical spec.growth Uright (firstGapOffset tempRegs 2)
                blankSymbol) = Utemp := by
        dsimp only [Utemp, rightSpec, updateSpec]
        rw [← hheadTwo']
      have hUclock :
          install clockRegs spec.growth spec.returnTag
              (writeLogical spec.growth Utemp (firstGapOffset clockRegs 3)
                blankSymbol) = Uclock := by
        dsimp only [Uclock, tempSpec, rightSpec, updateSpec]
        rw [← hheadThree']
      rw [hUright] at hone
      rw [hUtemp] at htwo
      rw [hUclock] at hthree
      rw [show boundaryOffset clockRegs (Fin.succ (3 : Fin 4)) =
        layoutEnd clockRegs by rfl, hclockEnd] at hfour
      simp only [searchRef, CounterControlPlan.resolve] at hone htwo hthree
      apply reaches_and_or_halts ?_ hdesired
      simpa only [MarkerSchedule.decrementStartBoundary, hheadOne'] using
        reaches_or_halts_trans hone
          (reaches_or_halts_trans htwo
            (reaches_or_halts_trans hthree hfour))



/-- The final blank rule leaves the vacated old boundary cell and moves left
onto boundary `4` of the decremented logical frame. -/
theorem machine_reaches_decrementPositiveFinish
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} (T : FullTM0.Tape (Symbol numTags))
    (hpositive : 0 < spec.registers.get register) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source finishDirectSlot),
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth ifPositive,
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd (spec.registers.decrement register))⟩ := by
  let raw : RawDirectRule :=
    ⟨spec.growth, directRef spec.growth source finishDirectSlot, .blank,
      .logical spec.growth ifPositive, .left⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [raw, decrementRules]
  have hmatch : raw.read.Matches
      (atLogical spec.growth (decrementTape spec register T)
        (layoutEnd spec.registers)).read := by
    change (atLogical spec.growth (decrementTape spec register T)
      (layoutEnd spec.registers)).read = blankSymbol
    rw [atLogical_read]
    exact decrementTape_old_layoutEnd_blank spec register T hpositive
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical spec.growth (decrementTape spec register T)
      (layoutEnd spec.registers)) hmatch
  have hend := layoutEnd_decrement_add_one spec.registers register hpositive
  have hmove : (atLogical spec.growth (decrementTape spec register T)
      (layoutEnd spec.registers)).move (orient spec.growth .left) =
      atLogical spec.growth (decrementTape spec register T)
        (layoutEnd (spec.registers.decrement register)) := by
    rw [← hend, orient_eq_orientDirection, atLogical_move_left]
  rw [hmove] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef spec.growth source finishDirectSlot),
      atLogical spec.growth (decrementTape spec register T)
        (layoutEnd spec.registers)⟩
    ⟨logicalState base c spec.growth ifPositive,
      atLogical spec.growth (decrementTape spec register T)
        (layoutEnd (spec.registers.decrement register))⟩ at hrun
  exact hrun

/-- Exact positive branch of a compiled conditional decrement.  Every
shorter search either completes the decremented logical frame or exposes a
halt from the instruction entry. -/
theorem machine_reaches_decrementPositiveInstruction_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hpositive : 0 < spec.registers.get register)
    (hshort : ShortResolves base c spec.outerDistance) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth ifPositive,
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd (spec.registers.decrement register))⟩ ∧
      BackedBy (decrementSpec spec register hpositive)
        (decrementTape spec register T) outer) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_or_halts base c spec.growth
    source (.decrement register ifZero ifPositive) hrule h rfl hshort
  have hroute := machine_reaches_decrementToTest_or_halts base c source
    ifZero ifPositive register hrule h hshort
  have htest := machine_reaches_decrementTest base c source ifZero ifPositive
    register hrule T (by
      rw [atLogical_read]
      exact h.boundary _)
  have hhandoff := machine_reaches_decrementPositiveHandoff base c source
    ifZero ifPositive register hrule h hpositive
  have hcommands : ∀ raw,
      raw ∈ decrementShiftCommands spec.growth source register →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, decrementCommands, hraw]
  have hschedule := machine_reaches_decrementSchedule_or_halts base c source
    register hback hpositive hshort hcommands
  have hfinish := machine_reaches_decrementPositiveFinish base c source
    ifZero ifPositive register hrule T hpositive
  have hscheduleFinish :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨spec.growth, source, secondarySearchBase⟩,
            atLogical spec.growth T
              (boundaryOffset spec.registers
                (MarkerSchedule.decrementStartBoundary register))⟩
          ⟨logicalState base c spec.growth ifPositive,
            atLogical spec.growth (decrementTape spec register T)
              (layoutEnd (spec.registers.decrement register))⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨spec.growth, source, secondarySearchBase⟩,
            atLogical spec.growth T
              (boundaryOffset spec.registers
                (MarkerSchedule.decrementStartBoundary register))⟩ := by
    rcases hschedule with hschedule | hhalts
    · exact Or.inl (hschedule.1.trans hfinish)
    · exact Or.inr hhalts
  have hrun := reaches_or_halts_trans hvalidation
    (reaches_or_halts_trans hroute
      (reaches_or_halts_trans (Or.inl htest)
        (reaches_or_halts_trans (Or.inl hhandoff) hscheduleFinish)))
  exact reaches_and_or_halts hrun
    (decrementTape_backedBy hback register hpositive)

/-! ## Abstract-step interface -/

/-- Successful concrete realization of an abstract counter configuration.
The existential core bound packages exactly the updated frame specification
needed by the next simultaneous-induction step. -/
def LogicalStepReached
    (base : Nat) (c : Nat.Partrec.Code)
    (source : Nat) (next : CounterMachine.Cfg)
    (spec : Spec numTags) (T outer : FullTM0.Tape (Symbol numTags)) : Prop :=
  ∃ (hcore : layoutEnd next.registers < spec.outerDistance)
      (nextTape : FullTM0.Tape (Symbol numTags)),
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth next.state,
          atLogical spec.growth nextTape (layoutEnd next.registers)⟩ ∧
      BackedBy (updateSpec spec next.registers hcore) nextTape outer

/-- Concrete boundary exposed when a requested increment collides with the
suspended outer target instead of producing a larger logical frame. -/
def IncrementCollisionReached
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (spec : Spec numTags) (T : FullTM0.Tape (Symbol numTags)) : Prop :=
  ∃ (register : Register) (next : Nat),
    (source, .increment register next) ∈ GlobalSourceProgram.program ∧
      layoutEnd spec.registers + 1 = spec.outerDistance ∧
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterFour spec T)
            spec.outerDistance⟩

/-- Uniform instruction-case API below the framed trace layer.  A defined
abstract step either reaches its exact backed successor, exposes the unique
increment-collision cleanup endpoint, or halts from the original logical
configuration. -/
theorem machine_resolves_counterStep
    (base : Nat) (c : Nat.Partrec.Code)
    (cfg nextCfg : CounterMachine.Cfg)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hregisters : cfg.registers = spec.registers)
    (hstep : CounterMachine.step GlobalSourceProgram.program cfg =
      some nextCfg)
    (hshort : ShortResolves base c spec.outerDistance) :
    LogicalStepReached base c cfg.state nextCfg spec T outer ∨
      IncrementCollisionReached base c cfg.state spec T ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth cfg.state,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  rcases cfg with ⟨source, registers⟩
  change registers = spec.registers at hregisters
  subst registers
  have hcase := CounterControlStepGeometry.stepCase_of_step_eq_some hstep
  cases hcase with
  | increment register target hlookup hnext =>
      subst nextCfg
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup
      rcases increment_has_room_or_collision spec register with
        hroom | hcollision
      · have hrun := machine_reaches_incrementInstruction_or_halts base c
          source target register hrule hback hroom hshort
        rcases hrun with hsuccess | hhalts
        · left
          refine ⟨hroom, incrementTape spec register T, hsuccess.1, ?_⟩
          simpa [incrementSpec] using hsuccess.2
        · exact Or.inr (Or.inr hhalts)
      · have hcollision' :
            layoutEnd spec.registers + 1 = spec.outerDistance :=
          (increment_collision_iff spec register).1 hcollision
        have hrun := machine_reaches_incrementCollisionInstruction_or_halts
          base c source target register hrule hback.represents hcollision'
          hshort
        rcases hrun with hsuccess | hhalts
        · exact Or.inr (Or.inl
            ⟨register, target, hrule, hcollision', hsuccess⟩)
        · exact Or.inr (Or.inr hhalts)
  | decrementZero register ifZero ifPositive hlookup hzero hnext =>
      subst nextCfg
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup
      have hrun := machine_reaches_decrementZeroInstruction_or_halts base c
        source ifZero ifPositive register hrule hback hzero hshort
      rcases hrun with hsuccess | hhalts
      · left
        refine ⟨spec.core_before_target, T, hsuccess.1, ?_⟩
        simpa [updateSpec] using hsuccess.2
      · exact Or.inr (Or.inr hhalts)
  | decrementPositive register ifZero ifPositive hlookup hpositive hnext =>
      subst nextCfg
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup
      have hrun := machine_reaches_decrementPositiveInstruction_or_halts
        base c source ifZero ifPositive register hrule hback hpositive hshort
      rcases hrun with hsuccess | hhalts
      · left
        let hcore := CounterControlStepGeometry.decrement_has_room spec
          register hpositive
        refine ⟨hcore, decrementTape spec register T, hsuccess.1, ?_⟩
        simpa [decrementSpec] using hsuccess.2
      · exact Or.inr (Or.inr hhalts)

/-- The complete compiled counter controller resolves one abstract step in
every represented nested frame.  The three outcomes are exactly those used
by the generic trace lifting layer: a backed logical successor, restoration
of the suspended search boundary, or concrete halting. -/
theorem oneStepResolves
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) CounterControlSearchSystem.Search)
    (hshort : ShortResolves base c frame.distance) :
    CounterControlTraceSimulation.OneStepResolves base c frame := by
  intro current next concrete hstep hlogical
  rcases hlogical with
    ⟨hcore, T, hback, rfl, _hstate, hframe⟩
  let spec := CounterControlFrameSimulation.activeSpec base c frame
    current.registers hcore
  change BackedBy spec T frame.outer at hback
  have hrun := machine_resolves_counterStep base c current next
    (spec := spec) hback
    (by simp [spec]) hstep
    (by simpa [spec] using hshort)
  rcases hrun with hnext | hcollision | hhalts
  · rcases hnext with ⟨hnextCore, nextTape, hreach, hnextBack⟩
    have hnextCore' : layoutEnd next.registers < frame.distance := by
      simpa [spec] using hnextCore
    have hnextBack' : BackedBy
        (CounterControlFrameSimulation.activeSpec base c frame
          next.registers hnextCore') nextTape frame.outer := by
      simpa [spec, CounterControlFrameSimulation.activeSpec, updateSpec] using
        hnextBack
    let nextConcrete := CounterControlFrameSimulation.logicalCfg base c frame
      next nextTape
    have hnextFrame : CounterControlFrameSimulation.LogicalFrame base c frame
        next nextConcrete := by
      exact ⟨hnextCore', nextTape, hnextBack', rfl,
        CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep,
        hframe⟩
    left
    refine ⟨nextConcrete, ?_, hnextFrame⟩
    simpa [nextConcrete, CounterControlFrameSimulation.logicalCfg, spec,
      CounterControlFrameSimulation.activeSpec] using hreach
  · rcases hcollision with
      ⟨register, target, hrule, hcollision, hcollisionReach⟩
    have hentry : CounterControlCleanupSemantics.cleanupEntryRule
        spec.growth current.state ∈ rawDirectRules := by
      apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
      change CounterControlCleanupSemantics.cleanupEntryRule
          spec.growth current.state ∈
        validationRules spec.growth current.state ++
          incrementRules spec.growth current.state target register
      apply List.mem_append_right
      simp [CounterControlCleanupSemantics.cleanupEntryRule, incrementRules]
    have hcleanupCommands : ∀ raw,
        raw ∈ cleanupCommands spec.growth current.state →
          raw ∈ rawCommands := by
      intro raw hraw
      apply command_mem_rawCommands_of_rule spec.growth hrule
      simp [commandsForRule, incrementCommands, hraw]
    have hreturnDirection :
        (compileCommand base c spec.returnTag).searchDirection =
          spec.growth := by
      simp [spec, CounterControlFrameSimulation.activeSpec,
        CounterControlFrameSimulation.frameGrowth,
        CounterControlSearchSystem.command]
    have hcleanup := machine_reaches_collisionCleanup_or_halts base c
      current.state hback hreturnDirection hcollision
      (by simpa [spec] using hshort) hentry hcleanupCommands
    have hcombined := reaches_or_halts_trans (Or.inl hcollisionReach)
      hcleanup
    rcases hcombined with hboundaryReach | hhalts
    · let boundary : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
        ⟨resumeState (CanonicalInitializer.radius c)
            (CounterControlSearchSystem.commandOffset base c frame.saved),
          frame.outer⟩
      have hboundary : CounterControlSearchSystem.BoundaryAt base c frame
          boundary := ⟨hframe, rfl⟩
      right
      left
      refine ⟨boundary, ?_, hboundary⟩
      simpa [boundary, CounterControlFrameSimulation.logicalCfg, spec,
        CounterControlFrameSimulation.activeSpec,
        CounterControlSearchSystem.command,
        CounterControlSearchSystem.commandOffset] using hboundaryReach
    · right
      right
      simpa [CounterControlFrameSimulation.logicalCfg, spec,
        CounterControlFrameSimulation.activeSpec] using hhalts
  · right
    right
    simpa [CounterControlFrameSimulation.logicalCfg, spec,
      CounterControlFrameSimulation.activeSpec] using hhalts

end

end CounterControlInstructionResolution
end Hooper
end Kari
end LeanWang
