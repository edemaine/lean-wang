/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCommandAt
import LeanWang.Kari.Hooper.CounterControlBridge
import LeanWang.Kari.Hooper.CounterControlNestingBridge

/-!
# Navigation semantics for generated counter commands

This module connects the symbolic boundary- and tag-navigation commands of
the counter plan to their compiled bounded searches.  Every theorem is
command-oriented: membership of the displayed `RawCommand` in `rawCommands`
selects its unique return tag and controller block.

A nearby search executes its continuation and reaches the exact advertised
tape.  A far search instead launches the tag-selected canonical initializer;
the alternative retains both the strict distance proof and the resulting
finite-frame representation.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlNavigationSemantics

open Turing
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlCommandAt CounterControlBridge

noncomputable section

/-! ## A raw-command form of the nesting bridge -/

/-- A failed search selected by a generated raw command reaches its exact
tag-selected canonical input.  This packages the enumeration-free interface
to `CounterControlNestingBridge.machine_reaches_nested`. -/
theorem machine_reaches_raw_nested
    (base : Nat) (c : Nat.Partrec.Code) (raw : RawCommand)
    (hraw : raw ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance)
    (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address, outer⟩
        (CounterControlNestingBridge.nestedCfg base c (rawTag raw hraw)
          outer) ∧
      FramedMarkerTape.Represents
        (FramedMarkerTape.frameSpec c
          (compileRawCommand base c raw hraw) distance hfar)
        (FramedMarkerTape.initializeTape c
          (compileRawCommand base c raw hraw) outer) := by
  simpa only [compileRawCommand, rawCommands_get_rawTag] using
    (CounterControlNestingBridge.machine_reaches_nested base c
      (rawTag raw hraw) outer distance hgap hfar)

/-! ## Boundary navigation -/

/-- A generated preserving boundary search either finds its target nearby
and leaves it unchanged, or launches the exact framed canonical input.
`direction` is logical; the compiled search uses its physical orientation. -/
theorem machine_reaches_boundary_preserve_or_nests
    (base : Nat) (c : Nat.Partrec.Code) (address : SearchAddress)
    (expected : Fin 5) (direction : Turing.Dir) (success : ControlRef)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      .preserve ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩
        ⟨resolve base c success,
          outer.moveN (orient address.growth direction) distance⟩ ∨
      ∃ hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
            ⟨searchState base c address, outer⟩
            (CounterControlNestingBridge.nestedCfg base c
              (rawTag
                (.boundaryNavigation address expected direction success
                  .preserve) hraw) outer) ∧
          FramedMarkerTape.Represents
            (FramedMarkerTape.frameSpec c
              (compileRawCommand base c
                (.boundaryNavigation address expected direction success
                  .preserve) hraw) distance hfar)
            (FramedMarkerTape.initializeTape c
              (compileRawCommand base c
                (.boundaryNavigation address expected direction success
                  .preserve) hraw) outer) := by
  let raw : RawCommand :=
    .boundaryNavigation address expected direction success .preserve
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hspec := compileRawCommand_spec base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c address)
      (.boundaryNavigation expected (orient address.growth direction)
        (resolve base c success) (rawTag raw hraw) .preserve)
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, compileRawAtTag, RawCommand.address,
      compileNavigationAction] using hatRaw
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hspec]
    simpa [raw, compileRawAtTag, Command.target, Command.searchDirection,
      compileNavigationAction] using hgap
  rcases le_or_gt distance
      (NestingMachine.bound (CanonicalInitializer.radius c)) with
    hnear | hfar
  · left
    simpa [CounterControlNestingBridge.machine, raw,
      BoundedMarkerProgram.entryState] using
      (CounterControlBridge.machine_reaches_navigation
        (coreTable base c) (Target.boundary expected)
        (orient address.growth direction) (resolve base c success)
        (rawTag raw hraw) hat outer distance hgap hnear)
  · right
    exact ⟨hfar,
      machine_reaches_raw_nested base c raw hraw outer distance
        hcompiledGap hfar⟩

/-- A generated erasing boundary search either finds its target nearby and
performs the exact optional logical departure, or launches the exact framed
canonical input. -/
theorem machine_reaches_boundary_erase_or_nests
    (base : Nat) (c : Nat.Partrec.Code) (address : SearchAddress)
    (expected : Fin 5) (direction : Turing.Dir) (success : ControlRef)
    (departure : Option Turing.Dir)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      (.erase departure) ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
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
      ∃ hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
            ⟨searchState base c address, outer⟩
            (CounterControlNestingBridge.nestedCfg base c
              (rawTag
                (.boundaryNavigation address expected direction success
                  (.erase departure)) hraw) outer) ∧
          FramedMarkerTape.Represents
            (FramedMarkerTape.frameSpec c
              (compileRawCommand base c
                (.boundaryNavigation address expected direction success
                  (.erase departure)) hraw) distance hfar)
            (FramedMarkerTape.initializeTape c
              (compileRawCommand base c
                (.boundaryNavigation address expected direction success
                  (.erase departure)) hraw) outer) := by
  let raw : RawCommand :=
    .boundaryNavigation address expected direction success (.erase departure)
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hspec := compileRawCommand_spec base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c address)
      (.boundaryNavigation expected (orient address.growth direction)
        (resolve base c success) (rawTag raw hraw)
        (.erase (departure.map (orient address.growth))))
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, compileRawAtTag, RawCommand.address,
      compileNavigationAction] using hatRaw
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hspec]
    simpa [raw, compileRawAtTag, Command.target, Command.searchDirection,
      compileNavigationAction] using hgap
  rcases le_or_gt distance
      (NestingMachine.bound (CanonicalInitializer.radius c)) with
    hnear | hfar
  · left
    have hrun := CounterControlBridge.machine_reaches_erase
      (coreTable base c) expected (orient address.growth direction)
      (resolve base c success) (rawTag raw hraw)
      (departure.map (orient address.growth)) hat outer distance hgap hnear
    cases departure <;>
      simpa [CounterControlNestingBridge.machine, raw,
        BoundedMarkerProgram.entryState] using hrun
  · right
    exact ⟨hfar,
      machine_reaches_raw_nested base c raw hraw outer distance
        hcompiledGap hfar⟩

/-! ## Tag navigation -/

/-- A generated tag search either finds a physical return tag nearby and
preserves it, or launches the exact framed canonical input. -/
theorem machine_reaches_tag_or_nests
    (base : Nat) (c : Nat.Partrec.Code) (address : SearchAddress)
    (direction : Turing.Dir) (success : ControlRef)
    (hraw : RawCommand.tagNavigation address direction success ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.anyTag : Target numTags).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩
        ⟨resolve base c success,
          outer.moveN (orient address.growth direction) distance⟩ ∨
      ∃ hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
            ⟨searchState base c address, outer⟩
            (CounterControlNestingBridge.nestedCfg base c
              (rawTag (.tagNavigation address direction success) hraw) outer) ∧
          FramedMarkerTape.Represents
            (FramedMarkerTape.frameSpec c
              (compileRawCommand base c
                (.tagNavigation address direction success) hraw)
              distance hfar)
            (FramedMarkerTape.initializeTape c
              (compileRawCommand base c
                (.tagNavigation address direction success) hraw) outer) := by
  let raw : RawCommand := .tagNavigation address direction success
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hspec := compileRawCommand_spec base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c address)
      (.tagNavigation (orient address.growth direction)
        (resolve base c success) (rawTag raw hraw))
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, compileRawAtTag, RawCommand.address] using hatRaw
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hspec]
    simpa [raw, compileRawAtTag, Command.target,
      Command.searchDirection] using hgap
  rcases le_or_gt distance
      (NestingMachine.bound (CanonicalInitializer.radius c)) with
    hnear | hfar
  · left
    simpa [CounterControlNestingBridge.machine, raw,
      BoundedMarkerProgram.entryState] using
      (CounterControlBridge.machine_reaches_navigation
        (coreTable base c) (Target.anyTag : Target numTags)
        (orient address.growth direction) (resolve base c success)
        (rawTag raw hraw) hat outer distance hgap hnear)
  · right
    exact ⟨hfar,
      machine_reaches_raw_nested base c raw hraw outer distance
        hcompiledGap hfar⟩

end

end CounterControlNavigationSemantics
end Hooper
end Kari
end LeanWang
