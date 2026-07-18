/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BasicLemmaConverse
import LeanWang.Kari.Hooper.CounterControlNestingBridge

/-!
# The compiled counter controller as a Hooper search system

Every entry of `CounterControlPlan.rawCommands` is one bounded search in the
sense of Hooper's Basic Lemma.  This file packages those searches into the
proof-neutral `SearchSystem` interface.  Its launched-frame predicate retains
the original search gap, while its boundary predicate is the exact state and
tape obtained after a nested computation has erased itself and dispatched on
its saved return tag.

The generated controller itself discharges the direct, launch, and unwind
laws.  Forward and converse users need supply only the respective nested-core
growth or termination property.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlSearchSystem

open Turing
open BoundedMarkerProgram CounterControlPlan

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- One search identity for every raw command in the compiled controller. -/
abbrev Search := Fin rawCommands.length

/-- Concrete command selected by a search identity. -/
def command (base : Nat) (c : Nat.Partrec.Code) (search : Search) :
    Command numTags :=
  compileCommand base c search

/-- Concrete entry-state offset selected by a search identity. -/
def commandOffset (base : Nat) (c : Nat.Partrec.Code) (search : Search) :
    FiniteTM0.State :=
  searchState base c (rawCommands.get search).address

/-- The saved outer tape really contains the target at the recorded finite
distance, beyond the controller's directly inspected prefix. -/
def FrameWellFormed (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search) : Prop :=
  SearchGap (fun symbol => symbol = blankSymbol)
      (command base c frame.saved).target.Matches frame.outer
      (command base c frame.saved).searchDirection frame.distance ∧
    NestingMachine.bound (CanonicalInitializer.radius c) < frame.distance

/-- Exact canonical configuration launched for a failed compiled search. -/
def NestedAt (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  FrameWellFormed base c frame ∧
    cfg = CounterControlNestingBridge.nestedCfg
      base c frame.saved frame.outer

/-- Exact restored configuration just before the command-local one-cell
resume transition. -/
def BoundaryAt (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  FrameWellFormed base c frame ∧
    cfg =
      ⟨resumeState (CanonicalInitializer.radius c)
          (commandOffset base c frame.saved),
        frame.outer⟩

/-- All compiled raw commands, with their heterogeneous targets and
directions, form one simultaneous search system. -/
def searchSystem (base : Nat) (c : Nat.Partrec.Code) :
    SearchSystem (Symbol numTags) FiniteTM0.State Search where
  machine := CounterControlNestingBridge.machine base c
  searchState := commandOffset base c
  successState := fun search =>
    foundState (CanonicalInitializer.radius c)
      (commandOffset base c search)
  direction := fun search => (command base c search).searchDirection
  radius := fun _ => NestingMachine.bound (CanonicalInitializer.radius c)
  isBlank := fun symbol => symbol = blankSymbol
  isMark := fun search => (command base c search).target.Matches
  nestedAt := NestedAt base c
  boundaryAt := BoundaryAt base c

/-! ## The three controller-local nesting laws -/

/-- A target in the directly inspected prefix reaches the exact found state
without changing the tape. -/
theorem direct (base : Nat) (c : Nat.Partrec.Code)
    {search : Search} {outer : FullTM0.Tape (Symbol numTags)}
    {distance : Nat}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (command base c search).target.Matches outer
      (command base c search).searchDirection distance)
    (hnear : distance ≤
      NestingMachine.bound (CanonicalInitializer.radius c)) :
    FullTM0.Reaches (searchSystem base c).machine
      ((searchSystem base c).startCfg search outer)
      ((searchSystem base c).successCfg search outer distance) := by
  simpa [searchSystem, SearchSystem.startCfg, SearchSystem.successCfg,
    command, commandOffset, CounterControlNestingBridge.machine,
    BoundedMarkerProgram.entryState] using
    (BoundedMarkerProgram.machine_reaches_found_native
      (coreTable base c)
      (CounterControlWellFormed.compileCommand_commandAt base c search)
      outer distance hgap hnear)

/-- A target beyond the direct prefix launches the exact canonical frame and
records the original outer search gap. -/
theorem launch (base : Nat) (c : Nat.Partrec.Code)
    {search : Search} {outer : FullTM0.Tape (Symbol numTags)}
    {distance : Nat}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (command base c search).target.Matches outer
      (command base c search).searchDirection distance)
    (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance) :
    ∃ cfg,
      FullTM0.Reaches (searchSystem base c).machine
        ((searchSystem base c).startCfg search outer) cfg ∧
      (searchSystem base c).nestedAt
        ⟨search, outer, distance⟩ cfg := by
  let cfg := CounterControlNestingBridge.nestedCfg base c search outer
  have hrun := CounterControlNestingBridge.machine_reaches_nested
    base c search outer distance (by simpa [command] using hgap) hfar
  refine ⟨cfg, ?_, ?_⟩
  · simpa [cfg, searchSystem, SearchSystem.startCfg, commandOffset,
      BoundedMarkerProgram.entryState] using hrun.1
  · exact ⟨⟨hgap, hfar⟩, rfl⟩

/-- Once cleanup has restored the saved outer tape and selected the original
command, the private resume rule advances one cell and restarts that search. -/
theorem unwind (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    {boundary : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hboundary : BoundaryAt base c frame boundary) :
    FullTM0.Reaches (searchSystem base c).machine boundary
      ((searchSystem base c).startCfg frame.saved
        (frame.outer.move
          ((searchSystem base c).direction frame.saved))) := by
  rcases hboundary with ⟨hframe, rfl⟩
  have hpositive : 0 < frame.distance := by
    exact lt_of_le_of_lt (Nat.zero_le _) hframe.2
  have hblank : frame.outer.read = blankSymbol := by
    simpa [FullTM0.Tape.read] using hframe.1.blank hpositive
  have hrun := BoundedMarkerProgram.machine_resume_reaches
    (coreTable base c)
    (CounterControlWellFormed.compileCommand_commandAt
      base c frame.saved)
    frame.outer hblank
  simpa [searchSystem, SearchSystem.startCfg, commandOffset, command,
    CounterControlNestingBridge.machine, BoundedMarkerProgram.entryState]
    using hrun

/-! ## Forward and converse nested-core obligations -/

/-- The sole semantic obligation left for the forward Basic Lemma. -/
def CoreGrows (base : Nat) (c : Nat.Partrec.Code)
    (CoreImmortal : Prop) : Prop :=
  ∀ {frame : Frame (Symbol numTags) Search}
      {cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State},
    CoreImmortal →
      (∀ j < frame.distance, (searchSystem base c).Solves j) →
      NestedAt base c frame cfg →
      ∃ boundary,
        FullTM0.Reaches (searchSystem base c).machine cfg boundary ∧
          BoundaryAt base c frame boundary

/-- The sole semantic obligation left for the converse Basic Lemma. -/
def CoreResolves (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ {frame : Frame (Symbol numTags) Search}
      {cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State},
    (∀ j < frame.distance, (searchSystem base c).Resolves j) →
      NestedAt base c frame cfg →
      (∃ boundary,
        FullTM0.Reaches (searchSystem base c).machine cfg boundary ∧
          BoundaryAt base c frame boundary) ∨
        FullTM0.HaltsFrom (searchSystem base c).machine cfg

/-- The generated controller reduces all four forward nesting laws to
`CoreGrows`. -/
def nestingLaws (base : Nat) (c : Nat.Partrec.Code)
    (CoreImmortal : Prop)
    (hgrows : CoreGrows base c CoreImmortal) :
    NestingLaws (searchSystem base c) CoreImmortal where
  direct := by
    intro search outer distance hgap hnear
    exact direct base c hgap hnear
  launch := by
    intro search outer distance hgap hfar
    exact launch base c hgap hfar
  grow := by
    intro frame cfg hcore hshort hnested
    exact hgrows hcore hshort hnested
  unwind := by
    intro frame boundary hboundary
    exact unwind base c hboundary

/-- The generated controller likewise reduces the converse nesting laws to
`CoreResolves`. -/
def converseNestingLaws (base : Nat) (c : Nat.Partrec.Code)
    (hcore : CoreResolves base c) :
    ConverseNestingLaws (searchSystem base c) where
  direct := by
    intro search outer distance hgap hnear
    exact direct base c hgap hnear
  launch := by
    intro search outer distance hgap hfar
    exact launch base c hgap hfar
  core := by
    intro frame cfg hshort hnested
    exact hcore hshort hnested
  unwind := by
    intro frame boundary hboundary
    exact unwind base c hboundary

/-- Concrete forward Basic Lemma for all compiled counter searches. -/
theorem solves_all (base : Nat) (c : Nat.Partrec.Code)
    (CoreImmortal : Prop) (hgrows : CoreGrows base c CoreImmortal)
    (hcore : CoreImmortal) :
    ∀ distance : Nat, (searchSystem base c).Solves distance :=
  (nestingLaws base c CoreImmortal hgrows).basicLemma hcore

/-- Concrete converse Basic Lemma for all compiled counter searches. -/
theorem resolves_all (base : Nat) (c : Nat.Partrec.Code)
    (hcore : CoreResolves base c) :
    ∀ distance : Nat, (searchSystem base c).Resolves distance :=
  (converseNestingLaws base c hcore).resolves

end

end CounterControlSearchSystem
end Hooper
end Kari
end LeanWang
