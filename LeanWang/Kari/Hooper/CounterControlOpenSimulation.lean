/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlFiniteForward
import LeanWang.Kari.Hooper.CounterControlOpenFrame

/-!
# The designated open counter computation

The top-level counter computation has no suspended outer search.  Its
canonical five-boundary core instead has an infinite blank runway.  This file
connects that open configuration to the already verified finite-frame
instruction semantics.

The key compactness argument is quantitative.  A finite frame whose target
lies beyond the first `n` head moves agrees with the open frame throughout
the radius-`n` light cone.  Meanwhile each simulated abstract instruction
contains a mandatory concrete transition, so `n` abstract instructions give
at least `n` concrete transitions.  Locality then transfers the first `n`
concrete transitions from the finite frame to the open one.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlOpenSimulation

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlFrameBacking CounterControlFrameSimulation
open CounterControlInstructionSemantics
open CounterControlOpenFrame CounterControlOpenFrame.OpenRepresents

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Finite-speed locality for unrestricted tapes -/

/-- Two head-relative tapes agree on the closed radius-`radius` interval. -/
def AgreesWithin {Gamma : Type*} (radius : Nat)
    (T U : FullTM0.Tape Gamma) : Prop :=
  ∀ position : Int, -(radius : Int) ≤ position →
    position ≤ radius → T position = U position

namespace AgreesWithin

variable {Gamma : Type*} {T U : FullTM0.Tape Gamma}

theorem mono {small large : Nat} (h : AgreesWithin large T U)
    (hle : small ≤ large) : AgreesWithin small T U := by
  intro position hlower hupper
  apply h position <;> omega

theorem read (h : AgreesWithin 0 T U) : T.read = U.read := by
  simpa [FullTM0.Tape.read] using h 0 (by omega) (by omega)

theorem move (direction : Turing.Dir) {radius : Nat}
    (h : AgreesWithin (radius + 1) T U) :
    AgreesWithin radius (T.move direction) (U.move direction) := by
  intro position hlower hupper
  cases direction <;> simp only [FullTM0.Tape.move_left_apply,
    FullTM0.Tape.move_right_apply] <;> apply h <;> omega

theorem write (written : Gamma) {radius : Nat}
    (h : AgreesWithin radius T U) :
    AgreesWithin radius (T.write written) (U.write written) := by
  intro position hlower hupper
  simp only [FullTM0.Tape.write_apply]
  by_cases hzero : position = 0
  · simp [hzero]
  · simp [hzero, h position hlower hupper]

end AgreesWithin

/-- One full-tape transition only consumes one cell of agreement radius. -/
theorem step_of_agreesWithin
    {Gamma Lambda : Type*} [Inhabited Gamma] [Inhabited Lambda]
    (M : Turing.TM0.Machine Gamma Lambda) {radius : Nat}
    {q : Lambda} {T U : FullTM0.Tape Gamma}
    (h : AgreesWithin (radius + 1) T U) :
    ∃ nextQ nextT nextU,
      FullTM0.step M ⟨q, T⟩ = some ⟨nextQ, nextT⟩ ↔
        FullTM0.step M ⟨q, U⟩ = some ⟨nextQ, nextU⟩ ∧
          AgreesWithin radius nextT nextU := by
  have hread : T.read = U.read :=
    (h.mono (by omega : 0 ≤ radius + 1)).read
  unfold FullTM0.step
  rw [hread]
  cases hmachine : M q U.read with
  | none => simp
  | some result =>
      rcases result with ⟨nextQ, action⟩
      cases action with
      | move direction =>
          refine ⟨nextQ, T.move direction, U.move direction, ?_⟩
          simp only [Option.map_some, true_and]
          exact ⟨fun _ => h.move direction, fun _ => trivial⟩
      | write written =>
          refine ⟨nextQ, T.write written, U.write written, ?_⟩
          simp only [Option.map_some, true_and]
          have hsmall := h.mono (by omega : radius ≤ radius + 1)
          exact ⟨fun _ => hsmall.write written, fun _ => trivial⟩

/-- Defined one-step executions transfer to a locally agreeing tape, with
the same control state and one less cell of agreement radius. -/
theorem step_some_of_agreesWithin
    {Gamma Lambda : Type*} [Inhabited Gamma] [Inhabited Lambda]
    (M : Turing.TM0.Machine Gamma Lambda) {radius : Nat}
    {q nextQ : Lambda} {T U nextT : FullTM0.Tape Gamma}
    (h : AgreesWithin (radius + 1) T U)
    (hstep : FullTM0.step M ⟨q, T⟩ = some ⟨nextQ, nextT⟩) :
    ∃ nextU,
      FullTM0.step M ⟨q, U⟩ = some ⟨nextQ, nextU⟩ ∧
        AgreesWithin radius nextT nextU := by
  have hread : T.read = U.read :=
    (h.mono (by omega : 0 ≤ radius + 1)).read
  unfold FullTM0.step at hstep ⊢
  rw [hread] at hstep
  simp only [FullTM0.Tape.read_eq] at hstep ⊢
  cases hmachine : M q U.read with
  | none =>
      rw [FullTM0.Tape.read_eq] at hmachine
      rw [hmachine] at hstep
      simp at hstep
  | some result =>
      rcases result with ⟨resultQ, action⟩
      rw [FullTM0.Tape.read_eq] at hmachine
      simp only [hmachine, Option.map_some] at hstep ⊢
      cases action with
      | move direction =>
          cases Option.some.inj hstep
          exact ⟨U.move direction, rfl, h.move direction⟩
      | write written =>
          cases Option.some.inj hstep
          have hsmall := h.mono (by omega : radius ≤ radius + 1)
          exact ⟨U.write written, rfl, hsmall.write written⟩

/-- A finite execution only observes its initial radius-`steps` light cone.
An additional `radius` cells of initial agreement remain at the endpoint. -/
theorem iterate_some_of_agreesWithin
    {Gamma Lambda : Type*} [Inhabited Gamma] [Inhabited Lambda]
    (M : Turing.TM0.Machine Gamma Lambda) (steps radius : Nat)
    {q finishQ : Lambda} {T U finishT : FullTM0.Tape Gamma}
    (h : AgreesWithin (steps + radius) T U)
    (hrun : Dynamics.iterate (FullTM0.step M) steps ⟨q, T⟩ =
      some ⟨finishQ, finishT⟩) :
    ∃ finishU,
      Dynamics.iterate (FullTM0.step M) steps ⟨q, U⟩ =
        some ⟨finishQ, finishU⟩ ∧
      AgreesWithin radius finishT finishU := by
  induction steps generalizing radius q finishQ T U finishT with
  | zero =>
      simp only [Dynamics.iterate_zero] at hrun ⊢
      cases Option.some.inj hrun
      exact ⟨U, rfl, by simpa using h⟩
  | succ steps ih =>
      rw [Dynamics.iterate_succ] at hrun
      cases hprefix : Dynamics.iterate (FullTM0.step M) steps ⟨q, T⟩ with
      | none => simp [hprefix] at hrun
      | some middle =>
          rcases middle with ⟨middleQ, middleT⟩
          have hlast : FullTM0.step M ⟨middleQ, middleT⟩ =
              some ⟨finishQ, finishT⟩ := by
            simpa [hprefix] using hrun
          have hinitial : AgreesWithin (steps + (radius + 1)) T U := by
            apply h.mono
            omega
          rcases ih (radius := radius + 1) hinitial hprefix with
            ⟨middleU, hprefixU, hmiddle⟩
          rcases step_some_of_agreesWithin M hmiddle hlast with
            ⟨finishU, hlastU, hfinish⟩
          refine ⟨finishU, ?_, hfinish⟩
          simp [Dynamics.iterate_succ, hprefixU, hlastU]

/-! ## Exact-time bookkeeping -/

theorem iterate_add {alpha : Type*} (step : alpha → Option alpha)
    (first second : Nat) (start : alpha) :
    Dynamics.iterate step (first + second) start =
      (Dynamics.iterate step first start).bind
        (Dynamics.iterate step second) := by
  induction second with
  | zero => simp
  | succ second ih =>
      rw [Nat.add_succ, Dynamics.iterate_succ, ih]
      cases Dynamics.iterate step first start <;>
        simp [Dynamics.iterate_succ]

theorem survives_of_le {alpha : Type*} {step : alpha → Option alpha}
    {start : alpha} {short long : Nat} (hle : short ≤ long)
    (hlong : Dynamics.Survives step start long) :
    Dynamics.Survives step start short := by
  induction long generalizing short start with
  | zero =>
      have hshort : short = 0 := Nat.eq_zero_of_le_zero hle
      subst short
      exact Dynamics.survives_zero step start
  | succ long ih =>
      by_cases htop : short = long + 1
      · subst short
        exact hlong
      · have hshort : short ≤ long := by omega
        rcases hlong with ⟨finish, hfinish⟩
        rw [Dynamics.iterate_succ] at hfinish
        cases hprefix : Dynamics.iterate step long start with
        | none => simp [hprefix] at hfinish
        | some middle => exact ih hshort ⟨middle, hprefix⟩

/-! ## A remote finite target -/

/-- The global controller contains at least one bounded command. -/
theorem numTags_pos : 0 < numTags := by
  have hstate :=
    CounterControlAbstractTrace.canonicalCounterCfg_state_mem_programStates
      (default : Nat.Partrec.Code)
  simp only [programStates, List.mem_flatMap] at hstate
  rcases hstate with ⟨rule, hrule, _hruleState⟩
  let raw : RawCommand :=
    .boundaryNavigation ⟨.right, rule.1, validationSearchBase⟩ 3 .left
      (directRef .right rule.1 validationDirectBase) .preserve
  have hraw : raw ∈ commandsForRule .right rule := by
    simp [raw, commandsForRule, validationCommands, routeCommandsAux,
      MarkerValidation.sweep, validationSearchBase, validationDirectBase]
  have hmem := command_mem_rawCommands_of_rule .right hrule hraw
  simpa only [numTags] using List.length_pos_of_mem hmem

/-- A fixed compiled command used only to supply the finite approximation's
outer target, direction, and return tag. -/
def rootSearch : Search := ⟨0, numTags_pos⟩

def rootCommand (base : Nat) (c : Nat.Partrec.Code) : Command numTags :=
  command base c rootSearch

def rootGrowth (base : Nat) (c : Nat.Partrec.Code) : Turing.Dir :=
  (rootCommand base c).searchDirection

/-- Choose one concrete symbol recognized by a target. -/
def targetWitness (fallback : Fin numTags) :
    Target numTags → Symbol numTags
  | .boundary label => boundarySymbol label
  | .anyTag => tagSymbol fallback

theorem targetWitness_matches (fallback : Fin numTags)
    (target : Target numTags) :
    target.Matches (targetWitness fallback target) := by
  cases target <;> simp [targetWitness, Target.Matches]

/-- All blank except for one chosen target at logical coordinate `distance`. -/
def remoteOuter (growth : Turing.Dir) (target : Target numTags)
    (fallback : Fin numTags) (distance : Nat) :
    FullTM0.Tape (Symbol numTags) :=
  fun position =>
    if position = physicalCoord growth distance then
      targetWitness fallback target
    else blankSymbol

theorem remoteOuter_searchGap (growth : Turing.Dir)
    (target : Target numTags) (fallback : Fin numTags) (distance : Nat) :
    SearchGap (fun symbol => symbol = blankSymbol) target.Matches
      (remoteOuter growth target fallback distance) growth distance := by
  constructor
  · intro position hposition
    simp only [remoteOuter]
    rw [if_neg (by
      intro heq
      rw [physicalCoord_nat] at heq
      cases growth <;>
        simp only [FullTM0.Tape.offset_left,
          FullTM0.Tape.offset_right] at heq <;> omega)]
  · simp only [remoteOuter, physicalCoord_nat, if_pos]
    exact targetWitness_matches fallback target

theorem remoteOuter_eq_blankTape_of_ne (growth : Turing.Dir)
    (target : Target numTags) (fallback : Fin numTags) (distance : Nat)
    {position : Int} (hne : position ≠ physicalCoord growth distance) :
    remoteOuter growth target fallback distance position =
      blankTape numTags position := by
  rw [physicalCoord_nat] at hne
  simp [remoteOuter, blankTape, hne]

private theorem install_eq_of_outer_eq_at
    (registers : Registers) (growth : Turing.Dir) (tag : Fin numTags)
    (outer : FullTM0.Tape (Symbol numTags)) {position : Int}
    (heq : outer position = blankTape numTags position) :
    install registers growth tag outer position =
      install registers growth tag (blankTape numTags) position := by
  cases growth <;>
    simp only [install, logicalTape, OrientedMarkerTape.orientTape,
      FiniteTM0Mirror.Tape.mirror_apply] <;>
    unfold logicalOverlay <;>
    split_ifs <;> simp_all

/-- Recentered finite and open installations agree until the remote target
can enter the head's light cone. -/
theorem install_remote_agreesWithin
    (registers : Registers) (growth : Turing.Dir) (tag : Fin numTags)
    (target : Target numTags) (distance origin radius : Nat)
    (hremote : origin + radius < distance) :
    AgreesWithin radius
      (atLogical growth
        (install registers growth tag
          (remoteOuter growth target tag distance)) origin)
      (atLogical growth
        (openTape registers growth tag) origin) := by
  intro position hlower hupper
  simp only [atLogical, FullTM0.Tape.moveN_apply, openTape]
  apply install_eq_of_outer_eq_at
  apply remoteOuter_eq_blankTape_of_ne
  rw [physicalCoord_nat]
  cases growth <;>
    simp only [FullTM0.Tape.offset_left,
      FullTM0.Tape.offset_right] at * <;> omega

/-! ## Canonical open and finite approximating configurations -/

def canonicalOpenCfg (base : Nat) (c : Nat.Partrec.Code) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  ⟨canonicalEntry base c (rootGrowth base c),
    atLogical (rootGrowth base c)
      (openTape (CanonicalInitializer.registers c) (rootGrowth base c)
        rootSearch)
      (CanonicalInitializer.span c)⟩

def approximationDistance (c : Nat.Partrec.Code) (depth : Nat) : Nat :=
  CanonicalInitializer.span c + depth +
    NestingMachine.bound (CanonicalInitializer.radius c) + 1

def approximationOuter (base : Nat) (c : Nat.Partrec.Code) (depth : Nat) :
    FullTM0.Tape (Symbol numTags) :=
  remoteOuter (rootGrowth base c) (rootCommand base c).target rootSearch
    (approximationDistance c depth)

def approximationFrame (base : Nat) (c : Nat.Partrec.Code) (depth : Nat) :
    Frame (Symbol numTags) Search :=
  ⟨rootSearch, approximationOuter base c depth,
    approximationDistance c depth⟩

def approximationCfg (base : Nat) (c : Nat.Partrec.Code) (depth : Nat) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  CounterControlNestingBridge.nestedCfg base c rootSearch
    (approximationOuter base c depth)

theorem approximation_nestedAt (base : Nat) (c : Nat.Partrec.Code)
    (depth : Nat) :
    NestedAt base c (approximationFrame base c depth)
      (approximationCfg base c depth) := by
  constructor
  · constructor
    · simpa [approximationFrame, approximationOuter, rootCommand,
        rootGrowth, command] using
        remoteOuter_searchGap (rootGrowth base c) (rootCommand base c).target
          rootSearch (approximationDistance c depth)
    · simp [approximationFrame, approximationDistance]
      omega
  · rfl

theorem approximation_logicalFrame (base : Nat) (c : Nat.Partrec.Code)
    (depth : Nat) :
    LogicalFrame base c (approximationFrame base c depth)
      (GlobalSourceSemantics.canonicalCounterCfg c)
      (approximationCfg base c depth) :=
  logicalFrame_of_nestedAt base c (approximation_nestedAt base c depth)

theorem approximation_agrees_open (base : Nat) (c : Nat.Partrec.Code)
    (depth : Nat) :
    AgreesWithin depth (approximationCfg base c depth).tape
      (canonicalOpenCfg base c).tape := by
  have hremote : CanonicalInitializer.span c + depth <
      approximationDistance c depth := by
    simp [approximationDistance]
    omega
  simpa [approximationCfg, CounterControlNestingBridge.nestedCfg,
    canonicalOpenCfg, approximationOuter, rootCommand, rootGrowth, command,
    FramedMarkerTape.initializeTape,
    CounterControlPlan.compileCommand_returnTag] using
    install_remote_agreesWithin (CanonicalInitializer.registers c)
      (rootGrowth base c) rootSearch (rootCommand base c).target
      (approximationDistance c depth) (CanonicalInitializer.span c) depth
      hremote

/-! ## Quantitative finite-frame instruction simulation -/

/-- A collision-free compiled instruction takes a positive number of
concrete transitions and reaches the exact successor logical frame.  This is
the quantitative refinement of `stepContinues_of_room`; positivity follows
from the mandatory validation-entry transition exposed by the instruction
semantics. -/
theorem step_runs_positive
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (hshort : ShortSearches base c frame.distance)
    {current next : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hstep : step GlobalSourceProgram.program current = some next)
    (hroom : layoutEnd next.registers < frame.distance)
    (hlogical : LogicalFrame base c frame current concrete) :
    ∃ runtime nextConcrete,
      0 < runtime ∧
      Dynamics.iterate
        (FullTM0.step (CounterControlNestingBridge.machine base c))
        runtime concrete = some nextConcrete ∧
      LogicalFrame base c frame next nextConcrete := by
  rcases hlogical with
    ⟨hcore, T, hback, rfl, _hstate, hframe⟩
  let spec := activeSpec base c frame current.registers hcore
  change BackedBy spec T frame.outer at hback
  have hrun := machine_reaches_abstractStep_solved base c current.state
    (spec := spec) hback
    (by
      simp [spec, activeSpec, frameGrowth,
        CounterControlSearchSystem.command])
    (by simpa [spec] using hstep)
    (by simpa [spec] using hshort)
  cases hrun with
  | logical hnextCore nextTape first hfirst hremaining hnextBack =>
      have hnextCore' : layoutEnd next.registers < frame.distance := by
        simpa [spec] using hnextCore
      have hnextBack' : BackedBy
          (activeSpec base c frame next.registers hnextCore')
          nextTape frame.outer := by
        simpa [spec, activeSpec, updateSpec] using hnextBack
      let nextConcrete := logicalCfg base c frame next nextTape
      have hnextFrame : LogicalFrame base c frame next nextConcrete := by
        exact ⟨hnextCore', nextTape, hnextBack', rfl,
          CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep,
          hframe⟩
      have hfirst' : FullTM0.step
          (CounterControlNestingBridge.machine base c)
          (logicalCfg base c frame current T) = some first := by
        simpa [logicalCfg, spec, activeSpec] using hfirst
      have hremaining' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) first nextConcrete := by
        simpa [nextConcrete, logicalCfg, spec, activeSpec] using hremaining
      rcases Dynamics.exists_iterate_eq_some_of_reaches hremaining' with
        ⟨tailRuntime, htail⟩
      refine ⟨1 + tailRuntime, nextConcrete, by omega, ?_, hnextFrame⟩
      rw [iterate_add]
      simp [Dynamics.iterate_succ, hfirst', htail]
  | boundary hcollision _first _hfirst _hremaining =>
      have hcollision' : layoutEnd next.registers = frame.distance := by
        simpa [spec] using hcollision.hitsTarget
      omega

/-- Exact abstract iteration lifts to an exact concrete iteration whose
runtime is at least the number of abstract instructions, provided the whole
abstract prefix fits before the finite target. -/
theorem iterate_runs_at_least
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (hshort : ShortSearches base c frame.distance)
    (steps : Nat) {start finish : CounterMachine.Cfg}
    (hrun : Dynamics.iterate (step GlobalSourceProgram.program)
      steps start = some finish)
    (hfits : layoutEnd start.registers + steps < frame.distance)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LogicalFrame base c frame start concrete) :
    ∃ runtime finishConcrete,
      steps ≤ runtime ∧
      Dynamics.iterate
        (FullTM0.step (CounterControlNestingBridge.machine base c))
        runtime concrete = some finishConcrete ∧
      LogicalFrame base c frame finish finishConcrete := by
  induction steps generalizing finish concrete with
  | zero =>
      simp only [Dynamics.iterate_zero] at hrun
      cases Option.some.inj hrun
      exact ⟨0, concrete, Nat.zero_le _, rfl, hlogical⟩
  | succ steps ih =>
      rw [Dynamics.iterate_succ] at hrun
      cases hprefix : Dynamics.iterate (step GlobalSourceProgram.program)
          steps start with
      | none => simp [hprefix] at hrun
      | some current =>
          have hlast : step GlobalSourceProgram.program current =
              some finish := by
            simpa [hprefix] using hrun
          have hprefixFits : layoutEnd start.registers + steps <
              frame.distance := by omega
          rcases ih hprefix hprefixFits hlogical with
            ⟨prefixRuntime, currentConcrete, hpRuntime, hpRun, hcurrent⟩
          have hcurrentBound :=
            CounterControlStepGeometry.layoutEnd_le_add_of_iterate
              steps hprefix
          have hfinishBound :=
            CounterControlStepGeometry.layoutEnd_next_le_add_one_of_step_eq_some
              hlast
          have hfinishRoom : layoutEnd finish.registers < frame.distance := by
            omega
          rcases step_runs_positive base c frame hshort hlast hfinishRoom
              hcurrent with
            ⟨lastRuntime, finishConcrete, hlPositive, hlRun, hfinish⟩
          refine ⟨prefixRuntime + lastRuntime, finishConcrete,
            by omega, ?_, hfinish⟩
          rw [iterate_add, hpRun]
          exact hlRun

/-! ## Designated open immortality -/

/-- Fixed nonhalting of the source machine gives an immortal execution of
the concrete controller on its canonical top-level open frame. -/
theorem fixedNonhalting_immortalFrom (base : Nat) (c : Nat.Partrec.Code) :
    DominoProblem.FixedNonhalting c →
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
        (canonicalOpenCfg base c) := by
  intro hnonhalting depth
  rcases GlobalSourceSemantics.fixedNonhalting_immortalFrom hnonhalting depth
      with ⟨finish, habstract⟩
  let frame := approximationFrame base c depth
  have hshort : ShortSearches base c frame.distance := by
    intro distance _hdistance
    exact CounterControlFiniteForward.solves_all base c hnonhalting distance
  have hcanonicalEnd : layoutEnd
      (GlobalSourceSemantics.canonicalCounterCfg c).registers =
        CanonicalInitializer.span c := by
    have hend : layoutEnd (CanonicalInitializer.registers c) =
        CanonicalInitializer.span c := by
      simpa [layoutEnd] using
        CanonicalInitializer.clockBoundary_registers c
    simpa [CanonicalInitializer.registers] using hend
  have hfits : layoutEnd
        (GlobalSourceSemantics.canonicalCounterCfg c).registers + depth <
      frame.distance := by
    rw [hcanonicalEnd]
    simp [frame, approximationFrame, approximationDistance]
    omega
  have hlogical : LogicalFrame base c frame
      (GlobalSourceSemantics.canonicalCounterCfg c)
      (approximationCfg base c depth) := by
    simpa [frame] using approximation_logicalFrame base c depth
  rcases iterate_runs_at_least base c frame hshort depth habstract hfits
      hlogical with
    ⟨runtime, finishConcrete, hruntime, hconcrete, _hfinishLogical⟩
  have hfiniteSurvives : Dynamics.Survives
      (FullTM0.step (CounterControlNestingBridge.machine base c))
      (approximationCfg base c depth) depth :=
    survives_of_le hruntime ⟨finishConcrete, hconcrete⟩
  rcases hfiniteSurvives with ⟨finiteFinish, hfiniteFinish⟩
  have hfiniteFinish' : Dynamics.iterate
      (FullTM0.step (CounterControlNestingBridge.machine base c)) depth
      ⟨(canonicalOpenCfg base c).q,
        (approximationCfg base c depth).tape⟩ = some finiteFinish := by
    simpa [canonicalOpenCfg, approximationCfg,
      CounterControlNestingBridge.nestedCfg, rootGrowth, rootCommand,
      CounterControlSearchSystem.command] using hfiniteFinish
  rcases finiteFinish with ⟨finishQ, finishTape⟩
  rcases iterate_some_of_agreesWithin
      (CounterControlNestingBridge.machine base c) depth 0
      (by simpa using approximation_agrees_open base c depth)
      hfiniteFinish' with
    ⟨openFinishTape, hopen, _hagrees⟩
  exact ⟨⟨finishQ, openFinishTape⟩, hopen⟩

end

end CounterControlOpenSimulation
end Hooper
end Kari
end LeanWang
