/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlLargeClock
import LeanWang.Kari.Hooper.CounterControlOpenSimulation
import LeanWang.Kari.Hooper.CounterControlTagFreeOpen
import LeanWang.Kari.Hooper.FullTM0Locality

/-!
# Mortality interfaces for the canonical open counter core

The canonical top-level computation is represented by five counter
boundaries followed by an infinite blank runway.  Finite framed
approximations replace the blank ray by a matching target at a remote
coordinate.  Locality relates a computation of runtime `n` to an
approximation whose target is more than `n` cells away, but it does **not**
permit choosing the target first and its (possibly larger) runtime
afterwards.

This file records that distinction explicitly.  First, it proves that the
open configuration halts exactly when one finite approximation halts within
its own agreement radius.  It also proves that source mortality makes all
sufficiently remote approximations halt; the missing inequality between
runtime and radius is deliberately not inferred.

The second interface isolates an alternative, operational route.  An open
logical frame retains only the exact tag-free counter core and its infinite
blank runway.  A one-instruction resolution law for these frames lifts over
the already formalized mortal abstract trace.  The large-clock theorem
discharges this law automatically above one uniform clock bound, reducing
the remaining target-free work to bounded clocks.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCanonicalOpenMortality

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlCoreFrame
open CounterControlTagFreeOpen
open CounterControlOpenSimulation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Exact halting-time bookkeeping -/

/-- Reachability-based full-tape halting is equivalent to halting at one
exact finite runtime. -/
theorem haltsFrom_iff_exists_haltsAt
    {Gamma Lambda : Type*} [Inhabited Gamma] [Inhabited Lambda]
    (M : Turing.TM0.Machine Gamma Lambda)
    (start : FullTM0.Cfg Gamma Lambda) :
    FullTM0.HaltsFrom M start ↔
      ∃ runtime, FullTM0.HaltsAt M start runtime := by
  constructor
  · rintro ⟨terminal, hreach, hterminal⟩
    rcases Dynamics.exists_iterate_eq_some_of_reaches hreach with
      ⟨runtime, hrun⟩
    exact ⟨runtime, terminal, hrun, hterminal⟩
  · rintro ⟨runtime, terminal, hrun, hterminal⟩
    exact ⟨terminal, Dynamics.reaches_of_iterate_eq_some hrun, hterminal⟩

/-- The finite approximation and the canonical open configuration agree as
full configurations throughout the radius used to construct it. -/
theorem approximation_cfg_agree (base : Nat) (c : Nat.Partrec.Code)
    (depth : Nat) :
    FullTM0.Cfg.Agree depth (approximationCfg base c depth)
      (canonicalOpenCfg base c) := by
  constructor
  · rfl
  · simpa [FullTM0.Tape.Agree, AgreesWithin] using
      approximation_agrees_open base c depth

/-- **Diagonal finite-approximation criterion.**  The canonical blank-ray
configuration halts iff some remote finite approximation halts no later than
the radius on which that approximation agrees with the blank ray.

The bound `runtime ≤ depth` is essential.  Merely knowing that every finite
approximation eventually halts is not a compactness argument for mortality
of the limit configuration. -/
theorem canonicalOpen_halts_iff_exists_approximation_haltsWithin
    (base : Nat) (c : Nat.Partrec.Code) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        (canonicalOpenCfg base c) ↔
      ∃ depth,
        FullTM0.HaltsWithin (CounterControlNestingBridge.machine base c)
          (approximationCfg base c depth) depth := by
  let M := CounterControlNestingBridge.machine base c
  constructor
  · intro hopen
    rcases (haltsFrom_iff_exists_haltsAt M
      (canonicalOpenCfg base c)).1 hopen with ⟨runtime, hruntime⟩
    refine ⟨runtime, runtime, Nat.le_refl runtime, ?_⟩
    exact (FullTM0.haltsAt_iff_of_agree M runtime
      (approximation_cfg_agree base c runtime)).2 hruntime
  · rintro ⟨depth, hfinite⟩
    have hopenWithin : FullTM0.HaltsWithin M
        (canonicalOpenCfg base c) depth :=
      (FullTM0.haltsWithin_iff_of_agree M depth
        (approximation_cfg_agree base c depth)).1 hfinite
    rcases hopenWithin with ⟨runtime, _hruntime, hopen⟩
    exact (haltsFrom_iff_exists_haltsAt M
      (canonicalOpenCfg base c)).2 ⟨runtime, hopen⟩

/-- Equivalent eventual form of the diagonal criterion.  Once the open
configuration halts at runtime `r`, every approximation of depth at least
`r` has the same halting trace within its own depth. -/
theorem canonicalOpen_halts_iff_approximations_eventually_haltWithin_depth
    (base : Nat) (c : Nat.Partrec.Code) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        (canonicalOpenCfg base c) ↔
      ∃ depthBound : Nat, ∀ depth,
        depthBound ≤ depth →
          FullTM0.HaltsWithin (CounterControlNestingBridge.machine base c)
            (approximationCfg base c depth) depth := by
  let M := CounterControlNestingBridge.machine base c
  constructor
  · intro hopen
    rcases (haltsFrom_iff_exists_haltsAt M
      (canonicalOpenCfg base c)).1 hopen with ⟨runtime, hruntime⟩
    refine ⟨runtime, ?_⟩
    intro depth hdepth
    refine ⟨runtime, hdepth, ?_⟩
    have hagree := (approximation_cfg_agree base c depth).mono hdepth
    exact (FullTM0.haltsAt_iff_of_agree M runtime hagree).2 hruntime
  · rintro ⟨depthBound, hfinite⟩
    apply (canonicalOpen_halts_iff_exists_approximation_haltsWithin
      base c).2
    exact ⟨depthBound, hfinite depthBound (Nat.le_refl depthBound)⟩

/-! ## What finite framed mortality supplies -/

/-- If the designated source computation is mortal, every sufficiently deep
finite approximation halts.  This statement intentionally contains no
runtime bound in terms of `depth`. -/
theorem not_fixedNonhalting_approximations_eventually_halt
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    ∃ depthBound : Nat, ∀ depth,
      depthBound < depth →
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          (approximationCfg base c depth) := by
  rcases CounterControlRoomResolution.exists_bound_halts_nested
      base c hmortal with ⟨frameBound, hframe⟩
  refine ⟨frameBound, ?_⟩
  intro depth hdepth
  apply hframe (frame := approximationFrame base c depth)
    (concrete := approximationCfg base c depth)
  · change frameBound < approximationDistance c depth
    unfold approximationDistance
    omega
  · intro distance _hdistance
    exact CounterControlFiniteConverse.resolves_all base c distance
  · exact approximation_nestedAt base c depth

/-- A uniform eventual runtime bound is sufficient to close the locality
argument.  This is a safe non-circular replacement for the invalid move of
choosing a remote target and only afterwards assuming it lies beyond that
target's halting time. -/
theorem canonicalOpen_halts_of_eventually_uniform_approximation_runtime
    (base : Nat) (c : Nat.Partrec.Code)
    (huniform : ∃ depthBound runtimeBound : Nat, ∀ depth,
      depthBound < depth →
        FullTM0.HaltsWithin (CounterControlNestingBridge.machine base c)
          (approximationCfg base c depth) runtimeBound) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      (canonicalOpenCfg base c) := by
  rcases huniform with ⟨depthBound, runtimeBound, huniform⟩
  let depth := max depthBound runtimeBound + 1
  have hdepthBound : depthBound < depth := by
    dsimp [depth]
    omega
  have hruntimeBound : runtimeBound ≤ depth := by
    dsimp [depth]
    omega
  rcases huniform depth hdepthBound with
    ⟨runtime, hruntime, hhalts⟩
  apply (canonicalOpen_halts_iff_exists_approximation_haltsWithin
    base c).2
  exact ⟨depth, runtime, hruntime.trans hruntimeBound, hhalts⟩

/-! ## Target-free logical frames -/

/-- A logical controller configuration backed only by a five-boundary core
and an infinite blank runway.  No return tag and no outer target are part of
this invariant. -/
inductive OpenLogical (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (abstract : CounterMachine.Cfg)
    (concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop where
  | intro
      (tape : FullTM0.Tape (Symbol numTags))
      (represents : CoreOpenRepresents abstract.registers growth tape)
      (concrete_eq : concrete =
        ⟨logicalState base c growth abstract.state,
          atLogical growth tape (layoutEnd abstract.registers)⟩)
      (state_lt : abstract.state < logicalSpan)

/-- One-step semantics needed on a target-free open logical frame.  A
defined abstract instruction must either reach its exact next open logical
frame or expose a concrete halt. -/
def OpenStepContinuesOrHalts (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ {growth : Turing.Dir} {current next : CounterMachine.Cfg}
      {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State},
    CounterMachine.step GlobalSourceProgram.program current = some next →
    OpenLogical base c growth current concrete →
      (∃ nextConcrete,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          concrete nextConcrete ∧
        OpenLogical base c growth next nextConcrete) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete

/-- The fragment of target-free one-step semantics at clocks bounded by
`bound`. -/
def BoundedOpenStepContinuesOrHalts
    (base : Nat) (c : Nat.Partrec.Code) (bound : Nat) : Prop :=
  ∀ {growth : Turing.Dir} {current next : CounterMachine.Cfg}
      {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State},
    current.registers.clock ≤ bound →
    CounterMachine.step GlobalSourceProgram.program current = some next →
    OpenLogical base c growth current concrete →
      (∃ nextConcrete,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          concrete nextConcrete ∧
        OpenLogical base c growth next nextConcrete) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete

/-- Target-free one-step semantics lifts over every finite abstract counter
trace. -/
theorem reaches_openLogical_or_halts
    (base : Nat) (c : Nat.Partrec.Code)
    (hlaw : OpenStepContinuesOrHalts base c)
    {growth : Turing.Dir} {start finish : CounterMachine.Cfg}
    (hreach : StateTransition.Reaches
      (CounterMachine.step GlobalSourceProgram.program) start finish)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : OpenLogical base c growth start concrete) :
    (∃ finishConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete finishConcrete ∧
      OpenLogical base c growth finish finishConcrete) ∨
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      concrete := by
  induction hreach generalizing concrete with
  | refl =>
      exact Or.inl ⟨concrete, Relation.ReflTransGen.refl, hlogical⟩
  | @tail current next hprefix hstep ih =>
      rcases ih hlogical with hcurrent | hhalts
      · rcases hcurrent with
          ⟨currentConcrete, hprefixConcrete, hcurrent⟩
        have hstep' : CounterMachine.step GlobalSourceProgram.program
            current = some next := by
          simpa using hstep
        rcases hlaw hstep' hcurrent with hnext | hhalts
        · rcases hnext with ⟨nextConcrete, hlastConcrete, hnext⟩
          exact Or.inl
            ⟨nextConcrete, hprefixConcrete.trans hlastConcrete, hnext⟩
        · exact Or.inr
            (FullTM0.HaltsFrom.of_reaches hprefixConcrete hhalts)
      · exact Or.inr hhalts

/-- A mortal abstract counter trace halts concretely from every target-free
open logical representation, provided the one-step interface is available. -/
theorem haltsFrom_openLogical_of_abstract_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (hlaw : OpenStepContinuesOrHalts base c)
    {growth : Turing.Dir} {start : CounterMachine.Cfg}
    (hhalts : CounterLiveness.HaltsFrom
      GlobalSourceProgram.program start)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : OpenLogical base c growth start concrete) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      concrete := by
  rcases hhalts with ⟨terminal, hterminalReach, hterminal⟩
  rcases reaches_openLogical_or_halts base c hlaw hterminalReach hlogical with
    hfinish | hhalts
  · rcases hfinish with
      ⟨finishConcrete, hfinishReach, hfinishLogical⟩
    rcases hfinishLogical with ⟨T, _hopen, rfl, hstate⟩
    apply FullTM0.HaltsFrom.of_reaches hfinishReach
    refine ⟨⟨logicalState base c growth terminal.state,
        atLogical growth T (layoutEnd terminal.registers)⟩,
      Relation.ReflTransGen.refl, ?_⟩
    exact CounterControlTerminalSemantics.machine_step_eq_none_of_counter_step_none
      base c growth terminal
        (atLogical growth T (layoutEnd terminal.registers))
      hstate hterminal
  · exact hhalts

/-- The designated blank-ray initializer is an open logical representation
of the canonical abstract counter configuration. -/
theorem canonicalOpen_openLogical (base : Nat) (c : Nat.Partrec.Code) :
    OpenLogical base c (rootGrowth base c)
      (GlobalSourceSemantics.canonicalCounterCfg c)
      (canonicalOpenCfg base c) := by
  let registers := CanonicalInitializer.registers c
  let growth := rootGrowth base c
  let T := CounterControlOpenFrame.openTape registers growth rootSearch
  have hopen : CoreOpenRepresents registers growth T :=
    CoreOpenRepresents.ofOpen
      (CounterControlOpenFrame.OpenRepresents.openTape_represents
        registers growth rootSearch)
  have hend : layoutEnd registers = CanonicalInitializer.span c := by
    simpa [registers, layoutEnd] using
      CanonicalInitializer.clockBoundary_registers c
  refine ⟨T, ?_, ?_,
    CounterControlAbstractTrace.canonicalCounterCfg_state_lt_logicalSpan c⟩
  · simpa [registers, growth, CanonicalInitializer.registers, numTags]
      using hopen
  · have hend' : layoutEnd
        (GlobalSourceSemantics.canonicalCounterCfg c).registers =
          CanonicalInitializer.span c := by
      simpa [registers, CanonicalInitializer.registers] using hend
    simp only [canonicalOpenCfg, canonicalEntry]
    rw [hend']

/-- The only new local ingredient needed for the genuine blank-ray endpoint
is `OpenStepContinuesOrHalts`; all abstract mortality and terminal-state
bookkeeping are already available. -/
theorem not_fixedNonhalting_canonicalOpen_halts_of_openStep
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : OpenStepContinuesOrHalts base c) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      (canonicalOpenCfg base c) := by
  apply haltsFrom_openLogical_of_abstract_haltsFrom base c hlaw
    (GlobalSourceMortality.not_fixedNonhalting_haltsFrom hmortal)
  exact canonicalOpen_openLogical base c

/-! ## Reduction to bounded clocks -/

/-- For a mortal designated source, the existing long-search/large-clock
theorem extends target-free one-step semantics from bounded clocks to all
clocks.  Above the bound, the current represented logical configuration
already halts, so no instruction simulation is needed. -/
theorem openStepContinuesOrHalts_of_bounded
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    ∃ bound : Nat,
      BoundedOpenStepContinuesOrHalts base c bound →
        OpenStepContinuesOrHalts base c := by
  rcases CounterControlLargeClock.exists_bound_halts_logical_of_core_clock
      base c hmortal with ⟨bound, hlarge⟩
  refine ⟨bound, ?_⟩
  intro hbounded growth current next concrete hstep hlogical
  by_cases hclock : bound < current.registers.clock
  · right
    rcases hlogical with ⟨T, hopen, rfl, hstate⟩
    exact hlarge growth current T hstate hopen.toCoreRepresents hclock
  · exact hbounded (Nat.le_of_not_gt hclock) hstep hlogical

/-- Consequently, for each mortal source code it is enough to establish the
target-free instruction law at one bounded set of clock values. -/
theorem exists_clockBound_canonicalOpen_halts_of_bounded_openStep
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    ∃ bound : Nat,
      BoundedOpenStepContinuesOrHalts base c bound →
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          (canonicalOpenCfg base c) := by
  rcases openStepContinuesOrHalts_of_bounded base c hmortal with
    ⟨bound, hextend⟩
  refine ⟨bound, ?_⟩
  intro hbounded
  exact not_fixedNonhalting_canonicalOpen_halts_of_openStep base c hmortal
    (hextend hbounded)

end

end CounterControlCanonicalOpenMortality
end Hooper
end Kari
end LeanWang
