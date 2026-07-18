/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlOpenStepLaw
import LeanWang.Kari.Hooper.GlobalSourceLiveness

/-!
# Mortality of every open logical counter core

The unconditional target-free instruction law simulates any finite abstract
counter trace.  If the abstract trace halts, so does its open-core
representation.  If it is immortal, the global program's cycle law reaches
logical configurations with arbitrarily large clock values; the uniform
large-clock theorem then forces a concrete halt.  Thus source mortality rules
out every open logical configuration, not only the designated canonical one.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlOpenMortality

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan
open CounterControlCanonicalOpenMortality CounterControlCoreFrame
open CounterControlTagFreeOpen

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Under source mortality, every target-free open logical representation of
an arbitrary abstract counter configuration reaches a concrete halt. -/
theorem haltsFrom_openLogical
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {growth : Turing.Dir} {abstract : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : OpenLogical base c growth abstract concrete) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      concrete := by
  let hlaw : OpenStepContinuesOrHalts base c :=
    CounterControlOpenStepLaw.openStepContinuesOrHalts (base := base) (c := c)
  rcases CounterLiveness.haltsFrom_or_immortalFrom
      GlobalSourceProgram.program abstract with hhalts | himmortal
  · exact haltsFrom_openLogical_of_abstract_haltsFrom
      base c hlaw hhalts hlogical
  · rcases CounterControlLargeClock.exists_bound_halts_logical_of_core_clock
        base c hmortal with ⟨bound, hlarge⟩
    rcases GlobalSourceLiveness.cycleLaws
        |>.exists_reachable_logical_clock_ge_of_immortalFrom
          himmortal (bound + 1) with
      ⟨finish, hreach, _hfinishLogical, hclock⟩
    rcases reaches_openLogical_or_halts base c hlaw hreach hlogical with
      hfinish | hhalts
    · rcases hfinish with
        ⟨finishConcrete, hconcreteReach, hfinishLogical⟩
      rcases hfinishLogical with ⟨T, hopen, rfl, hstate⟩
      apply FullTM0.HaltsFrom.of_reaches hconcreteReach
      exact hlarge growth finish T hstate hopen.toCoreRepresents (by omega)
    · exact hhalts

/-- Convenient concrete form: an arbitrary bounded logical state centered on
a valid open counter core halts under source mortality. -/
theorem haltsFrom_logical_of_coreOpen
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (abstract : CounterMachine.Cfg)
    (T : FullTM0.Tape (Symbol numTags))
    (hstate : abstract.state < logicalSpan)
    (hopen : CoreOpenRepresents abstract.registers growth T) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c growth abstract.state,
        atLogical growth T (layoutEnd abstract.registers)⟩ := by
  apply haltsFrom_openLogical base c hmortal
  exact ⟨T, hopen, rfl, hstate⟩

end


end CounterControlOpenMortality
end Hooper
end Kari
end LeanWang
