/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlLooseFrameMortality

/-!
# Unconditional resolution of loose finite counter frames

An abstract counter run is either mortal or immortal.  Mortality already
resolves a loose frame by following the finite abstract trace.  On an immortal
run, the global source cycle laws force the clock past the fixed outer-frame
distance.  This contradicts the strict geometric bound carried by any
surviving `LooseLogical`, so the concrete run must already have restored its
saved search or halted.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlLooseFrameMortality

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- An immortal abstract counter run cannot remain forever inside one finite
loose frame: unbounded clock growth forces either boundary restoration or a
concrete halt. -/
theorem boundary_or_halts_of_abstract_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code) (frame : LooseFrame base c)
    {start : CounterMachine.Cfg}
    (himmortal : Dynamics.ImmortalFrom
      (CounterMachine.step GlobalSourceProgram.program) start)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LooseLogical base c frame start concrete) :
    ReachesBoundary base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases GlobalSourceLiveness.cycleLaws
      |>.exists_reachable_logical_clock_ge_of_immortalFrom
        himmortal frame.outerDistance with
    ⟨finish, hreach, _hfinishLogical, hclock⟩
  rcases reaches_loose_or_boundary_or_halts base c frame hreach hlogical with
    hfinish | hboundary | hhalts
  · rcases hfinish with
      ⟨_finishConcrete, _hfinishReach, hfinishLoose⟩
    rcases hfinishLoose with
      ⟨hcore, _tape, _backed, _concreteEq, _stateLt⟩
    have hclockEnd := clock_lt_layoutEnd finish.registers
    omega
  · exact Or.inl hboundary
  · exact Or.inr hhalts

/-- Every loose logical frame, from an arbitrary abstract configuration,
eventually restores its saved outer search or reaches a concrete halt. -/
theorem boundary_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (frame : LooseFrame base c)
    {start : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LooseLogical base c frame start concrete) :
    ReachesBoundary base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases CounterLiveness.haltsFrom_or_immortalFrom
      GlobalSourceProgram.program start with hhalts | himmortal
  · exact boundary_or_halts_of_abstract_haltsFrom base c frame
      hhalts hlogical
  · exact boundary_or_halts_of_abstract_immortalFrom base c frame
      himmortal hlogical

end

end CounterControlLooseFrameMortality
end Hooper
end Kari
end LeanWang
