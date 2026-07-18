/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.GlobalSourceLiveness
import LeanWang.Kari.Hooper.GlobalSourceSemantics
import LeanWang.Kari.Hooper.CounterControlStepGeometry

/-!
# Designated mortality of the global source program

The forward simulation supplies an immortal canonical counter computation
when the fixed evaluator does not halt.  This file records the complementary
finite-run statement: if fixed nonhalting fails, the same canonical counter
configuration reaches an actual terminal state of the compiled program.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace GlobalSourceMortality

open CounterMachine SourceProgram

noncomputable section

/-- Failure of fixed nonhalting produces a finite global-counter execution
from the designated encoding to a configuration with no outgoing rule. -/
theorem not_fixedNonhalting_haltsFrom {c : Nat.Partrec.Code}
    (h : ¬ DominoProblem.FixedNonhalting c) :
    CounterLiveness.HaltsFrom GlobalSourceProgram.program
      (GlobalSourceSemantics.canonicalCounterCfg c) := by
  have hmortal : ¬ Dynamics.ImmortalFrom SourceControl.registerStep
      (SourceRegisterSemantics.canonical c) := by
    intro himmortal
    exact h ((SourceRegisterSemantics.fixedNonhalting_iff_immortalFrom c).2
      himmortal)
  have hdom :
      (StateTransition.eval SourceControl.registerStep
        (SourceRegisterSemantics.canonical c)).Dom := by
    by_contra hnotdom
    exact hmortal
      ((Dynamics.not_eval_dom_iff_immortalFrom _ _).1 hnotdom)
  rcases Part.dom_iff_mem.mp hdom with ⟨terminal, hterminalMem⟩
  rcases StateTransition.mem_eval.mp hterminalMem with
    ⟨hsourceReach, hterminal⟩
  rcases Dynamics.exists_iterate_eq_some_of_reaches hsourceReach with
    ⟨steps, hsteps⟩
  let terminalCounter : CounterMachine.Cfg :=
    ⟨controlCode terminal.state terminal.tape.head,
      logicalRegisters terminal.tape steps⟩
  refine ⟨terminalCounter, ?_, ?_⟩
  · simpa [terminalCounter, GlobalSourceSemantics.canonicalCounterCfg] using
      (GlobalSourceProgram.iterate_registerStep_reaches steps hsteps 0)
  · simpa [terminalCounter] using
      (GlobalSourceLiveness.step_logical_eq_none_of_registerStep_none
        terminal steps hterminal)

/-! ## A uniform finite layout bound -/

/-- The mortal canonical computation has an exact finite runtime ending at a
genuine terminal counter configuration. -/
theorem not_fixedNonhalting_exists_terminal_iterate
    {c : Nat.Partrec.Code} (h : ¬ DominoProblem.FixedNonhalting c) :
    ∃ (steps : Nat) (terminal : CounterMachine.Cfg),
      Dynamics.iterate (CounterMachine.step GlobalSourceProgram.program)
          steps (GlobalSourceSemantics.canonicalCounterCfg c) =
        some terminal ∧
      CounterMachine.step GlobalSourceProgram.program terminal = none := by
  rcases not_fixedNonhalting_haltsFrom h with
    ⟨terminal, hreach, hterminal⟩
  rcases Dynamics.exists_iterate_eq_some_of_reaches hreach with
    ⟨steps, hiterate⟩
  exact ⟨steps, terminal, hiterate, hterminal⟩

/-- Every configuration occurring no later than the terminal runtime fits
strictly inside the canonical initial layout plus `steps + 1`.  This is the
single large-frame bound used in the arbitrary-entry converse. -/
theorem prefix_layoutEnd_lt_terminalBound
    {c : Nat.Partrec.Code} {steps k : Nat}
    {terminal current : CounterMachine.Cfg}
    (_hterminal : Dynamics.iterate
      (CounterMachine.step GlobalSourceProgram.program) steps
      (GlobalSourceSemantics.canonicalCounterCfg c) = some terminal)
    (hk : k ≤ steps)
    (hcurrent : Dynamics.iterate
      (CounterMachine.step GlobalSourceProgram.program) k
      (GlobalSourceSemantics.canonicalCounterCfg c) = some current) :
    FramedMarkerTape.layoutEnd current.registers <
      FramedMarkerTape.layoutEnd
          (GlobalSourceSemantics.canonicalCounterCfg c).registers +
        steps + 1 := by
  have hbound :=
    CounterControlStepGeometry.layoutEnd_le_add_of_iterate k hcurrent
  omega

end

end GlobalSourceMortality
end Hooper
end Kari
end LeanWang
