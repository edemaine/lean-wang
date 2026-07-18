/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.GlobalSourceLiveness
import LeanWang.Kari.Hooper.GlobalSourceSemantics

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

end

end GlobalSourceMortality
end Hooper
end Kari
end LeanWang
