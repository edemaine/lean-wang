/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCommandContinuationMortality

/-!
# Exact normalization of immortal shared-return entries

The general controller-normalization API deliberately forgets the tape
relation at a shared return.  The global unnesting argument needs the exact
geometry: the recognized tag is cleared and the selected generated search
starts one cell in the return direction.  This file retains that information.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlReturnFrontier

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlArbitraryEntry
open CounterControlCommandAt

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- An immortal shared-return configuration recognizes one actual generated
raw command.  It clears that command's tag and reaches the exact search entry
one cell in the return direction. -/
theorem reaches_generated_search_of_immortal_return
    (base : Nat) (c : Nat.Partrec.Code) (direction : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c direction, T⟩) :
    ∃ (raw : RawCommand) (hraw : raw ∈ rawCommands),
      T.read = tagSymbol (rawTag raw hraw) ∧
        (compileRawCommand base c raw hraw).searchDirection = direction ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨controllerReturn base c direction, T⟩
          ⟨searchState base c raw.address,
            (T.write blankSymbol).move direction⟩ := by
  rcases return_step_or_haltsFrom base c direction T with
    hhalts | ⟨before, command, after, hlist, hdirection, hread, hstep⟩
  · exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c direction, T⟩).mp himmortal hhalts)
  · let radius := CanonicalInitializer.radius c
    let commandOffset := base + before.length * blockWidth radius
    have hat : CommandAt radius base commandOffset command
        (commands base c) := by
      rw [hlist]
      exact CounterControlControllerNormalization.commandAt_append
        radius base before command after
    rcases CounterControlCommandAtConverse.exists_raw_of_commandAt base c hat with
      ⟨raw, hraw, hcommand, hoffset⟩
    subst command
    have hone : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c direction, T⟩
        ⟨resumeState radius commandOffset, T.write blankSymbol⟩ :=
      Relation.ReflTransGen.single (by simpa [radius, commandOffset] using hstep)
    have hresume : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resumeState radius commandOffset, T.write blankSymbol⟩
        ⟨entryState radius commandOffset,
          (T.write blankSymbol).move
            (compileRawCommand base c raw hraw).searchDirection⟩ := by
      change FullTM0.Reaches
        (BoundedMarkerProgram.machine base radius (commands base c)
          (coreTable base c)) _ _
      exact machine_resume_reaches (coreTable base c) hat
        (T.write blankSymbol) (FullTM0.Tape.read_write blankSymbol T)
    refine ⟨raw, hraw, ?_, ?_, ?_⟩
    · simpa using hread
    · exact hdirection
    · have hboth := hone.trans hresume
      simpa [FullTM0.Reaches, StateTransition.Reaches, radius, commandOffset,
        entryState, hoffset, hdirection] using hboth

end

end CounterControlReturnFrontier
end Hooper
end Kari
end LeanWang
