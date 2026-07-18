/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlSearchSystem
import LeanWang.Kari.Hooper.CounterControlCommandAt

/-!
# Applying Hooper search hypotheses to generated commands

The Basic Lemma speaks about a finite search index, whereas the operational
counter proofs naturally name a generated `RawCommand` and its membership
proof.  These small bridges select the command's unique enumeration tag and
specialize `Solves` or `Resolves` to the exact compiled entry and found-state
configurations.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlSearchExecution

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlCommandAt

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- A `Solves` hypothesis for the simultaneous search system executes any
named generated command on its exact genuine gap. -/
theorem reaches_found_of_solves
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hsolves : (CounterControlSearchSystem.searchSystem base c).Solves
      distance)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c raw.address, outer⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c raw.address),
        outer.moveN
          (compileRawCommand base c raw hraw).searchDirection distance⟩ := by
  have hrun := hsolves (rawTag raw hraw) outer (by
    simpa [CounterControlSearchSystem.searchSystem,
      CounterControlSearchSystem.command, compileRawCommand] using hgap)
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨searchState base c (rawCommands.get (rawTag raw hraw)).address, outer⟩
    ⟨foundState (CanonicalInitializer.radius c)
        (searchState base c (rawCommands.get (rawTag raw hraw)).address),
      outer.moveN (compileCommand base c (rawTag raw hraw)).searchDirection
        distance⟩ at hrun
  rw [rawCommands_get_rawTag raw hraw] at hrun
  simpa only [compileRawCommand] using hrun

/-- A `Resolves` hypothesis gives the corresponding exact success-or-halt
dichotomy for a named generated command. -/
theorem reaches_found_or_halts_of_resolves
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hresolves : (CounterControlSearchSystem.searchSystem base c).Resolves
      distance)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address, outer⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c raw.address),
          outer.moveN
            (compileRawCommand base c raw hraw).searchDirection distance⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address, outer⟩ := by
  have hrun := hresolves (rawTag raw hraw) outer (by
    simpa [CounterControlSearchSystem.searchSystem,
      CounterControlSearchSystem.command, compileRawCommand] using hgap)
  change (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c (rawCommands.get (rawTag raw hraw)).address, outer⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c (rawCommands.get (rawTag raw hraw)).address),
        outer.moveN (compileCommand base c (rawTag raw hraw)).searchDirection
          distance⟩ ∨
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      ⟨searchState base c (rawCommands.get (rawTag raw hraw)).address,
        outer⟩) at hrun
  rw [rawCommands_get_rawTag raw hraw] at hrun
  simpa only [compileRawCommand] using hrun

end


end CounterControlSearchExecution
end Hooper
end Kari
end LeanWang
