/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitrarySearchMortality
import LeanWang.Kari.Hooper.CounterControlOpenStepLaw

/-!
# Genuine gaps at immortal generated search entries

For a mortal source code, an immortal orbit cannot enter a generated search
on a target-free or malformed ray: the arbitrary-search mortality theorem
would make that exact entry halt.  This file packages that result directly in
terms of a generated `RawCommand`, hiding its enumeration tag and the
search-system conversion.

The source-mortality hypothesis is essential.  Without it, a target-free
search may launch a genuinely immortal source computation.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGeneratedSearchGap

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlCommandAt CounterControlSearchSystem

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- An exact generated raw-search entry on an immortal orbit has a genuine
finite blank-to-target gap.  The raw command's enumeration tag is entirely
internal to the proof. -/
theorem gap_of_reachable_search_on_immortal_orbit
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c raw.address, outer⟩) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (compileRawCommand base c raw hraw).target.Matches outer
        (compileRawCommand base c raw hraw).searchDirection distance := by
  let search : Search := rawTag raw hraw
  have hsearchCfg : (searchSystem base c).startCfg search outer =
      ⟨searchState base c raw.address, outer⟩ := by
    change (⟨CounterControlSearchSystem.commandOffset base c search, outer⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    unfold CounterControlSearchSystem.commandOffset
    rw [show rawCommands.get search = raw by
      exact rawCommands_get_rawTag raw hraw]
  have hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c raw.address, outer⟩
      ((searchSystem base c).startCfg search outer) := by
    rw [hsearchCfg]
    exact Relation.ReflTransGen.refl
  rcases
      CounterControlArbitrarySearchMortality.gap_of_reachable_search_on_immortal_orbit
        base c hmortal
        (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
        himmortal hreach with ⟨distance, hgap⟩
  have hcommand : command base c search =
      compileRawCommand base c raw hraw := by
    rfl
  rw [hcommand] at hgap
  exact ⟨distance, hgap⟩

/-- Constructor-specialized form for generated boundary navigation.  It
exposes the labelled target and physically oriented search direction without
mentioning command compilation. -/
theorem boundaryNavigation_gap_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (action : RawNavigationAction)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      action ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary expected).Matches outer
        (orient address.growth direction) distance := by
  let raw : RawCommand :=
    .boundaryNavigation address expected direction success action
  rcases gap_of_reachable_search_on_immortal_orbit base c hmortal raw hraw
      outer (by simpa [raw, RawCommand.address] using himmortal) with
    ⟨distance, hgap⟩
  refine ⟨distance, ?_⟩
  rw [compileRawCommand_spec] at hgap
  simpa [raw, compileRawAtTag, Command.target, Command.searchDirection,
    compileNavigationAction] using hgap

end

end CounterControlGeneratedSearchGap
end Hooper
end Kari
end LeanWang
