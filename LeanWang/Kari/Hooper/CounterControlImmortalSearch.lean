/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitrarySearchMortality
import LeanWang.Kari.Hooper.CounterControlFiniteConverse
import LeanWang.Kari.Hooper.CounterControlSearchResolution

/-!
# Resolving reached searches on an immortal orbit

Source mortality rules out malformed and target-free search rays.  Hooper's
converse Basic Lemma resolves every genuine finite search.  This file joins
those facts for a generated preserving boundary command already reached on
an immortal orbit.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlImmortalSearch

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlCommandAt CounterControlSearchSystem
open CounterControlCanonicalOpenMortality

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- A reached generated preserving boundary search on an immortal orbit has
a genuine finite gap and reaches its advertised symbolic continuation. -/
theorem reaches_boundary_preserve_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : OpenStepContinuesOrHalts base c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      .preserve ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags))
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨searchState base c address, outer⟩) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary expected).Matches outer
        (orient address.growth direction) distance ∧
      FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
        ⟨resolve base c success,
          outer.moveN (orient address.growth direction) distance⟩ := by
  let raw : RawCommand :=
    .boundaryNavigation address expected direction success .preserve
  let search : Search := rawTag raw hraw
  have hsearchCfg : (searchSystem base c).startCfg search outer =
      ⟨searchState base c address, outer⟩ := by
    change (⟨CounterControlSearchSystem.commandOffset base c search, outer⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    unfold CounterControlSearchSystem.commandOffset
    rw [show rawCommands.get search = raw by
      exact rawCommands_get_rawTag raw hraw]
    rfl
  have hreachSearch : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ((searchSystem base c).startCfg search outer) := by
    rw [hsearchCfg]
    exact hreach
  rcases
      CounterControlArbitrarySearchMortality.gap_of_reachable_search_on_immortal_orbit
      base c hmortal hlaw himmortal hreachSearch with
    ⟨distance, hgap⟩
  have hcommand : CounterControlSearchSystem.command base c search =
      compileRawCommand base c raw hraw := by
    rfl
  rw [hcommand] at hgap
  have hgapRaw : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth direction) distance := by
    simpa [compileRawCommand_spec, compileRawAtTag, raw,
      Command.target, Command.searchDirection] using hgap
  have hshort : CounterControlSearchResolution.ShortResolves
      base c (distance + 1) := by
    intro shorter _hshorter
    exact CounterControlFiniteConverse.resolves_all base c shorter
  have hrun := CounterControlSearchResolution.machine_reaches_boundary_preserve_or_halts
      base c (distance + 1) hshort address expected direction success hraw
      outer distance (by omega) hgapRaw
  refine ⟨distance, hgapRaw, ?_⟩
  rcases hrun with hsuccess | hhalts
  · exact hreach.trans hsuccess
  · exfalso
    apply (FullTM0.HaltsFrom.immortalFrom_iff_not
      (CounterControlNestingBridge.machine base c) start).mp himmortal
    exact FullTM0.HaltsFrom.of_reaches hreach hhalts

end


end CounterControlImmortalSearch
end Hooper
end Kari
end LeanWang
