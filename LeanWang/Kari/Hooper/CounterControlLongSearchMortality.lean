/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlFiniteConverse
import LeanWang.Kari.Hooper.CounterControlRoomResolution

/-!
# Mortality of sufficiently long compiled searches

When the designated source computation is mortal, the room-resolution
theorem supplies a uniform distance beyond which a launched canonical core
halts.  The converse Basic Lemma supplies the shorter-search hypotheses
required by that theorem.  Consequently every genuine compiled search whose
matching target is sufficiently far away halts from its search entry.

This statement deliberately assumes a genuine finite matching search gap.
It makes no claim about a blank ray or a nearer nonmatching symbol; those are
separate obligations in the arbitrary-entry converse.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlLongSearchMortality

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlSearchSystem CounterControlSearchResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- If the designated source computation is mortal, one uniform bound makes
every genuine compiled search halt whenever its matching target lies beyond
that bound. -/
theorem exists_bound_halts_search
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    ∃ bound : Nat,
      ∀ {search : Search}
          {outer : FullTM0.Tape (Symbol numTags)} {distance : Nat},
        bound < distance →
        SearchGap (fun symbol => symbol = blankSymbol)
          (command base c search).target.Matches outer
          (command base c search).searchDirection distance →
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ((searchSystem base c).startCfg search outer) := by
  rcases CounterControlRoomResolution.exists_bound_halts_nested
      base c hmortal with ⟨coreBound, hcore⟩
  let searchBound := NestingMachine.bound (CanonicalInitializer.radius c)
  refine ⟨max coreBound searchBound, ?_⟩
  intro search outer distance hlarge hgap
  have hfar : searchBound < distance :=
    (Nat.le_max_right coreBound searchBound).trans_lt hlarge
  rcases CounterControlSearchSystem.launch base c hgap hfar with
    ⟨nested, hlaunch, hnested⟩
  apply FullTM0.HaltsFrom.of_reaches hlaunch
  apply hcore (frame := ⟨search, outer, distance⟩) (concrete := nested)
  · exact (Nat.le_max_left coreBound searchBound).trans_lt hlarge
  · intro j _hj
    exact CounterControlFiniteConverse.resolves_all base c j
  · exact hnested

end

end CounterControlLongSearchMortality
end Hooper
end Kari
end LeanWang
