/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineOddExtraBaseAudit

/-!
# Transported odd-extra base routes

The finite full-board audit is transported from canonical border states back
to every corrected parent tile.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineOddExtraStep

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
open RedShadeGraph RedShadeGraphTranslation RefinementTranslation
  Signals.FreeCellLocal BorderGeometry BorderCoverage
  SparseFreeLineOddExtraBaseAudit
set_option maxRecDepth 20000

theorem sameComponents_searchGrid_canonicalIndex (parent : Index) :
    SameComponents (searchGrid (BorderSubstitution.canonicalIndex parent))
      (searchGrid parent) := by
  have sameFine := sameComponents_fineLocalGrid_canonicalIndex .odd 0 parent
  intro x y
  rw [searchGrid, searchGrid, componentAt_iterateRefine_shift,
    componentAt_iterateRefine_shift]
  norm_num
  exact sameFine (16 + x) (16 + y)

theorem starts_canonicalIndex (parent : Index) :
    starts (BorderSubstitution.canonicalIndex parent) = starts parent := by
  have same := sameComponents_localGrid_canonicalIndex .odd 0 parent
  unfold starts candidates oldGrid
  rw [patternCandidates_congr same]

theorem route_of_canonicalIndex {parent : Index} {target : Port}
    (route : Route (BorderSubstitution.canonicalIndex parent) target) :
    Route parent target := by
  have same := sameComponents_searchGrid_canonicalIndex parent
  rcases route with ⟨start, hstart, path, targetLive⟩
  refine ⟨start, ?_, BoundedPath.congr_of_component_eq
    (fun x y _ _ => same x y) path, ?_⟩
  · rwa [starts_canonicalIndex] at hstart
  · rwa [portPresent_congr same target] at targetLive

theorem canonical_check (parent : Index) :
    check (BorderSubstitution.canonicalIndex parent) = true := by
  exact canonical_complete (BorderSubstitution.indexState parent)
    (BorderSubstitution.indexState_mem_states parent)

theorem auditedVerticalRoutes
    (parent : Index) (x : Nat) (hxLower : 2 ≤ x) (hxUpper : x < 32)
    (interior : Signals.verticalInterior?
      (componentAt (searchGrid parent) x 19) (quadrantAt x 19) ≠ none) :
    Route parent ⟨x, 19, .south⟩ ∨ Route parent ⟨x, 19, .north⟩ := by
  have same := sameComponents_searchGrid_canonicalIndex parent
  have canonicalInterior : Signals.verticalInterior?
      (componentAt (searchGrid (BorderSubstitution.canonicalIndex parent)) x 19)
      (quadrantAt x 19) ≠ none := by
    rw [same x 19]
    exact interior
  rcases (check_sound (canonical_check parent)).1 x hxLower hxUpper
      canonicalInterior with route | route
  · exact Or.inl (route_of_canonicalIndex route)
  · exact Or.inr (route_of_canonicalIndex route)

theorem auditedHorizontalRoutes
    (parent : Index) (y : Nat) (hyLower : 2 ≤ y) (hyUpper : y < 32)
    (interior : Signals.horizontalInterior?
      (componentAt (searchGrid parent) 19 y) (quadrantAt 19 y) ≠ none) :
    Route parent ⟨19, y, .west⟩ ∨ Route parent ⟨19, y, .east⟩ := by
  have same := sameComponents_searchGrid_canonicalIndex parent
  have canonicalInterior : Signals.horizontalInterior?
      (componentAt (searchGrid (BorderSubstitution.canonicalIndex parent)) 19 y)
      (quadrantAt 19 y) ≠ none := by
    rw [same 19 y]
    exact interior
  rcases (check_sound (canonical_check parent)).2 y hyLower hyUpper
      canonicalInterior with route | route
  · exact Or.inl (route_of_canonicalIndex route)
  · exact Or.inr (route_of_canonicalIndex route)


end SparseFreeLineOddExtraStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
