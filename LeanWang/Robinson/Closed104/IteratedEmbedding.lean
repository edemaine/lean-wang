/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.HierarchyEmbedding

/-!
Iterate the concrete hierarchy-coordinate embedding through arbitrary depth.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace HierarchyEmbedding

open ParentPlane Hierarchy RedCycles

theorem iterateRefine_refineIndexGrid (depth : Nat)
    (grid : Nat → Nat → Index) :
    iterateRefine depth (refineIndexGrid grid) =
      iterateRefine (depth + 1) grid := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change refineIndexGrid (iterateRefine depth (refineIndexGrid grid)) =
        refineIndexGrid (iterateRefine (depth + 1) grid)
      rw [ih]

/-- Fine-plane origin below a coarse coordinate after `depth` parent steps. -/
def descendOrigin {base : ValidPlane} (tower : Tower base)
    (baseLevel : Nat) : Nat → Int × Int → Int × Int
  | 0, coarseOrigin => coarseOrigin
  | depth + 1, coarseOrigin =>
      descendOrigin tower baseLevel depth
        (blockOrigin (tower.origin (baseLevel + depth)) coarseOrigin)

/-- Iterated refinement is realized contiguously in the actual fine plane. -/
theorem Tower.natGridAt_descendOrigin
    {base : ValidPlane} (tower : Tower base) :
    ∀ (depth baseLevel : Nat) (coarseOrigin : Int × Int),
      natGridAt (tower.plane baseLevel).tiling
          (descendOrigin tower baseLevel depth coarseOrigin) =
        iterateRefine depth
          (natGridAt (tower.plane (baseLevel + depth)).tiling coarseOrigin) := by
  intro depth
  induction depth with
  | zero =>
      intro baseLevel coarseOrigin
      rfl
  | succ depth ih =>
      intro baseLevel coarseOrigin
      let intermediateOrigin :=
        blockOrigin (tower.origin (baseLevel + depth)) coarseOrigin
      calc
        natGridAt (tower.plane baseLevel).tiling
            (descendOrigin tower baseLevel (depth + 1) coarseOrigin) =
            natGridAt (tower.plane baseLevel).tiling
              (descendOrigin tower baseLevel depth intermediateOrigin) := by
          rfl
        _ = iterateRefine depth
              (natGridAt (tower.plane (baseLevel + depth)).tiling
                intermediateOrigin) :=
          ih baseLevel intermediateOrigin
        _ = iterateRefine depth
              (refineIndexGrid
                (natGridAt (tower.plane ((baseLevel + depth) + 1)).tiling
                  coarseOrigin)) := by
          have hstep :=
            HierarchyEmbedding.natGridAt_refines
              (tower.children (baseLevel + depth)) coarseOrigin
          simpa only [intermediateOrigin] using
            congrArg (iterateRefine depth) hstep
        _ = iterateRefine (depth + 1)
              (natGridAt (tower.plane ((baseLevel + depth) + 1)).tiling
                coarseOrigin) :=
          iterateRefine_refineIndexGrid depth _
        _ = iterateRefine (depth + 1)
              (natGridAt (tower.plane (baseLevel + (depth + 1))).tiling
                coarseOrigin) := by
          have hindex : (baseLevel + depth) + 1 =
              baseLevel + (depth + 1) := by omega
          rw [hindex]

end HierarchyEmbedding
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
