/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedRedBoardTranslations

/-!
Corner half-scale boards in the translated Robinson hierarchy.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace TranslatedRedShadeCrossings

open OrientedRedBoardTranslations OrientedRedCycles PlaneRedBoards RedCycles

set_option maxRecDepth 20000

/-- A corner half-scale board, expressed in the same refined grid. -/
theorem cornerSmallCycle (grid : Nat → Nat → Index)
    {level : Nat} (hlevel : 1 ≤ level) (blockX blockY : Nat)
    (cornerX cornerY : Fin 2) :
    CycleOn (iterateRefine (level + 2) grid)
      (2 ^ (level - 1) * (4 * (2 * blockX + cornerX.val) + 1))
      (2 ^ (level - 1) * (4 * (2 * blockX + cornerX.val) + 3))
      (2 ^ (level - 1) * (4 * (2 * blockY + cornerY.val) + 1))
      (2 ^ (level - 1) * (4 * (2 * blockY + cornerY.val) + 3)) := by
  have cycle := at_scale (iterateRefine 1 grid) (level - 1)
    (2 * blockX + cornerX.val) (2 * blockY + cornerY.val)
  have hgrid :
      iterateRefine (level - 1 + 2) (iterateRefine 1 grid) =
        iterateRefine (level + 2) grid := by
    rw [iterateRefine_add]
    congr 1
    omega
  rw [hgrid] at cycle
  exact cycle


end TranslatedRedShadeCrossings
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
