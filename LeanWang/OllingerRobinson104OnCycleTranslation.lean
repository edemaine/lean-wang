/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104OrientedRedBoardTranslations
import LeanWang.OllingerRobinson104RedShadeGraphBoards
import LeanWang.OllingerRobinson104RedShadeGraphTranslation

/-! Translation of quarter-coordinate ports on oriented red cycles. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace OnCycleTranslation

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphTranslation

set_option linter.unnecessarySeqFocus false in
/-- Translate a quarter-coordinate port together with the cycle's
component-coordinate rectangle. -/
theorem translate
    {west east south north offsetX offsetY : Nat} {port : Port}
    (onCycle : OnCycle west east south north port) :
    OnCycle (offsetX + west) (offsetX + east)
      (offsetY + south) (offsetY + north)
      (translatePort port (2 * offsetX) (2 * offsetY)) := by
  cases onCycle with
  | southWest qx hwest heast =>
      convert OnCycle.southWest
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetX + qx) (by simp [quarterWest] at *; omega)
        (by simp [quarterEast] at *; omega) using 1 <;>
        simp [translatePort, quarterSouth] <;> omega
  | southEast qx hwest heast =>
      convert OnCycle.southEast
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetX + qx) (by simp [quarterWest] at *; omega)
        (by simp [quarterEast] at *; omega) using 1 <;>
        simp [translatePort, quarterSouth] <;> omega
  | northWest qx hwest heast =>
      convert OnCycle.northWest
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetX + qx) (by simp [quarterWest] at *; omega)
        (by simp [quarterEast] at *; omega) using 1 <;>
        simp [translatePort, quarterNorth] <;> omega
  | northEast qx hwest heast =>
      convert OnCycle.northEast
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetX + qx) (by simp [quarterWest] at *; omega)
        (by simp [quarterEast] at *; omega) using 1 <;>
        simp [translatePort, quarterNorth] <;> omega
  | westSouth qy hsouth hnorth =>
      convert OnCycle.westSouth
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetY + qy) (by simp [quarterSouth] at *; omega)
        (by simp [quarterNorth] at *; omega) using 1 <;>
        simp [translatePort, quarterWest] <;> omega
  | westNorth qy hsouth hnorth =>
      convert OnCycle.westNorth
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetY + qy) (by simp [quarterSouth] at *; omega)
        (by simp [quarterNorth] at *; omega) using 1 <;>
        simp [translatePort, quarterWest] <;> omega
  | eastSouth qy hsouth hnorth =>
      convert OnCycle.eastSouth
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetY + qy) (by simp [quarterSouth] at *; omega)
        (by simp [quarterNorth] at *; omega) using 1 <;>
        simp [translatePort, quarterEast] <;> omega
  | eastNorth qy hsouth hnorth =>
      convert OnCycle.eastNorth
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetY + qy) (by simp [quarterSouth] at *; omega)
        (by simp [quarterNorth] at *; omega) using 1 <;>
        simp [translatePort, quarterEast] <;> omega

end OnCycleTranslation
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
