/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeGrid
import LeanWang.OllingerRobinson104RedShadeInnerBoards
import Mathlib.Tactic.IntervalCases

/-!
The first free row and column in Robinson's two-level recurrence.

The center lines are not free for an arbitrary shade assignment.  They are
free when the surrounding canonical board is light and the shade grid obeys
the local matching rules: every possible perpendicular center segment reaches
the south or west side of that board, where the crossing rule forces it dark.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineBase

open OrientedRedCycles OrientedRedBoardTranslations RedCycles RedShadeCycles
  RedShadePaths RefinementTranslation ShadedFreeGrid
  ShadedFreeLineTranslation ShadedPlaneSignalGrid Signals.FreeCellLocal

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
set_option linter.flexible false in
theorem centerVertical_reaches_south
    (grid : Nat → Nat → Index) {quarterX : Nat}
    (hwest : 9 < quarterX) (heast : quarterX < 24)
    (hcenter : Signals.verticalInterior?
      (componentAt (iterateRefine 4 grid) quarterX 16)
      (quadrantAt quarterX 16) ≠ none) :
    ∀ quarterY, 9 ≤ quarterY → quarterY < 16 →
      RedShades.hasVertical
        (componentAt (iterateRefine 4 grid) quarterX quarterY)
        (quadrantAt quarterX quarterY) = true := by
  intro quarterY hsouth hnorth
  interval_cases quarterX <;> interval_cases quarterY <;>
    simp [componentAt, quadrantAt, iterateRefine, refineIndexGrid,
      parityOffset, Signals.verticalInterior?, RedShades.hasVertical] at hcenter ⊢
  all_goals
    generalize grid 0 0 = parent at hcenter ⊢
    revert parent
    native_decide

set_option linter.style.nativeDecide false in
set_option linter.flexible false in
theorem centerHorizontal_reaches_west
    (grid : Nat → Nat → Index) {quarterY : Nat}
    (hsouth : 9 < quarterY) (hnorth : quarterY < 24)
    (hcenter : Signals.horizontalInterior?
      (componentAt (iterateRefine 4 grid) 16 quarterY)
      (quadrantAt 16 quarterY) ≠ none) :
    ∀ quarterX, 9 ≤ quarterX → quarterX < 16 →
      RedShades.hasHorizontal
        (componentAt (iterateRefine 4 grid) quarterX quarterY)
        (quadrantAt quarterX quarterY) = true := by
  intro quarterX hwest heast
  interval_cases quarterY <;> interval_cases quarterX <;>
    simp [componentAt, quadrantAt, iterateRefine, refineIndexGrid,
      parityOffset, Signals.horizontalInterior?, RedShades.hasHorizontal]
      at hcenter ⊢
  all_goals
    generalize grid 0 0 = parent at hcenter ⊢
    revert parent
    native_decide

theorem centerRow_free_of_light
    (grid : Nat → Nat → Index)
    {shadeGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 4 grid) shadeGrid)
    (shaded : CycleShade shadeGrid 4 12 4 12 .light) :
    IsFreeRow (iterateRefine 4 grid) shadeGrid 4 12 16 := by
  intro quarterX hwest heast
  have hwest' : 9 < quarterX := by
    simpa [quarterWest] using hwest
  have heast' : quarterX < 24 := by
    simpa [quarterEast] using heast
  by_cases hnone : Signals.verticalInterior?
      (componentAt (iterateRefine 4 grid) quarterX 16)
      (quadrantAt quarterX 16) = none
  · exact ShadedSignals.selectedVerticalFor_of_none _ hnone
  · let cycle := at_scale grid 2 0 0
    have hpath := centerVertical_reaches_south grid hwest' heast' hnone
    have hverticalStart := hpath 9 (by omega) (by omega)
    have hhorizontalStart := RedShadeCycles.CycleOn.south_path
      cycle hwest heast
    have hparent := shaded.south_at cycle valid hwest heast
    have hopposite := valid.crossing_opposite quarterX 9
      hhorizontalStart hverticalStart
    have hsouthPresent := valid.south_present quarterX 9 (by
      simp [RedShades.hasSouth, hverticalStart])
    have hsouthDark : (shadeGrid quarterX 9).south = some .dark := by
      cases hsouth : (shadeGrid quarterX 9).south with
      | none => simp [hsouth] at hsouthPresent
      | some shade =>
          cases shade with
          | light =>
              exact False.elim (hopposite (hparent.1.trans hsouth.symm))
          | dark => rfl
    have hnorthDark : (shadeGrid quarterX 9).north = some .dark :=
      (valid.vertical_eq quarterX 9 hverticalStart).symm.trans hsouthDark
    have hflow := vertical_shade_across
      (fun quarterY => shadeGrid quarterX quarterY) 9 6
      (fun i hi => valid.vmatch quarterX (9 + i))
      (fun i hi => valid.vertical_eq quarterX (9 + i + 1)
        (hpath (9 + i + 1) (by omega) (by omega)))
    have hcenterSouth : (shadeGrid quarterX 16).south = some .dark := by
      have hend : 9 + 6 + 1 = 16 := by omega
      rw [hend] at hflow
      exact hflow.symm.trans hnorthDark
    simp [ShadedSignals.selectedVerticalFor, ShadedSignals.verticalShade?,
      hcenterSouth]

theorem centerColumn_free_of_light
    (grid : Nat → Nat → Index)
    {shadeGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 4 grid) shadeGrid)
    (shaded : CycleShade shadeGrid 4 12 4 12 .light) :
    IsFreeColumn (iterateRefine 4 grid) shadeGrid 4 12 16 := by
  intro quarterY hsouth hnorth
  have hsouth' : 9 < quarterY := by
    simpa [quarterSouth] using hsouth
  have hnorth' : quarterY < 24 := by
    simpa [quarterNorth] using hnorth
  by_cases hnone : Signals.horizontalInterior?
      (componentAt (iterateRefine 4 grid) 16 quarterY)
      (quadrantAt 16 quarterY) = none
  · exact ShadedSignals.selectedHorizontalFor_of_none _ hnone
  · let cycle := at_scale grid 2 0 0
    have hpath := centerHorizontal_reaches_west grid hsouth' hnorth' hnone
    have hhorizontalStart := hpath 9 (by omega) (by omega)
    have hverticalStart := RedShadeCycles.CycleOn.west_path
      cycle hsouth hnorth
    have hparent := shaded.west_at cycle valid hsouth hnorth
    have hopposite := valid.crossing_opposite 9 quarterY
      hhorizontalStart hverticalStart
    have hwestPresent := valid.west_present 9 quarterY (by
      simp [RedShades.hasWest, hhorizontalStart])
    have hwestDark : (shadeGrid 9 quarterY).west = some .dark := by
      cases hwestShade : (shadeGrid 9 quarterY).west with
      | none => simp [hwestShade] at hwestPresent
      | some shade =>
          cases shade with
          | light =>
              exact False.elim (hopposite (hwestShade.trans hparent.1.symm))
          | dark => rfl
    have heastDark : (shadeGrid 9 quarterY).east = some .dark :=
      (valid.horizontal_eq 9 quarterY hhorizontalStart).symm.trans hwestDark
    have hflow := horizontal_shade_across
      (fun quarterX => shadeGrid quarterX quarterY) 9 6
      (fun i hi => valid.hmatch (9 + i) quarterY)
      (fun i hi => valid.horizontal_eq (9 + i + 1) quarterY
        (hpath (9 + i + 1) (by omega) (by omega)))
    have hcenterWest : (shadeGrid 16 quarterY).west = some .dark := by
      have hend : 9 + 6 + 1 = 16 := by omega
      rw [hend] at hflow
      exact hflow.symm.trans heastDark
    simp [ShadedSignals.selectedHorizontalFor,
      ShadedSignals.horizontalShade?, hcenterWest]

def centerFreeGrid
    (grid : Nat → Nat → Index)
    {shadeGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 4 grid) shadeGrid)
    (shaded : CycleShade shadeGrid 4 12 4 12 .light) :
    FreeGrid (iterateRefine 4 grid) shadeGrid 4 12 4 12 1 :=
  singleton (by simp [quarterWest]) (by simp [quarterEast])
    (by simp [quarterSouth]) (by simp [quarterNorth])
    (centerColumn_free_of_light grid valid shaded)
    (centerRow_free_of_light grid valid shaded)

def centerFreeGrid_at
    (grid : Nat → Nat → Index)
    {shadeGrid : Nat → Nat → RedShades.State}
    (blockX blockY : Nat)
    (valid : ValidShadeGrid (iterateRefine 4 grid) shadeGrid)
    (shaded : CycleShade shadeGrid
      (16 * blockX + 4) (16 * blockX + 12)
      (16 * blockY + 4) (16 * blockY + 12) .light) :
    FreeGrid (iterateRefine 4 grid) shadeGrid
      (16 * blockX + 4) (16 * blockX + 12)
      (16 * blockY + 4) (16 * blockY + 12) 1 := by
  have localValid := validShadeGrid_shift 4 grid valid blockX blockY
  have localShaded : CycleShade
      (shiftQuarterGrid shadeGrid (32 * blockX) (32 * blockY))
      4 12 4 12 .light := by
    simpa only [show 2 * (16 * blockX) = 32 * blockX by omega,
      show 2 * (16 * blockY) = 32 * blockY by omega] using
        (cycleShade_shift_iff shadeGrid (16 * blockX) (16 * blockY)
          4 12 4 12 .light).2 shaded
  have localGrid : FreeGrid
      (iterateRefine 4 (shiftGrid grid blockX blockY))
      (shiftQuarterGrid shadeGrid (32 * blockX) (32 * blockY))
      4 12 4 12 1 := by
    apply centerFreeGrid (shiftGrid grid blockX blockY) localValid localShaded
  simpa only [show 2 ^ 4 = 16 by norm_num,
    show 2 ^ (4 + 1) = 32 by norm_num] using localGrid.translate

end ShadedFreeLineBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
