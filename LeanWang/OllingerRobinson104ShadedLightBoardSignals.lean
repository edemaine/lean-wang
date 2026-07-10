/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedPlaneSignalGrid
import LeanWang.OllingerRobinson104SignalCorridors

/-!
Obstruction-signal endpoint rules along every strict side quarter of a
uniformly light Robinson board.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedPlaneSignalGrid

open OrientedRedCycles QuarterGeometry RedCycles RedShadeCycles RedShadePaths
  Signals.FreeCellLocal

set_option maxRecDepth 20000

variable {indexGrid : Nat → Nat → Index}
  {shadeGrid : Nat → Nat → RedShades.State}
  {signalGrid : Nat → Nat → Signals.State}
  {west east south north : Nat}

theorem CycleShade.south_selected
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {quarterX : Nat}
    (hwest : quarterWest west < quarterX)
    (heast : quarterX < quarterEast east) :
    ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid quarterX (quarterSouth south))
      (quadrantAt quarterX (quarterSouth south))
      (shadeGrid quarterX (quarterSouth south)) = some .north := by
  apply ShadedSignals.selectedHorizontalFor_r1
  · rw [componentAt, show quarterSouth south / 2 = south by
      unfold quarterSouth
      omega]
    rw [← indexThick_eq]
    exact cycle.southLane (quarterX / 2) (by
      simp [quarterWest] at hwest
      omega) (by
      simp [quarterEast] at heast
      omega)
  · exact quadrantAt_quarterSouth_yBit quarterX south
  · have hshade := shaded.south_at cycle valid.shadeValid hwest heast
    simp [ShadedSignals.horizontalShade?, hshade.1]

theorem CycleShade.north_selected
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {quarterX : Nat}
    (hwest : quarterWest west < quarterX)
    (heast : quarterX < quarterEast east) :
    ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid quarterX (quarterNorth north))
      (quadrantAt quarterX (quarterNorth north))
      (shadeGrid quarterX (quarterNorth north)) = some .south := by
  apply ShadedSignals.selectedHorizontalFor_r3
  · rw [componentAt, show quarterNorth north / 2 = north by
      simp [quarterNorth]]
    rw [← indexThick_eq]
    exact cycle.northLane (quarterX / 2) (by
      simp [quarterWest] at hwest
      omega) (by
      simp [quarterEast] at heast
      omega)
  · exact quadrantAt_quarterNorth_yBit quarterX north
  · have hshade := shaded.north_at cycle valid.shadeValid hwest heast
    simp [ShadedSignals.horizontalShade?, hshade.1]

theorem CycleShade.west_selected
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {quarterY : Nat}
    (hsouth : quarterSouth south < quarterY)
    (hnorth : quarterY < quarterNorth north) :
    ShadedSignals.selectedVerticalFor
      (componentAt indexGrid (quarterWest west) quarterY)
      (quadrantAt (quarterWest west) quarterY)
      (shadeGrid (quarterWest west) quarterY) = some .east := by
  apply ShadedSignals.selectedVerticalFor_r0
  · rw [componentAt, show quarterWest west / 2 = west by
      unfold quarterWest
      omega]
    rw [← indexThick_eq]
    exact cycle.westLane (quarterY / 2) (by
      simp [quarterSouth] at hsouth
      omega) (by
      simp [quarterNorth] at hnorth
      omega)
  · exact quadrantAt_quarterWest_xBit west quarterY
  · have hshade := shaded.west_at cycle valid.shadeValid hsouth hnorth
    simp [ShadedSignals.verticalShade?, hshade.1]

theorem CycleShade.east_selected
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {quarterY : Nat}
    (hsouth : quarterSouth south < quarterY)
    (hnorth : quarterY < quarterNorth north) :
    ShadedSignals.selectedVerticalFor
      (componentAt indexGrid (quarterEast east) quarterY)
      (quadrantAt (quarterEast east) quarterY)
      (shadeGrid (quarterEast east) quarterY) = some .west := by
  apply ShadedSignals.selectedVerticalFor_r2
  · rw [componentAt, show quarterEast east / 2 = east by
      simp [quarterEast]]
    rw [← indexThick_eq]
    exact cycle.eastLane (quarterY / 2) (by
      simp [quarterSouth] at hsouth
      omega) (by
      simp [quarterNorth] at hnorth
      omega)
  · exact quadrantAt_quarterEast_xBit east quarterY
  · have hshade := shaded.east_at cycle valid.shadeValid hsouth hnorth
    simp [ShadedSignals.verticalShade?, hshade.1]

theorem CycleShade.south_signal_rules
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {quarterX : Nat}
    (hwest : quarterWest west < quarterX)
    (heast : quarterX < quarterEast east) :
    (signalGrid quarterX (quarterSouth south)).south ≠ .none ∧
      (signalGrid quarterX (quarterSouth south)).north ≠ .forward := by
  apply Signals.vertical_interiorNorth_rules
  simpa only [south_selected shaded cycle valid hwest heast] using
    valid.verticalAllowed quarterX (quarterSouth south)

theorem CycleShade.north_signal_rules
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {quarterX : Nat}
    (hwest : quarterWest west < quarterX)
    (heast : quarterX < quarterEast east) :
    (signalGrid quarterX (quarterNorth north)).north ≠ .none ∧
      (signalGrid quarterX (quarterNorth north)).south ≠ .backward := by
  apply Signals.vertical_interiorSouth_rules
  simpa only [north_selected shaded cycle valid hwest heast] using
    valid.verticalAllowed quarterX (quarterNorth north)

theorem CycleShade.west_signal_rules
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {quarterY : Nat}
    (hsouth : quarterSouth south < quarterY)
    (hnorth : quarterY < quarterNorth north) :
    (signalGrid (quarterWest west) quarterY).west ≠ .none ∧
      (signalGrid (quarterWest west) quarterY).east ≠ .forward := by
  apply Signals.horizontal_interiorEast_rules
  simpa only [west_selected shaded cycle valid hsouth hnorth] using
    valid.horizontalAllowed (quarterWest west) quarterY

theorem CycleShade.east_signal_rules
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {quarterY : Nat}
    (hsouth : quarterSouth south < quarterY)
    (hnorth : quarterY < quarterNorth north) :
    (signalGrid (quarterEast east) quarterY).east ≠ .none ∧
      (signalGrid (quarterEast east) quarterY).west ≠ .backward := by
  apply Signals.horizontal_interiorWest_rules
  simpa only [east_selected shaded cycle valid hsouth hnorth] using
    valid.horizontalAllowed (quarterEast east) quarterY

end ShadedPlaneSignalGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
