/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedLightBoardSignals

/-!
Signal characterization of free rows and columns inside uniformly light
Robinson boards.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedPlaneSignalGrid

open OrientedRedCycles RedShadeCycles ShadedPlaneShadeGrid Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- No selected light vertical border crosses this strict board row. -/
def IsFreeRow (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east row : Nat) : Prop :=
  ∀ quarterX, quarterWest west < quarterX → quarterX < quarterEast east →
    ShadedSignals.selectedVerticalFor
      (componentAt indexGrid quarterX row) (quadrantAt quarterX row)
      (shadeGrid quarterX row) = none

/-- No selected light horizontal border crosses this strict board column. -/
def IsFreeColumn (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (south north column : Nat) : Prop :=
  ∀ quarterY, quarterSouth south < quarterY → quarterY < quarterNorth north →
    ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column quarterY) (quadrantAt column quarterY)
      (shadeGrid column quarterY) = none

variable {indexGrid : Nat → Nat → Index}
  {shadeGrid : Nat → Nat → RedShades.State}
  {signalGrid : Nat → Nat → Signals.State}
  {west east south north : Nat}

set_option maxHeartbeats 500000 in
-- Elaborating both dependent board endpoints and arbitrary corridor lengths.
theorem CycleShade.clear_at_free_row
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {row quarterX : Nat}
    (hsouth : quarterSouth south < row)
    (hnorth : row < quarterNorth north)
    (free : IsFreeRow indexGrid shadeGrid west east row)
    (hwest : quarterWest west < quarterX)
    (heast : quarterX < quarterEast east) :
    (signalGrid quarterX row).west = .none ∧
      (signalGrid quarterX row).east = .none := by
  let left := quarterWest west
  let right := quarterEast east
  have hleftRight : left < right := by
    have := cycle.west_lt_east
    simp [left, right, quarterWest, quarterEast]
    omega
  have hwhole : (signalGrid left row).east = (signalGrid right row).west := by
    have hflow := Signals.horizontal_flow_across
      (fun x => signalGrid x row) left (right - left - 1)
      (fun i hi => valid.hmatch (left + i) row)
      (fun i hi => Signals.horizontal_transmits_of_allowed (by
        have hfree := free (left + i + 1) (by omega) (by omega)
        simpa only [hfree] using valid.horizontalAllowed (left + i + 1) row))
    have hend : left + (right - left - 1) + 1 = right := by omega
    simpa only [hend] using hflow
  have hleftRule := west_signal_rules shaded cycle valid hsouth hnorth
  have hrightRule := east_signal_rules shaded cycle valid hsouth hnorth
  have hends := Signals.horizontal_clear_of_inner_edges hwhole
    hleftRule.2 hrightRule.2
  have hprefix : (signalGrid left row).east =
      (signalGrid quarterX row).west := by
    have hflow := Signals.horizontal_flow_across
      (fun x => signalGrid x row) left (quarterX - left - 1)
      (fun i hi => valid.hmatch (left + i) row)
      (fun i hi => Signals.horizontal_transmits_of_allowed (by
        have hfree := free (left + i + 1) (by omega) (by omega)
        simpa only [hfree] using valid.horizontalAllowed (left + i + 1) row))
    have hend : left + (quarterX - left - 1) + 1 = quarterX := by omega
    simpa only [hend] using hflow
  have hwestClear : (signalGrid quarterX row).west = .none :=
    hprefix.symm.trans hends.1
  have htransmit := Signals.horizontal_transmits_of_allowed (by
    have hfree := free quarterX hwest heast
    simpa only [hfree] using valid.horizontalAllowed quarterX row)
  exact ⟨hwestClear, htransmit.symm.trans hwestClear⟩

set_option maxHeartbeats 500000 in
-- Elaborating both dependent board endpoints and arbitrary corridor lengths.
theorem CycleShade.clear_at_free_column
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {column quarterY : Nat}
    (hwest : quarterWest west < column)
    (heast : column < quarterEast east)
    (free : IsFreeColumn indexGrid shadeGrid south north column)
    (hsouth : quarterSouth south < quarterY)
    (hnorth : quarterY < quarterNorth north) :
    (signalGrid column quarterY).south = .none ∧
      (signalGrid column quarterY).north = .none := by
  let lower := quarterSouth south
  let upper := quarterNorth north
  have hlowerUpper : lower < upper := by
    have := cycle.south_lt_north
    simp [lower, upper, quarterSouth, quarterNorth]
    omega
  have hwhole : (signalGrid column lower).north =
      (signalGrid column upper).south := by
    have hflow := Signals.vertical_flow_across
      (fun y => signalGrid column y) lower (upper - lower - 1)
      (fun i hi => valid.vmatch column (lower + i))
      (fun i hi => Signals.vertical_transmits_of_allowed (by
        have hfree := free (lower + i + 1) (by omega) (by omega)
        simpa only [hfree] using valid.verticalAllowed column (lower + i + 1)))
    have hend : lower + (upper - lower - 1) + 1 = upper := by omega
    simpa only [hend] using hflow
  have hlowerRule := south_signal_rules shaded cycle valid hwest heast
  have hupperRule := north_signal_rules shaded cycle valid hwest heast
  have hends := Signals.vertical_clear_of_inner_edges hwhole
    hlowerRule.2 hupperRule.2
  have hprefix : (signalGrid column lower).north =
      (signalGrid column quarterY).south := by
    have hflow := Signals.vertical_flow_across
      (fun y => signalGrid column y) lower (quarterY - lower - 1)
      (fun i hi => valid.vmatch column (lower + i))
      (fun i hi => Signals.vertical_transmits_of_allowed (by
        have hfree := free (lower + i + 1) (by omega) (by omega)
        simpa only [hfree] using valid.verticalAllowed column (lower + i + 1)))
    have hend : lower + (quarterY - lower - 1) + 1 = quarterY := by omega
    simpa only [hend] using hflow
  have hsouthClear : (signalGrid column quarterY).south = .none :=
    hprefix.symm.trans hends.1
  have htransmit := Signals.vertical_transmits_of_allowed (by
    have hfree := free quarterY hsouth hnorth
    simpa only [hfree] using valid.verticalAllowed column quarterY)
  exact ⟨hsouthClear, htransmit.symm.trans hsouthClear⟩

theorem CycleShade.clear_at_free_crossing
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {column row : Nat}
    (hwest : quarterWest west < column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south < row)
    (hnorth : row < quarterNorth north)
    (freeRow : IsFreeRow indexGrid shadeGrid west east row)
    (freeColumn : IsFreeColumn indexGrid shadeGrid south north column) :
    signalGrid column row = Signals.clearState := by
  have hhorizontal := clear_at_free_row shaded cycle valid
    hsouth hnorth freeRow hwest heast
  have hvertical := clear_at_free_column shaded cycle valid
    hwest heast freeColumn hsouth hnorth
  rcases hstate : signalGrid column row with ⟨westFlow, eastFlow,
    southFlow, northFlow⟩
  simp only [hstate] at hhorizontal
  simp only [hstate] at hvertical
  simp [Signals.clearState, hhorizontal.1, hhorizontal.2,
    hvertical.1, hvertical.2]

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int → TileIn
    (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}

theorem routeRole_at_clear
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) (quarterX quarterY : Nat)
    (hclear : ShadedPlaneSignalGrid.signalGrid decoded parentOrigin
      quarterX quarterY =
      Signals.clearState) :
    ShadedSignals.routeRole
      (decoded.base (ShadedPlaneShadeGrid.point decoded parentOrigin
        quarterX quarterY)).1 =
        .active ∨
      ShadedSignals.routeRole
        (decoded.base (ShadedPlaneShadeGrid.point decoded parentOrigin
          quarterX quarterY)).1 = .corner := by
  let p := ShadedPlaneShadeGrid.point decoded parentOrigin quarterX quarterY
  have hrole := ShadedSignals.routeRole_tile_clear
    (ShadedSignals.decode (decoded.base p)) (by
      simpa only [ShadedPlaneSignalGrid.signalGrid,
        ShadedSignals.signalPlane, p] using hclear)
  simpa only [ShadedSignals.decode_tile] using hrole

theorem routeRole_at_clear_eq_corner_iff
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) (quarterX quarterY : Nat)
    (hclear : ShadedPlaneSignalGrid.signalGrid decoded parentOrigin
      quarterX quarterY = Signals.clearState) :
    ShadedSignals.routeRole
        (decoded.base (ShadedPlaneShadeGrid.point decoded parentOrigin
          quarterX quarterY)).1 = .corner ↔
      decoded.quarter (ShadedPlaneShadeGrid.point decoded parentOrigin
        quarterX quarterY) = Signals.cornerQuarter := by
  let p := ShadedPlaneShadeGrid.point decoded parentOrigin quarterX quarterY
  have hsignal : (ShadedSignals.decode (decoded.base p)).2 =
      Signals.clearState := by
    simpa only [ShadedPlaneSignalGrid.signalGrid,
      ShadedSignals.signalPlane, p] using hclear
  have hrole := ShadedSignals.routeRole_tile_eq_corner_iff
    (ShadedSignals.decode (decoded.base p))
  rw [ShadedSignals.decode_tile] at hrole
  constructor
  · intro hcorner
    have hquarter := (hrole.1 hcorner).2
    simpa only [ShadedRoutedPlaneDecode.Decoded.quarter,
      ShadedSignals.quarterPlane, ShadedSignals.sitePlane, p] using hquarter
  · intro hquarter
    apply hrole.2
    refine ⟨hsignal, ?_⟩
    simpa only [ShadedRoutedPlaneDecode.Decoded.quarter,
      ShadedSignals.quarterPlane, ShadedSignals.sitePlane, p] using hquarter

theorem payload_at_clear_corner_eq_seed
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) (quarterX quarterY : Nat)
    (hclear : ShadedPlaneSignalGrid.signalGrid decoded parentOrigin
      quarterX quarterY = Signals.clearState)
    (hquarter : decoded.quarter
      (ShadedPlaneShadeGrid.point decoded parentOrigin quarterX quarterY) =
        Signals.cornerQuarter) :
    decoded.payload (ShadedPlaneShadeGrid.point decoded parentOrigin
      quarterX quarterY) = seed := by
  exact (decoded.corner_payload _
    ((routeRole_at_clear_eq_corner_iff decoded parentOrigin
      quarterX quarterY hclear).2 hquarter)).2

theorem payload_free_crossing_mem
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int)
    {west east south north column row : Nat}
    (cycle : CycleOn (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      west east south north)
    (shaded : CycleShade (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      west east south north .light)
    (hwest : quarterWest west < column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south < row)
    (hnorth : row < quarterNorth north)
    (freeRow : IsFreeRow
      (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin) west east row)
    (freeColumn : IsFreeColumn
      (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      south north column) :
    decoded.payload (ShadedPlaneShadeGrid.point decoded parentOrigin
      column row) ∈ T := by
  have hclear := CycleShade.clear_at_free_crossing shaded cycle
    (ShadedPlaneSignalGrid.valid decoded parentOrigin)
    hwest heast hsouth hnorth freeRow freeColumn
  rcases routeRole_at_clear decoded parentOrigin column row hclear with
    hactive | hcorner
  · exact decoded.active_payload _ hactive
  · exact (decoded.corner_payload _ hcorner).1

end ShadedPlaneSignalGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
