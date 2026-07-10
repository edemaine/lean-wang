/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SignalRoutedPlaneDecode
import LeanWang.OllingerRobinson104SignalFreeCrossings
import LeanWang.OllingerRobinson104IteratedEmbedding

/-!
Instantiate the abstract free-crossing theorem inside an actual routed
Robinson product plane.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals
namespace RoutedFreeCrossings

open Desubstitution ParentPlane HierarchyEmbedding FreeCellLocal
  FreeCellEmbedding FreeCrossings RoutedSignalPlaneDecode RedCycles

set_option maxRecDepth 20000

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int → TileIn
    (combineWithRoutedScaffold routedScaffold T seed)}

/-- Quarter-plane origin of the natural grid below a parent coordinate. -/
def quarterGridOrigin (decoded : RoutedSignalPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) : Int × Int :=
  blockOrigin decoded.quarterOrigin parentOrigin

/-- Actual quarter-plane point at a natural offset from a parent origin. -/
def point (decoded : RoutedSignalPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) (quarterX quarterY : Nat) : Int × Int :=
  shift (quarterGridOrigin decoded parentOrigin) quarterX quarterY

/-- Regrouping identifies every natural quarter-grid point exactly. -/
theorem quarter_at_point (decoded : RoutedSignalPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) (quarterX quarterY : Nat) :
    decoded.quarter (point decoded parentOrigin quarterX quarterY) =
      (natGridAt decoded.parent parentOrigin
          (quarterX / 2) (quarterY / 2),
        quadrantAt quarterX quarterY) := by
  let parentCoordinate :=
    shift parentOrigin (quarterX / 2 : Nat) (quarterY / 2 : Nat)
  have hcoordinate := childCoordinate decoded.quarterOrigin parentOrigin
    quarterX quarterY
  have hblocks := decoded.quarter_blocks parentCoordinate
  have hx : quarterX % 2 = 0 ∨ quarterX % 2 = 1 := by
    have := Nat.mod_lt quarterX (by decide : 0 < 2)
    omega
  have hy : quarterY % 2 = 0 ∨ quarterY % 2 = 1 := by
    have := Nat.mod_lt quarterY (by decide : 0 < 2)
    omega
  rw [show point decoded parentOrigin quarterX quarterY =
      shift (blockOrigin decoded.quarterOrigin parentCoordinate)
        (quarterX % 2 : Nat) (quarterY % 2 : Nat) by
    simpa only [point, quarterGridOrigin, parentCoordinate] using hcoordinate]
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · simpa [parentCoordinate, natGridAt, quadrantAt, Quadrant.ofBits, hx, hy, shift]
      using hblocks.1
  · simpa [parentCoordinate, natGridAt, quadrantAt, Quadrant.ofBits, hx, hy]
      using hblocks.2.2.1
  · simpa [parentCoordinate, natGridAt, quadrantAt, Quadrant.ofBits, hx, hy]
      using hblocks.2.1
  · simpa [parentCoordinate, natGridAt, quadrantAt, Quadrant.ofBits, hx, hy]
      using hblocks.2.2.2

/-- Signal states on the natural quarter grid below a parent coordinate. -/
def stateGrid (decoded : RoutedSignalPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) : Nat → Nat → State :=
  fun quarterX quarterY =>
    signalPlane decoded.base (point decoded parentOrigin quarterX quarterY)

theorem stateGrid_valid (decoded : RoutedSignalPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) :
    ValidSignalGrid (natGridAt decoded.parent parentOrigin)
      (stateGrid decoded parentOrigin) := by
  constructor
  · intro quarterX quarterY
    have hallowed := plane_locallyAllowed decoded.base
      (point decoded parentOrigin quarterX quarterY)
    change locallyAllowed
      (decoded.quarter (point decoded parentOrigin quarterX quarterY))
      (signalPlane decoded.base
        (point decoded parentOrigin quarterX quarterY)) = true at hallowed
    rw [quarter_at_point decoded parentOrigin quarterX quarterY] at hallowed
    simpa only [stateGrid] using hallowed
  · intro quarterX quarterY
    have hmatch := signalPlane_hmatch decoded.base_valid
      (point decoded parentOrigin quarterX quarterY)
    have hpoint : point decoded parentOrigin (quarterX + 1) quarterY =
        ((point decoded parentOrigin quarterX quarterY).1 + 1,
          (point decoded parentOrigin quarterX quarterY).2) := by
      simp [point, quarterGridOrigin, shift]
      omega
    simpa only [stateGrid, hpoint] using hmatch
  · intro quarterX quarterY
    have hmatch := signalPlane_vmatch decoded.base_valid
      (point decoded parentOrigin quarterX quarterY)
    have hpoint : point decoded parentOrigin quarterX (quarterY + 1) =
        ((point decoded parentOrigin quarterX quarterY).1,
          (point decoded parentOrigin quarterX quarterY).2 + 1) := by
      simp [point, quarterGridOrigin, shift]
      omega
    simpa only [stateGrid, hpoint] using hmatch

/-- Coarse index grid whose depth refinement occurs below a tower coordinate. -/
def coarseGrid (decoded : RoutedSignalPlaneDecode.Decoded x)
    (depth : Nat) (coarseOrigin : Int × Int) : Nat → Nat → Index :=
  natGridAt (decoded.tower.plane depth).tiling coarseOrigin

/-- Actual parent-plane origin of that depth refinement. -/
def fineParentOrigin (decoded : RoutedSignalPlaneDecode.Decoded x)
    (depth : Nat) (coarseOrigin : Int × Int) : Int × Int :=
  descendOrigin decoded.tower 0 depth coarseOrigin

theorem parentGrid_eq_iterateRefine
    (decoded : RoutedSignalPlaneDecode.Decoded x)
    (depth : Nat) (coarseOrigin : Int × Int) :
    natGridAt decoded.parent (fineParentOrigin decoded depth coarseOrigin) =
      iterateRefine depth (coarseGrid decoded depth coarseOrigin) := by
  have h := HierarchyEmbedding.Tower.natGridAt_descendOrigin
    decoded.tower depth 0 coarseOrigin
  rw [decoded.tower.zero] at h
  simpa only [RoutedSignalPlaneDecode.Decoded.hierarchyBase, Nat.zero_add,
    fineParentOrigin, coarseGrid] using h

theorem refined_stateGrid_valid
    (decoded : RoutedSignalPlaneDecode.Decoded x)
    (depth : Nat) (coarseOrigin : Int × Int) :
    ValidSignalGrid (iterateRefine depth
        (coarseGrid decoded depth coarseOrigin))
      (stateGrid decoded (fineParentOrigin decoded depth coarseOrigin)) := by
  rw [← parentGrid_eq_iterateRefine decoded depth coarseOrigin]
  exact stateGrid_valid decoded _

/-- Selected free crossing in actual quarter-plane coordinates. -/
def freePoint (decoded : RoutedSignalPlaneDecode.Decoded x)
    (depth : Nat) (coarseOrigin : Int × Int) (i j : Nat) : Int × Int :=
  point decoded (fineParentOrigin decoded depth coarseOrigin)
    (freeCoordinate depth i) (freeCoordinate depth j)

/-- Every selected actual free crossing has the active routing role. -/
theorem routeRole_freePoint_eq_active
    (decoded : RoutedSignalPlaneDecode.Decoded x)
    {depth : Nat} (hdepth : 5 ≤ depth)
    (coarseOrigin : Int × Int) (i j : Nat) :
    routeRole (decoded.base (freePoint decoded depth coarseOrigin i j)).1 =
      .active := by
  have hclear := clearState_at
    (depth := depth) (i := i) (j := j) hdepth
    (refined_stateGrid_valid decoded depth coarseOrigin)
  have hrole : routeRole
      (tile (sitePlane decoded.base
        (freePoint decoded depth coarseOrigin i j))) = .active :=
    (routeRole_tile_eq_active_iff _).2 (by
      simpa only [stateGrid, freePoint, signalPlane] using hclear)
  change routeRole
    (tile (decode (decoded.base
      (freePoint decoded depth coarseOrigin i j)))) = .active at hrole
  rw [decode_tile] at hrole
  exact hrole

/-- Payloads at all selected actual free crossings belong to the source set. -/
theorem payload_freePoint_mem
    (decoded : RoutedSignalPlaneDecode.Decoded x)
    {depth : Nat} (hdepth : 5 ≤ depth)
    (coarseOrigin : Int × Int) (i j : Nat) :
    decoded.payload (freePoint decoded depth coarseOrigin i j) ∈ T :=
  decoded.active_payload _
    (routeRole_freePoint_eq_active decoded hdepth coarseOrigin i j)

end RoutedFreeCrossings
end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
