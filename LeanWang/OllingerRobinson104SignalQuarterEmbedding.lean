/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SignalPlaneDecode
import LeanWang.OllingerRobinson104OrientedPlaneRedBoards

/-!
Embed parent-plane red-board coordinates into the concrete signal quarter plane.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals
namespace QuarterEmbedding

open Figure16 QuarterGeometry CombinedPlaneDecode
  QuarterRegrouping ParentPlane Desubstitution

set_option maxRecDepth 20000

theorem verticalInterior_r0 {component : Thick} {quadrant : Quadrant}
    (hline : containsLine component .r0 = true)
    (heast : quadrant.xBit = true) :
    verticalInterior? component quadrant = some .east := by
  cases component <;> cases quadrant <;>
    simp [containsLine, Thick.lineSum?, ThickLineSum.mkDistinct,
      redVerticalAt, verticalInterior?, Quadrant.xBit] at hline heast ⊢

theorem verticalInterior_r2 {component : Thick} {quadrant : Quadrant}
    (hline : containsLine component .r2 = true)
    (hwest : quadrant.xBit = false) :
    verticalInterior? component quadrant = some .west := by
  cases component <;> cases quadrant <;>
    simp [containsLine, Thick.lineSum?, ThickLineSum.mkDistinct,
      redVerticalAt, verticalInterior?, Quadrant.xBit] at hline hwest ⊢

theorem horizontalInterior_r1 {component : Thick} {quadrant : Quadrant}
    (hline : containsLine component .r1 = true)
    (hnorth : quadrant.yBit = true) :
    horizontalInterior? component quadrant = some .north := by
  cases component <;> cases quadrant <;>
    simp [containsLine, Thick.lineSum?, ThickLineSum.mkDistinct,
      redHorizontalAt, horizontalInterior?, Quadrant.yBit] at hline hnorth ⊢

theorem horizontalInterior_r3 {component : Thick} {quadrant : Quadrant}
    (hline : containsLine component .r3 = true)
    (hsouth : quadrant.yBit = false) :
    horizontalInterior? component quadrant = some .south := by
  cases component <;> cases quadrant <;>
    simp [containsLine, Thick.lineSum?, ThickLineSum.mkDistinct,
      redHorizontalAt, horizontalInterior?, Quadrant.yBit] at hline hsouth ⊢

def quadrantDx : Quadrant → Int
  | .southwest | .northwest => 0
  | .southeast | .northeast => 1

def quadrantDy : Quadrant → Int
  | .southwest | .southeast => 0
  | .northwest | .northeast => 1

/-- Concrete quarter-plane coordinate of one parent tile quadrant. -/
def point {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (decoded : Decoded x) (parentCoordinate : Int × Int)
    (quadrant : Quadrant) : Int × Int :=
  shift (blockOrigin decoded.quarterOrigin parentCoordinate)
    (quadrantDx quadrant) (quadrantDy quadrant)

theorem quarter_at_point {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (decoded : Decoded x) (parentCoordinate : Int × Int)
    (quadrant : Quadrant) :
    quarterPlane decoded.base (point decoded parentCoordinate quadrant) =
      (decoded.parent parentCoordinate, quadrant) := by
  have hblocks := decoded.quarter_blocks parentCoordinate
  cases quadrant with
  | southwest =>
      simpa [CombinedPlaneDecode.Decoded.quarter, point, quadrantDx,
        quadrantDy, shift] using hblocks.1
  | southeast =>
      simpa [CombinedPlaneDecode.Decoded.quarter, point, quadrantDx,
        quadrantDy] using hblocks.2.1
  | northwest =>
      simpa [CombinedPlaneDecode.Decoded.quarter, point, quadrantDx,
        quadrantDy] using hblocks.2.2.1
  | northeast =>
      simpa [CombinedPlaneDecode.Decoded.quarter, point, quadrantDx,
        quadrantDy] using hblocks.2.2.2

theorem locallyAllowed_at_point {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (decoded : Decoded x) (parentCoordinate : Int × Int)
    (quadrant : Quadrant) :
    locallyAllowed (decoded.parent parentCoordinate, quadrant)
      (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true := by
  have hallowed := plane_locallyAllowed decoded.base
    (point decoded parentCoordinate quadrant)
  rw [quarter_at_point decoded parentCoordinate quadrant] at hallowed
  exact hallowed

theorem horizontalAllowed_at_point {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (decoded : Decoded x) (parentCoordinate : Int × Int)
    (quadrant : Quadrant) :
    horizontalAllowed
        (verticalInterior? (components (decoded.parent parentCoordinate)).2.1 quadrant)
        (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true := by
  have hallowed := locallyAllowed_at_point decoded parentCoordinate quadrant
  have hparts :
      horizontalAllowed
          (verticalInterior? (components (decoded.parent parentCoordinate)).2.1 quadrant)
          (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true ∧
        verticalAllowed
          (horizontalInterior? (components (decoded.parent parentCoordinate)).2.1 quadrant)
          (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true := by
    simpa only [locallyAllowed, Bool.and_eq_true] using hallowed
  exact hparts.1

theorem verticalAllowed_at_point {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (decoded : Decoded x) (parentCoordinate : Int × Int)
    (quadrant : Quadrant) :
    verticalAllowed
        (horizontalInterior? (components (decoded.parent parentCoordinate)).2.1 quadrant)
        (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true := by
  have hallowed := locallyAllowed_at_point decoded parentCoordinate quadrant
  have hparts :
      horizontalAllowed
          (verticalInterior? (components (decoded.parent parentCoordinate)).2.1 quadrant)
          (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true ∧
        verticalAllowed
          (horizontalInterior? (components (decoded.parent parentCoordinate)).2.1 quadrant)
          (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true := by
    simpa only [locallyAllowed, Bool.and_eq_true] using hallowed
  exact hparts.2

theorem horizontalAllowed_r0 {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (decoded : Decoded x) (parentCoordinate : Int × Int)
    {quadrant : Quadrant} (heast : quadrant.xBit = true)
    (hline : QuarterGeometry.containsLine
      (RedCycles.indexThick (decoded.parent parentCoordinate)) .r0 = true) :
    horizontalAllowed (some .east)
      (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true := by
  have hboundary : verticalInterior?
      (components (decoded.parent parentCoordinate)).2.1 quadrant = some .east := by
    apply verticalInterior_r0 (quadrant := quadrant) _ heast
    simpa only [RedCycles.indexThick_eq] using hline
  simpa only [hboundary] using
    horizontalAllowed_at_point decoded parentCoordinate quadrant

theorem horizontalAllowed_r2 {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (decoded : Decoded x) (parentCoordinate : Int × Int)
    {quadrant : Quadrant} (hwest : quadrant.xBit = false)
    (hline : QuarterGeometry.containsLine
      (RedCycles.indexThick (decoded.parent parentCoordinate)) .r2 = true) :
    horizontalAllowed (some .west)
      (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true := by
  have hboundary : verticalInterior?
      (components (decoded.parent parentCoordinate)).2.1 quadrant = some .west := by
    apply verticalInterior_r2 (quadrant := quadrant) _ hwest
    simpa only [RedCycles.indexThick_eq] using hline
  simpa only [hboundary] using
    horizontalAllowed_at_point decoded parentCoordinate quadrant

theorem verticalAllowed_r1 {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (decoded : Decoded x) (parentCoordinate : Int × Int)
    {quadrant : Quadrant} (hnorth : quadrant.yBit = true)
    (hline : QuarterGeometry.containsLine
      (RedCycles.indexThick (decoded.parent parentCoordinate)) .r1 = true) :
    verticalAllowed (some .north)
      (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true := by
  have hboundary : horizontalInterior?
      (components (decoded.parent parentCoordinate)).2.1 quadrant = some .north := by
    apply horizontalInterior_r1 (quadrant := quadrant) _ hnorth
    simpa only [RedCycles.indexThick_eq] using hline
  simpa only [hboundary] using
    verticalAllowed_at_point decoded parentCoordinate quadrant

theorem verticalAllowed_r3 {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (decoded : Decoded x) (parentCoordinate : Int × Int)
    {quadrant : Quadrant} (hsouth : quadrant.yBit = false)
    (hline : QuarterGeometry.containsLine
      (RedCycles.indexThick (decoded.parent parentCoordinate)) .r3 = true) :
    verticalAllowed (some .south)
      (signalPlane decoded.base (point decoded parentCoordinate quadrant)) = true := by
  have hboundary : horizontalInterior?
      (components (decoded.parent parentCoordinate)).2.1 quadrant = some .south := by
    apply horizontalInterior_r3 (quadrant := quadrant) _ hsouth
    simpa only [RedCycles.indexThick_eq] using hline
  simpa only [hboundary] using
    verticalAllowed_at_point decoded parentCoordinate quadrant

end QuarterEmbedding
end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
