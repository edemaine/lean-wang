/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedSignals
import LeanWang.OllingerRobinson104SignalRoutingScaffold

/-!
Role-sensitive payload routing over the corrected shaded obstruction layer.
An all-clear occurrence of the distinguished corrected quarter tile marks the
fixed-corner payload seed.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSignals

open Signals

set_option maxRecDepth 20000

theorem isClear_tile_eq_true_iff (site : Site) :
    isClear (tile site) = true ↔ site.2 = clearState := by
  rcases site with ⟨base, signal⟩
  rcases signal with ⟨west, east, south, north⟩
  cases west <;> cases east <;> cases south <;> cases north <;>
    simp [isClear, edgeFlowCode, tile, Signals.State.tile, Flow.code,
      clearState, WangTile.product]

/-- Innermost corrected quarter-tile layer of a shaded signal tile. -/
def quarterLayer (wang : WangTile) : WangTile :=
  WangTile.productBase (WangTile.productBase wang)

theorem quarterLayer_primrec : Primrec quarterLayer :=
  WangTile.productBase_primrec.comp WangTile.productBase_primrec

@[simp] theorem quarterLayer_tile (site : Site) :
    quarterLayer (tile site) = Quarters.quarterTile site.1.1 := by
  simp [quarterLayer, tile, RedShades.tile]

/-- Quarter types appearing at the canonical marked crossing of every parent. -/
def markerQuarters : List Quarters.QuarterIndex :=
  [(0, .southwest), (1, .southwest),
    (2, .southwest), (3, .southwest)]

def isMarkerQuarterTile (wang : WangTile) : Bool :=
  wang == Quarters.quarterTile (0, .southwest) ||
    wang == Quarters.quarterTile (1, .southwest) ||
    wang == Quarters.quarterTile (2, .southwest) ||
    wang == Quarters.quarterTile (3, .southwest)

theorem isMarkerQuarterTile_primrec : Primrec isMarkerQuarterTile := by
  have heq (quarter : Quarters.QuarterIndex) :
      Primrec (fun wang : WangTile => wang == Quarters.quarterTile quarter) :=
    Primrec.beq.comp Primrec.id
      (Primrec.const (Quarters.quarterTile quarter))
  exact Primrec.or.comp
    (Primrec.or.comp
      (Primrec.or.comp (heq (0, .southwest)) (heq (1, .southwest)))
      (heq (2, .southwest)))
    (heq (3, .southwest))

set_option linter.style.nativeDecide false in
theorem isMarkerQuarterTile_quarterTile_eq_true_iff
    (quarter : Quarters.QuarterIndex) :
    isMarkerQuarterTile (Quarters.quarterTile quarter) = true ↔
      quarter ∈ markerQuarters := by
  rcases quarter with ⟨index, quadrant⟩
  cases quadrant <;> revert index <;> native_decide

/-- The finite marker selecting the lower-left payload seed crossing. -/
def isCornerMarker (wang : WangTile) : Bool :=
  Signals.isClear wang && isMarkerQuarterTile (quarterLayer wang)

theorem isCornerMarker_primrec : Primrec isCornerMarker := by
  exact Primrec.and.comp Signals.isClear_primrec
    (isMarkerQuarterTile_primrec.comp quarterLayer_primrec)

/-- Routing role with the distinguished all-clear quarter promoted to corner. -/
def routeRole (wang : WangTile) : RouteRole :=
  if isCornerMarker wang then RouteRole.corner else Signals.routeRole wang

theorem routeRole_primrec : Primrec routeRole := by
  have hmarker : PrimrecPred (fun wang => isCornerMarker wang = true) :=
    Primrec.eq.comp isCornerMarker_primrec (Primrec.const true)
  exact Primrec.ite hmarker (Primrec.const RouteRole.corner)
    Signals.routeRole_primrec

theorem routeRole_eq_active_or_corner_iff (wang : WangTile) :
    routeRole wang = RouteRole.active ∨
      routeRole wang = RouteRole.corner ↔
        Signals.routeRole wang = RouteRole.active := by
  by_cases hmarker : isCornerMarker wang = true
  · have hclear : Signals.isClear wang = true := by
      change (Signals.isClear wang &&
        isMarkerQuarterTile (quarterLayer wang)) = true
        at hmarker
      have hparts : Signals.isClear wang = true ∧
          isMarkerQuarterTile (quarterLayer wang) = true := by
        simpa only [Bool.and_eq_true] using hmarker
      exact hparts.1
    simp [routeRole, hmarker, (Signals.routeRole_eq_active_iff wang).2 hclear]
  · simp [routeRole, hmarker, Signals.routeRole_ne_corner]

theorem routeRole_tile_eq_corner_iff (site : Site) :
    routeRole (tile site) = RouteRole.corner ↔
      site.2 = clearState ∧ site.1.1 ∈ markerQuarters := by
  by_cases hmarker : isCornerMarker (tile site) = true
  · have hparts : site.2 = clearState ∧
        site.1.1 ∈ markerQuarters := by
      change (Signals.isClear (tile site) &&
        isMarkerQuarterTile (quarterLayer (tile site))) = true at hmarker
      rw [Bool.and_eq_true, isClear_tile_eq_true_iff, quarterLayer_tile,
        isMarkerQuarterTile_quarterTile_eq_true_iff] at hmarker
      exact hmarker
    simp [routeRole, hmarker, hparts]
  · constructor
    · intro hcorner
      have : Signals.routeRole (tile site) = .corner := by
        simpa [routeRole, hmarker] using hcorner
      exact False.elim (Signals.routeRole_ne_corner _ this)
    · rintro ⟨hclear, hquarter⟩
      exfalso
      apply hmarker
      simp [isCornerMarker, hclear, hquarter, isClear_tile_eq_true_iff,
        isMarkerQuarterTile_quarterTile_eq_true_iff]

theorem routeRole_tile_eq_active_iff (site : Site) :
    routeRole (tile site) = .active ↔
      site.2 = clearState ∧ site.1.1 ∉ markerQuarters := by
  constructor
  · intro hactive
    have hclear : site.2 = clearState := by
      apply (isClear_tile_eq_true_iff site).1
      exact (Signals.routeRole_eq_active_iff _).1
        ((routeRole_eq_active_or_corner_iff _).1 (Or.inl hactive))
    refine ⟨hclear, ?_⟩
    intro hcorner
    exact RouteRole.noConfusion
      (hactive.symm.trans ((routeRole_tile_eq_corner_iff site).2
        ⟨hclear, hcorner⟩))
  · rintro ⟨hclear, hnotCorner⟩
    have hor := (routeRole_eq_active_or_corner_iff (tile site)).2
      ((Signals.routeRole_eq_active_iff _).2
        ((isClear_tile_eq_true_iff site).2 hclear))
    rcases hor with hactive | hcorner
    · exact hactive
    · exact False.elim (hnotCorner
        ((routeRole_tile_eq_corner_iff site).1 hcorner).2)

theorem routeRole_tile_clear (site : Site) (hclear : site.2 = clearState) :
    routeRole (tile site) = .active ∨ routeRole (tile site) = .corner :=
  (routeRole_eq_active_or_corner_iff _).2
    ((Signals.routeRole_eq_active_iff _).2
      ((isClear_tile_eq_true_iff site).2 hclear))

/-- Final shaded Robinson scaffold with directional payload channels. -/
@[irreducible] def routedScaffold : RoutedScaffold where
  tiles := tileSet
  role := routeRole
  role_primrec := routeRole_primrec

@[simp] theorem routedScaffold_tiles : routedScaffold.tiles = tileSet := by
  unfold routedScaffold
  rfl

@[simp] theorem routedScaffold_role : routedScaffold.role = routeRole := by
  unfold routedScaffold
  rfl

end ShadedSignals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
