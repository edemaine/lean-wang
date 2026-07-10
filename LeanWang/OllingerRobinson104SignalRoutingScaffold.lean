/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SignalScaffold
import LeanWang.RoutedScaffold

/-!
The role-sensitive routed scaffold carried by Robinson's signal layer.

The absence of horizontal and vertical obstruction signals supplies two local
bits. They distinguish horizontal channels, vertical channels, crossings, and
inactive sites. The corner role is reserved for a subsequent finite marker
decoration selecting the seed crossing.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals

set_option maxRecDepth 20000

/-- Whether both horizontal signal edges of a Wang tile are clear. -/
def horizontalClear (wang : WangTile) : Bool :=
  edgeFlowCode wang.w == 0 && edgeFlowCode wang.e == 0

/-- Whether both vertical signal edges of a Wang tile are clear. -/
def verticalClear (wang : WangTile) : Bool :=
  edgeFlowCode wang.s == 0 && edgeFlowCode wang.n == 0

theorem horizontalClear_primrec : Primrec horizontalClear := by
  have hw : Primrec (fun wang : WangTile => edgeFlowCode wang.w) :=
    Primrec.snd.comp (Primrec.unpair.comp WangTile.w_primrec)
  have he : Primrec (fun wang : WangTile => edgeFlowCode wang.e) :=
    Primrec.snd.comp (Primrec.unpair.comp WangTile.e_primrec)
  exact Primrec.and.comp
    (Primrec.beq.comp hw (Primrec.const 0))
    (Primrec.beq.comp he (Primrec.const 0))

theorem verticalClear_primrec : Primrec verticalClear := by
  have hs : Primrec (fun wang : WangTile => edgeFlowCode wang.s) :=
    Primrec.snd.comp (Primrec.unpair.comp WangTile.s_primrec)
  have hn : Primrec (fun wang : WangTile => edgeFlowCode wang.n) :=
    Primrec.snd.comp (Primrec.unpair.comp WangTile.n_primrec)
  exact Primrec.and.comp
    (Primrec.beq.comp hs (Primrec.const 0))
    (Primrec.beq.comp hn (Primrec.const 0))

/-- Routing role decoded from the two clear-signal directions. -/
def routeRole (wang : WangTile) : RouteRole :=
  if horizontalClear wang then
    if verticalClear wang then .active else .horizontal
  else if verticalClear wang then .vertical else .inactive

theorem routeRole_primrec : Primrec routeRole := by
  have hhorizontal : PrimrecPred (fun wang => horizontalClear wang = true) :=
    Primrec.eq.comp horizontalClear_primrec (Primrec.const true)
  have hvertical : PrimrecPred (fun wang => verticalClear wang = true) :=
    Primrec.eq.comp verticalClear_primrec (Primrec.const true)
  exact Primrec.ite hhorizontal
    (Primrec.ite hvertical
      (Primrec.const RouteRole.active)
      (Primrec.const RouteRole.horizontal))
    (Primrec.ite hvertical
      (Primrec.const RouteRole.vertical)
      (Primrec.const RouteRole.inactive))

/-- The active role agrees exactly with the older all-clear predicate. -/
theorem routeRole_eq_active_iff (wang : WangTile) :
    routeRole wang = .active ↔ isClear wang = true := by
  simp only [routeRole, isClear, horizontalClear, verticalClear]
  split_ifs <;> simp_all only [Bool.and_eq_true, beq_iff_eq] <;> aesop

theorem routeRole_eq_horizontal_iff (wang : WangTile) :
    routeRole wang = .horizontal ↔
      horizontalClear wang = true ∧ verticalClear wang = false := by
  simp only [routeRole]
  split_ifs <;> simp_all

theorem routeRole_eq_vertical_iff (wang : WangTile) :
    routeRole wang = .vertical ↔
      horizontalClear wang = false ∧ verticalClear wang = true := by
  simp only [routeRole]
  split_ifs <;> simp_all

theorem routeRole_eq_inactive_iff (wang : WangTile) :
    routeRole wang = .inactive ↔
      horizontalClear wang = false ∧ verticalClear wang = false := by
  simp only [routeRole]
  split_ifs <;> simp_all

theorem routeRole_tile_eq_active_iff (site : Site) :
    routeRole (tile site) = .active ↔ site.2 = clearState := by
  rw [routeRole_eq_active_iff, isClear_tile_eq_true_iff]

theorem routeRole_ne_corner (wang : WangTile) :
    routeRole wang ≠ .corner := by
  simp only [routeRole]
  split_ifs <;> simp

/-- Concrete Robinson signal scaffold with role-sensitive payload channels. -/
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

end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
