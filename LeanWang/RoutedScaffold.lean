/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Theorems

/-!
Role-sensitive scaffold combination for Robinson's routed free-grid argument.

Unlike the older Boolean scaffold interface, horizontal and vertical channel
cells constrain their payload layer to transmit the corresponding edge color.
-/

namespace LeanWang

/-- Payload-routing role of one scaffold tile. -/
inductive RouteRole where
  | inactive
  | horizontal
  | vertical
  | active
  | corner
deriving DecidableEq, Repr

namespace RouteRole

def toCode : RouteRole → Option (Bool × Bool)
  | .inactive => none
  | .horizontal => some (false, false)
  | .vertical => some (false, true)
  | .active => some (true, false)
  | .corner => some (true, true)

def ofCode : Option (Bool × Bool) → RouteRole
  | none => .inactive
  | some (false, false) => .horizontal
  | some (false, true) => .vertical
  | some (true, false) => .active
  | some (true, true) => .corner

def equivCode : RouteRole ≃ Option (Bool × Bool) where
  toFun := toCode
  invFun := ofCode
  left_inv := by intro role; cases role <;> rfl
  right_inv := by
    intro code
    rcases code with _ | ⟨first, second⟩
    · rfl
    · cases first <;> cases second <;> rfl

instance instPrimcodable : Primcodable RouteRole :=
  Primcodable.ofEquiv (Option (Bool × Bool)) equivCode

theorem toCode_primrec : Primrec toCode := by
  simpa [equivCode] using
    (Primrec.of_equiv (e := equivCode) : Primrec equivCode)

def isHorizontal : RouteRole → Bool
  | .horizontal => true
  | _ => false

def isVertical : RouteRole → Bool
  | .vertical => true
  | _ => false

def isActive : RouteRole → Bool
  | .active | .corner => true
  | _ => false

def isCorner : RouteRole → Bool
  | .corner => true
  | _ => false

theorem isHorizontal_primrec : Primrec isHorizontal := by
  exact (Primrec.eq.decide.comp Primrec.id
    (Primrec.const RouteRole.horizontal)).of_eq fun role => by
      cases role <;> rfl

theorem isVertical_primrec : Primrec isVertical := by
  exact (Primrec.eq.decide.comp Primrec.id
    (Primrec.const RouteRole.vertical)).of_eq fun role => by
      cases role <;> rfl

theorem isActive_primrec : Primrec isActive := by
  exact (Primrec.or.comp
    (Primrec.eq.decide.comp Primrec.id (Primrec.const RouteRole.active))
    (Primrec.eq.decide.comp Primrec.id (Primrec.const RouteRole.corner))).of_eq
      fun role => by cases role <;> rfl

theorem isCorner_primrec : Primrec isCorner := by
  exact (Primrec.eq.decide.comp Primrec.id
    (Primrec.const RouteRole.corner)).of_eq fun role => by
      cases role <;> rfl

end RouteRole

/-- Scaffold tiles together with a primitive-recursive routing-role decoder. -/
structure RoutedScaffold where
  tiles : TileSet
  role : WangTile → RouteRole
  role_primrec : Primrec role

/-- Complete-palette tiles that transmit their horizontal color unchanged. -/
def horizontalPayloadWires (T : TileSet) : TileSet :=
  (completePayloads T).filter fun tile => tile.w = tile.e

/-- Complete-palette tiles that transmit their vertical color unchanged. -/
def verticalPayloadWires (T : TileSet) : TileSet :=
  (completePayloads T).filter fun tile => tile.s = tile.n

theorem mem_horizontalPayloadWires_iff {T : TileSet} {tile : WangTile} :
    tile ∈ horizontalPayloadWires T ↔
      tile ∈ completePayloads T ∧ tile.w = tile.e := by
  simp [horizontalPayloadWires]

theorem mem_verticalPayloadWires_iff {T : TileSet} {tile : WangTile} :
    tile ∈ verticalPayloadWires T ↔
      tile ∈ completePayloads T ∧ tile.s = tile.n := by
  simp [verticalPayloadWires]

theorem horizontalPayloadWires_primrec : Primrec horizontalPayloadWires := by
  have hpredicate : PrimrecPred (fun tile : WangTile => tile.w = tile.e) :=
    Primrec.eq.comp WangTile.w_primrec WangTile.e_primrec
  exact (Primrec.listFilter hpredicate).comp completePayloads_primrec

theorem verticalPayloadWires_primrec : Primrec verticalPayloadWires := by
  have hpredicate : PrimrecPred (fun tile : WangTile => tile.s = tile.n) :=
    Primrec.eq.comp WangTile.s_primrec WangTile.n_primrec
  exact (Primrec.listFilter hpredicate).comp completePayloads_primrec

/-- Payload tiles permitted over one routed scaffold tile. -/
def routedPayloads (S : RoutedScaffold) (T : TileSet)
    (seed base : WangTile) : TileSet :=
  match S.role base with
  | .inactive => completePayloads T
  | .horizontal => horizontalPayloadWires T
  | .vertical => verticalPayloadWires T
  | .active => T
  | .corner => T.filter fun payload => payload = seed

/-- Layer a routed scaffold with a fixed-corner square instance. -/
def combineWithRoutedScaffold (S : RoutedScaffold) (T : TileSet)
    (seed : WangTile) : TileSet :=
  S.tiles.flatMap fun base =>
    (routedPayloads S T seed base).map fun payload =>
      WangTile.product base payload

theorem mem_routedPayloads_iff {S : RoutedScaffold} {T : TileSet}
    {seed base payload : WangTile} :
    payload ∈ routedPayloads S T seed base ↔
      match S.role base with
      | .inactive => payload ∈ completePayloads T
      | .horizontal =>
          payload ∈ completePayloads T ∧ payload.w = payload.e
      | .vertical =>
          payload ∈ completePayloads T ∧ payload.s = payload.n
      | .active => payload ∈ T
      | .corner => payload ∈ T ∧ payload = seed := by
  cases hrole : S.role base <;>
    simp [routedPayloads, hrole, horizontalPayloadWires,
      verticalPayloadWires]

theorem mem_combineWithRoutedScaffold_iff
    {S : RoutedScaffold} {T : TileSet} {seed tile : WangTile} :
    tile ∈ combineWithRoutedScaffold S T seed ↔
      ∃ base ∈ S.tiles, ∃ payload : WangTile,
        payload ∈ routedPayloads S T seed base ∧
          WangTile.product base payload = tile := by
  simp [combineWithRoutedScaffold]

theorem routedPayloads_primrec (S : RoutedScaffold) :
    Primrec (fun input : (TileSet × WangTile) × WangTile =>
      routedPayloads S input.1.1 input.1.2 input.2) := by
  let role : (TileSet × WangTile) × WangTile → RouteRole :=
    fun input => S.role input.2
  have hrole : Primrec role := S.role_primrec.comp Primrec.snd
  have hinactive : PrimrecPred (fun input => role input = RouteRole.inactive) :=
    Primrec.eq.comp hrole (Primrec.const RouteRole.inactive)
  have hhorizontal :
      PrimrecPred (fun input => role input = RouteRole.horizontal) :=
    Primrec.eq.comp hrole (Primrec.const RouteRole.horizontal)
  have hvertical : PrimrecPred (fun input => role input = RouteRole.vertical) :=
    Primrec.eq.comp hrole (Primrec.const RouteRole.vertical)
  have hactive : PrimrecPred (fun input => role input = RouteRole.active) :=
    Primrec.eq.comp hrole (Primrec.const RouteRole.active)
  have hcomplete : Primrec (fun input : (TileSet × WangTile) × WangTile =>
      completePayloads input.1.1) :=
    completePayloads_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hhorizontalWires : Primrec
      (fun input : (TileSet × WangTile) × WangTile =>
        horizontalPayloadWires input.1.1) :=
    horizontalPayloadWires_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hverticalWires : Primrec
      (fun input : (TileSet × WangTile) × WangTile =>
        verticalPayloadWires input.1.1) :=
    verticalPayloadWires_primrec.comp (Primrec.fst.comp Primrec.fst)
  have htiles : Primrec (fun input : (TileSet × WangTile) × WangTile =>
      input.1.1) := Primrec.fst.comp Primrec.fst
  have hseedOnly : Primrec (fun input : (TileSet × WangTile) × WangTile =>
      input.1.1.filter fun payload => payload = input.1.2) :=
    (PrimrecRel.listFilter
      (R := fun payload seed : WangTile => payload = seed) Primrec.eq).comp
        (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  exact (Primrec.ite hinactive hcomplete
    (Primrec.ite hhorizontal hhorizontalWires
      (Primrec.ite hvertical hverticalWires
        (Primrec.ite hactive htiles hseedOnly)))).of_eq fun input => by
          cases h : S.role input.2 <;> simp [routedPayloads, role, h]

theorem combineWithRoutedScaffold_primrec (S : RoutedScaffold) :
    Primrec (fun input : TileSet × WangTile =>
      combineWithRoutedScaffold S input.1 input.2) := by
  unfold combineWithRoutedScaffold
  refine Primrec.list_flatMap (Primrec.const S.tiles) ?_
  apply Primrec₂.mk
  have hpayload : Primrec
      (fun input : (TileSet × WangTile) × WangTile =>
        routedPayloads S input.1.1 input.1.2 input.2) :=
    routedPayloads_primrec S
  refine Primrec.list_map hpayload ?_
  rw [← Primrec₂.uncurry]
  exact WangTile.product_primrec.comp
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem combineWithRoutedScaffold_computable (S : RoutedScaffold) :
    Computable (fun input : TileSet × WangTile =>
      combineWithRoutedScaffold S input.1 input.2) :=
  (combineWithRoutedScaffold_primrec S).to_comp

end LeanWang
