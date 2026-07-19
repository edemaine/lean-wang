/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Scaffold.Payload

/-!
Role-sensitive scaffold combination for Robinson's routed free-grid argument.

Horizontal and vertical channel cells constrain their payload layer to
transmit the corresponding edge color.
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

instance instFintype : Fintype RouteRole :=
  Fintype.ofList [.inactive, .horizontal, .vertical, .active, .corner] (by
    intro role
    cases role <;> simp)

instance instPrimcodable : Primcodable RouteRole :=
  Primcodable.ofEquiv (Option (Bool × Bool)) equivCode

theorem toCode_primrec : Primrec toCode :=
  Primrec.dom_finite _

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

/-- Whether a routed payload cell has a prescribed channel or source role. -/
def isConstrained : RouteRole → Bool
  | .inactive => false
  | _ => true

/-- Roles that carry the horizontal payload coordinate or channel label. -/
def isHorizontalCarrier : RouteRole → Bool
  | .horizontal | .active | .corner => true
  | .inactive | .vertical => false

/-- Roles that carry the vertical payload coordinate or channel label. -/
def isVerticalCarrier : RouteRole → Bool
  | .vertical | .active | .corner => true
  | .inactive | .horizontal => false

theorem eq_horizontal_iff_carriers {role : RouteRole} :
    role = .horizontal ↔
      role.isHorizontalCarrier = true ∧ role.isVerticalCarrier = false := by
  cases role <;> simp [isHorizontalCarrier, isVerticalCarrier]

theorem eq_vertical_iff_carriers {role : RouteRole} :
    role = .vertical ↔
      role.isHorizontalCarrier = false ∧ role.isVerticalCarrier = true := by
  cases role <;> simp [isHorizontalCarrier, isVerticalCarrier]

@[simp] theorem isConstrained_eq_false_iff {role : RouteRole} :
    role.isConstrained = false ↔ role = .inactive := by
  cases role <;> simp [isConstrained]

@[simp] theorem isConstrained_eq_true_iff {role : RouteRole} :
    role.isConstrained = true ↔ role ≠ .inactive := by
  cases role <;> simp [isConstrained]

theorem isHorizontal_primrec : Primrec isHorizontal :=
  Primrec.dom_finite _

theorem isVertical_primrec : Primrec isVertical :=
  Primrec.dom_finite _

theorem isActive_primrec : Primrec isActive :=
  Primrec.dom_finite _

theorem isCorner_primrec : Primrec isCorner :=
  Primrec.dom_finite _

end RouteRole

/-- Forget that an active routed cell is the distinguished source corner. -/
def eraseCorner : RouteRole → RouteRole
  | .corner => .active
  | role => role

@[simp] theorem eraseCorner_isHorizontalCarrier (role : RouteRole) :
    (eraseCorner role).isHorizontalCarrier = role.isHorizontalCarrier := by
  cases role <;> rfl

@[simp] theorem eraseCorner_isVerticalCarrier (role : RouteRole) :
    (eraseCorner role).isVerticalCarrier = role.isVerticalCarrier := by
  cases role <;> rfl

@[simp] theorem eraseCorner_eq_active_iff (role : RouteRole) :
    eraseCorner role = .active ↔ role = .active ∨ role = .corner := by
  cases role <;> simp [eraseCorner]

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

/-- Membership in the complete payload palette exposes all four edge colors. -/
theorem edge_mem_payloadPalette_of_mem_completePayloads
    {T : TileSet} {tile : WangTile} (htile : tile ∈ completePayloads T) :
    tile.n ∈ payloadPalette T ∧ tile.s ∈ payloadPalette T ∧
      tile.e ∈ payloadPalette T ∧ tile.w ∈ payloadPalette T := by
  rcases tile with ⟨n, s, e, w⟩
  have colors :
      (n ∈ payloadPalette T ∧ s ∈ payloadPalette T) ∧
        e ∈ payloadPalette T ∧ w ∈ payloadPalette T := by
    simpa [completePayloads, completePayloadsFromColors] using htile
  exact ⟨colors.1.1, colors.1.2, colors.2.1, colors.2.2⟩

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

/-- Every routed payload uses only colors from the complete payload palette. -/
theorem mem_completePayloads_of_mem_routedPayloads
    {S : RoutedScaffold} {T : TileSet} {seed base payload : WangTile}
    (hpayload : payload ∈ routedPayloads S T seed base) :
    payload ∈ completePayloads T := by
  rw [mem_routedPayloads_iff] at hpayload
  cases hrole : S.role base
  · simpa only [hrole] using hpayload
  · exact (show payload ∈ completePayloads T ∧ payload.w = payload.e from
      by simpa only [hrole] using hpayload).1
  · exact (show payload ∈ completePayloads T ∧ payload.s = payload.n from
      by simpa only [hrole] using hpayload).1
  · apply mem_completePayloads_of_mem
    simpa only [hrole] using hpayload
  · apply mem_completePayloads_of_mem
    exact (show payload ∈ T ∧ payload = seed from
      by simpa only [hrole] using hpayload).1

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

/-- A finite centered routed-product patch, separated into scaffold and payload
layers.  The concrete Robinson realization only has to construct these finite
objects; product matching and compactness are generic. -/
structure RoutedCombinedBoxLayerPatch
    (S : RoutedScaffold) (T : TileSet) (seed : WangTile) (r : Nat) where
  base : BoxPattern S.tiles r
  payload : Box r → WangTile
  base_valid : ValidBoxTiling S.tiles r base
  payload_mem : ∀ p : Box r,
    payload p ∈ routedPayloads S T seed (base p).1
  payload_hmatch : ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
    WangTile.HMatches (payload p)
      (payload ⟨(p.1.1 + 1, p.1.2), hp⟩)
  payload_vmatch : ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
    WangTile.VMatches (payload p)
      (payload ⟨(p.1.1, p.1.2 + 1), hp⟩)

/--
A routed finite box whose payload is prescribed only on constrained cells.

Inactive cells are deliberately left out of the local matching obligations;
`toRoutedCombinedBoxLayerPatch` fills them from the complete payload palette.
-/
structure RoutedCoreBoxLayerPatch
    (S : RoutedScaffold) (T : TileSet) (seed : WangTile) (r : Nat) where
  base : BoxPattern S.tiles r
  core : Box r → WangTile
  base_valid : ValidBoxTiling S.tiles r base
  core_mem : ∀ p : Box r,
    core p ∈ routedPayloads S T seed (base p).1
  core_hmatch :
    ∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
      (S.role (base p).1).isConstrained = true →
        (S.role (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1).isConstrained = true →
          WangTile.HMatches (core p)
            (core ⟨(p.1.1 + 1, p.1.2), hp⟩)
  core_vmatch :
    ∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
      (S.role (base p).1).isConstrained = true →
        (S.role (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1).isConstrained = true →
          WangTile.VMatches (core p)
            (core ⟨(p.1.1, p.1.2 + 1), hp⟩)

namespace RoutedCoreBoxLayerPatch

private def constrained
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {r : Nat}
    (patch : RoutedCoreBoxLayerPatch S T seed r) (p : Box r) : Bool :=
  (S.role (patch.base p).1).isConstrained

private theorem core_mem_completePayloads
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {r : Nat}
    (patch : RoutedCoreBoxLayerPatch S T seed r) (p : Box r) :
    patch.core p ∈ completePayloads T :=
  mem_completePayloads_of_mem_routedPayloads (patch.core_mem p)

private theorem colorFromNeighbor_mem
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {r : Nat}
    (patch : RoutedCoreBoxLayerPatch S T seed r)
    (neighbor : Option (Box r)) (edge : WangTile → Nat)
    (edge_mem : ∀ q, edge (patch.core q) ∈ payloadPalette T) :
    PayloadCompletion.colorFromNeighbor
      patch.constrained patch.core neighbor edge ∈ payloadPalette T := by
  cases neighbor with
  | none => exact zero_mem_payloadPalette T
  | some q =>
      by_cases hcore : patch.constrained q = true
      · simpa [PayloadCompletion.colorFromNeighbor, hcore] using edge_mem q
      · simp [PayloadCompletion.colorFromNeighbor, hcore,
          zero_mem_payloadPalette]

private theorem inactivePayloadAround_mem
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {r : Nat}
    (patch : RoutedCoreBoxLayerPatch S T seed r) (p : Box r) :
    PayloadCompletion.inactiveAround
      patch.constrained patch.core p ∈
      completePayloads T := by
  apply mk_mem_completePayloads
  · apply colorFromNeighbor_mem patch
    intro q
    exact (edge_mem_payloadPalette_of_mem_completePayloads
      (patch.core_mem_completePayloads q)).2.1
  · apply colorFromNeighbor_mem patch
    intro q
    exact (edge_mem_payloadPalette_of_mem_completePayloads
      (patch.core_mem_completePayloads q)).1
  · apply colorFromNeighbor_mem patch
    intro q
    exact (edge_mem_payloadPalette_of_mem_completePayloads
      (patch.core_mem_completePayloads q)).2.2.2
  · apply colorFromNeighbor_mem patch
    intro q
    exact (edge_mem_payloadPalette_of_mem_completePayloads
      (patch.core_mem_completePayloads q)).2.2.1

/-- Fill all inactive cells around a locally compatible routed core. -/
def toRoutedCombinedBoxLayerPatch
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {r : Nat}
    (patch : RoutedCoreBoxLayerPatch S T seed r) :
    RoutedCombinedBoxLayerPatch S T seed r where
  base := patch.base
  payload := PayloadCompletion.complete
    patch.constrained patch.core
  base_valid := patch.base_valid
  payload_mem := by
    intro p
    by_cases hcore : patch.constrained p = true
    · simpa [PayloadCompletion.complete, hcore] using
        patch.core_mem p
    · have hfalse : patch.constrained p = false :=
        Bool.eq_false_of_not_eq_true hcore
      have hrole : S.role (patch.base p).1 = .inactive := by
        exact RouteRole.isConstrained_eq_false_iff.mp hfalse
      simpa [PayloadCompletion.complete, hfalse,
        routedPayloads, hrole] using
        patch.inactivePayloadAround_mem p
  payload_hmatch := by
    exact PayloadCompletion.complete_hmatch
      patch.core_hmatch
  payload_vmatch := by
    exact PayloadCompletion.complete_vmatch
      patch.core_vmatch

end RoutedCoreBoxLayerPatch

namespace RoutedCombinedBoxLayerPatch

theorem product_mem
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {r : Nat}
    (patch : RoutedCombinedBoxLayerPatch S T seed r) (p : Box r) :
    WangTile.product (patch.base p).1 (patch.payload p) ∈
      combineWithRoutedScaffold S T seed := by
  rw [mem_combineWithRoutedScaffold_iff]
  exact ⟨(patch.base p).1, (patch.base p).2, patch.payload p,
    patch.payload_mem p, rfl⟩

/-- Assemble the separated routed layers into an ordinary finite box. -/
def toBoxPattern
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {r : Nat}
    (patch : RoutedCombinedBoxLayerPatch S T seed r) :
    BoxPattern (combineWithRoutedScaffold S T seed) r :=
  fun p => ⟨WangTile.product (patch.base p).1 (patch.payload p),
    patch.product_mem p⟩

theorem validBoxTiling_toBoxPattern
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {r : Nat}
    (patch : RoutedCombinedBoxLayerPatch S T seed r) :
    ValidBoxTiling (combineWithRoutedScaffold S T seed) r
      patch.toBoxPattern := by
  constructor
  · intro p hp
    exact (WangTile.HMatches_product_iff
      (patch.base p).1 (patch.payload p)
      (patch.base ⟨(p.1.1 + 1, p.1.2), hp⟩).1
      (patch.payload ⟨(p.1.1 + 1, p.1.2), hp⟩)).2
        ⟨patch.base_valid.1 p hp, patch.payload_hmatch p hp⟩
  · intro p hp
    exact (WangTile.VMatches_product_iff
      (patch.base p).1 (patch.payload p)
      (patch.base ⟨(p.1.1, p.1.2 + 1), hp⟩).1
      (patch.payload ⟨(p.1.1, p.1.2 + 1), hp⟩)).2
        ⟨patch.base_valid.2 p hp, patch.payload_vmatch p hp⟩

theorem tileableBox
    {S : RoutedScaffold} {T : TileSet} {seed : WangTile} {r : Nat}
    (patch : RoutedCombinedBoxLayerPatch S T seed r) :
    TileableBox (combineWithRoutedScaffold S T seed) r :=
  ⟨patch.toBoxPattern, patch.validBoxTiling_toBoxPattern⟩

end RoutedCombinedBoxLayerPatch

/-- Finite-patch form of the backward routed scaffold construction. -/
def HasRoutedCombinedBoxLayerPatches (S : RoutedScaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    (∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n) →
      ∀ r : Nat, Nonempty (RoutedCombinedBoxLayerPatch S T seed r)

/-- Core-patch form of the backward routed scaffold construction. -/
def HasRoutedCoreBoxLayerPatches (S : RoutedScaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    (∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n) →
      ∀ r : Nat, Nonempty (RoutedCoreBoxLayerPatch S T seed r)

/-- Locally compatible constrained cores supply the required full patches. -/
theorem hasRoutedCombinedBoxLayerPatches_of_coreBoxLayerPatches
    {S : RoutedScaffold} (cores : HasRoutedCoreBoxLayerPatches S) :
    HasRoutedCombinedBoxLayerPatches S := by
  intro T seed squares r
  rcases cores T seed squares r with ⟨core⟩
  exact ⟨core.toRoutedCombinedBoxLayerPatch⟩

/-- The abstract property required of a channel-aware routed scaffold. -/
def IsRoutedScaffold (S : RoutedScaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    TilesPlane (combineWithRoutedScaffold S T seed) ↔
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n

/-- Backward half of the routed scaffold equivalence. -/
def RealizesRoutedFixedCornerSquares (S : RoutedScaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    (∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n) →
      TilesPlane (combineWithRoutedScaffold S T seed)

/-- Forward half of the routed scaffold equivalence. -/
def ForcesRoutedFixedCornerSquares (S : RoutedScaffold) : Prop :=
  ∀ {T : TileSet} {seed : WangTile},
    TilesPlane (combineWithRoutedScaffold S T seed) →
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n

/-- Finite routed layer patches realize every family of fixed-corner squares
by Wang compactness. -/
theorem realizesRoutedFixedCornerSquares_of_combinedBoxLayerPatches
    {S : RoutedScaffold}
    (patches : HasRoutedCombinedBoxLayerPatches S) :
    RealizesRoutedFixedCornerSquares S := by
  intro T seed hsquares
  apply tilesPlane_of_all_tileableBoxes
  intro r
  rcases patches T seed hsquares r with ⟨patch⟩
  exact patch.tileableBox

theorem isRoutedScaffold_of_realizes_of_forces
    {S : RoutedScaffold}
    (realizes : RealizesRoutedFixedCornerSquares S)
    (forces : ForcesRoutedFixedCornerSquares S) :
    IsRoutedScaffold S := by
  intro T seed
  exact ⟨forces, realizes T seed⟩

theorem isRoutedScaffold_of_combinedBoxLayerPatches_of_forces
    {S : RoutedScaffold}
    (patches : HasRoutedCombinedBoxLayerPatches S)
    (forces : ForcesRoutedFixedCornerSquares S) :
    IsRoutedScaffold S :=
  isRoutedScaffold_of_realizes_of_forces
    (realizesRoutedFixedCornerSquares_of_combinedBoxLayerPatches patches)
    forces

/-- Correctness theorem exposed by any certified routed scaffold. -/
theorem routedScaffold_reduction_correct {S : RoutedScaffold}
    (hS : IsRoutedScaffold S) (T : TileSet) (seed : WangTile) :
    TilesPlane (combineWithRoutedScaffold S T seed) ↔
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n :=
  hS T seed

end LeanWang
