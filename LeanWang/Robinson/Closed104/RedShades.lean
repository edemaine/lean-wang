/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.QuarterGeometry

/-!
The light/dark red-wire decoration required before Robinson obstruction
signals are added.

The CIRM construction first duplicates the red color and requires crossing red
wires to have opposite shades. This layer records a shade on every red path
edge of a corrected quarter tile, propagates it along each path, and separates
the two paths at a crossing.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShades

open Figure16 Quarters QuarterGeometry QuarterRegrouping

set_option maxRecDepth 20000

inductive Shade where
  | light
  | dark
deriving DecidableEq, Repr

namespace Shade

def all : List Shade := [.light, .dark]

@[simp] theorem mem_all (shade : Shade) : shade ∈ all := by
  cases shade <;> decide

def code : Shade → Nat
  | .light => 1
  | .dark => 2

def opposite : Shade → Shade
  | .light => .dark
  | .dark => .light

@[simp] theorem opposite_opposite (shade : Shade) :
    shade.opposite.opposite = shade := by
  cases shade <;> rfl

theorem eq_opposite_of_ne {first second : Shade} (hne : first ≠ second) :
    second = first.opposite := by
  cases first <;> cases second <;> simp_all [opposite]

theorem code_injective : Function.Injective code := by
  intro first second heq
  cases first <;> cases second <;> simp [code] at heq ⊢

end Shade

/-- Optional shade carried by each edge of one quarter tile. -/
structure State where
  west : Option Shade
  east : Option Shade
  south : Option Shade
  north : Option Shade
deriving DecidableEq, Repr

namespace State

def edgeValues : List (Option Shade) := none :: Shade.all.map some

def all : List State :=
  edgeValues.flatMap fun west =>
    edgeValues.flatMap fun east =>
      edgeValues.flatMap fun south =>
        edgeValues.map fun north => ⟨west, east, south, north⟩

@[simp] theorem mem_edgeValues (value : Option Shade) : value ∈ edgeValues := by
  rcases value with _ | shade
  · simp [edgeValues]
  · simp [edgeValues]

@[simp] theorem mem_all (state : State) : state ∈ all := by
  rcases state with ⟨west, east, south, north⟩
  simp [all]

def edgeCode : Option Shade → Nat
  | none => 0
  | some shade => shade.code

theorem edgeCode_injective : Function.Injective edgeCode := by
  intro first second heq
  rcases first with _ | first <;> rcases second with _ | second
  · rfl
  · cases second <;> simp [edgeCode, Shade.code] at heq
  · cases first <;> simp [edgeCode, Shade.code] at heq
  · exact congrArg some (Shade.code_injective (by
      simpa only [edgeCode] using heq))

def tile (state : State) : WangTile where
  n := edgeCode state.north
  s := edgeCode state.south
  e := edgeCode state.east
  w := edgeCode state.west

theorem tile_injective : Function.Injective tile := by
  intro first second heq
  rcases first with ⟨firstWest, firstEast, firstSouth, firstNorth⟩
  rcases second with ⟨secondWest, secondEast, secondSouth, secondNorth⟩
  have hwest := edgeCode_injective (congrArg WangTile.w heq)
  have heast := edgeCode_injective (congrArg WangTile.e heq)
  have hsouth := edgeCode_injective (congrArg WangTile.s heq)
  have hnorth := edgeCode_injective (congrArg WangTile.n heq)
  change firstWest = secondWest at hwest
  change firstEast = secondEast at heast
  change firstSouth = secondSouth at hsouth
  change firstNorth = secondNorth at hnorth
  subst secondWest
  subst secondEast
  subst secondSouth
  subst secondNorth
  rfl

end State

/-- Red corner path entering the west edge of this quarter. -/
def cornerWest (component : Thick) (quadrant : Quadrant) : Bool :=
  decide ((component = .c ∧ quadrant = .northwest) ∨
    (component = .d ∧ quadrant = .southwest))

/-- Red corner path entering the east edge of this quarter. -/
def cornerEast (component : Thick) (quadrant : Quadrant) : Bool :=
  decide ((component = .a ∧ quadrant = .southeast) ∨
    (component = .b ∧ quadrant = .northeast))

/-- Red corner path entering the south edge of this quarter. -/
def cornerSouth (component : Thick) (quadrant : Quadrant) : Bool :=
  decide ((component = .a ∧ quadrant = .southeast) ∨
    (component = .d ∧ quadrant = .southwest))

/-- Red corner path entering the north edge of this quarter. -/
def cornerNorth (component : Thick) (quadrant : Quadrant) : Bool :=
  decide ((component = .b ∧ quadrant = .northeast) ∨
    (component = .c ∧ quadrant = .northwest))

def hasHorizontal (component : Thick) (quadrant : Quadrant) : Bool :=
  redHorizontalAt component quadrant.yBit

def hasVertical (component : Thick) (quadrant : Quadrant) : Bool :=
  redVerticalAt component quadrant.xBit

def hasWest (component : Thick) (quadrant : Quadrant) : Bool :=
  hasHorizontal component quadrant || cornerWest component quadrant

def hasEast (component : Thick) (quadrant : Quadrant) : Bool :=
  hasHorizontal component quadrant || cornerEast component quadrant

def hasSouth (component : Thick) (quadrant : Quadrant) : Bool :=
  hasVertical component quadrant || cornerSouth component quadrant

def hasNorth (component : Thick) (quadrant : Quadrant) : Bool :=
  hasVertical component quadrant || cornerNorth component quadrant

def optionPresent (value : Option Shade) : Bool := value.isSome

/-- Local rule with the thick component made explicit for proof reuse. -/
def allowedFor (component : Thick) (quadrant : Quadrant) (state : State) : Bool :=
  decide (optionPresent state.west = hasWest component quadrant) &&
    decide (optionPresent state.east = hasEast component quadrant) &&
    decide (optionPresent state.south = hasSouth component quadrant) &&
    decide (optionPresent state.north = hasNorth component quadrant) &&
    (if hasHorizontal component quadrant then decide (state.west = state.east)
      else true) &&
    (if hasVertical component quadrant then decide (state.south = state.north)
      else true) &&
    (if cornerEast component quadrant && cornerSouth component quadrant then
      decide (state.east = state.south) else true) &&
    (if cornerEast component quadrant && cornerNorth component quadrant then
      decide (state.east = state.north) else true) &&
    (if cornerWest component quadrant && cornerSouth component quadrant then
      decide (state.west = state.south) else true) &&
    (if cornerWest component quadrant && cornerNorth component quadrant then
      decide (state.west = state.north) else true) &&
    (if hasHorizontal component quadrant && hasVertical component quadrant then
      decide (state.west ≠ state.south) else true)

/-- Constructor form of the local red-shade rule. -/
theorem allowedFor_of {component : Thick} {quadrant : Quadrant} {state : State}
    (hwest : state.west.isSome = hasWest component quadrant)
    (heast : state.east.isSome = hasEast component quadrant)
    (hsouth : state.south.isSome = hasSouth component quadrant)
    (hnorth : state.north.isSome = hasNorth component quadrant)
    (hhorizontal : hasHorizontal component quadrant = true →
      state.west = state.east)
    (hvertical : hasVertical component quadrant = true →
      state.south = state.north)
    (heastSouth : cornerEast component quadrant = true →
      cornerSouth component quadrant = true → state.east = state.south)
    (heastNorth : cornerEast component quadrant = true →
      cornerNorth component quadrant = true → state.east = state.north)
    (hwestSouth : cornerWest component quadrant = true →
      cornerSouth component quadrant = true → state.west = state.south)
    (hwestNorth : cornerWest component quadrant = true →
      cornerNorth component quadrant = true → state.west = state.north)
    (hcrossing : hasHorizontal component quadrant = true →
      hasVertical component quadrant = true → state.west ≠ state.south) :
    allowedFor component quadrant state = true := by
  simp only [allowedFor, Bool.and_eq_true, decide_eq_true_eq, optionPresent]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwest, heast⟩, hsouth⟩, hnorth⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · split <;> simp_all
  · split <;> simp_all
  · split <;> simp_all
  · split <;> simp_all
  · split <;> simp_all
  · split <;> simp_all
  · split <;> simp_all

/-- Local red-path incidence, propagation, corner, and crossing rules. -/
def locallyAllowed (site : QuarterIndex) (state : State) : Bool :=
  allowedFor (components site.1).2.1 site.2 state

theorem horizontal_eq_of_allowedFor {component : Thick} {quadrant : Quadrant}
    {state : State} (hallowed : allowedFor component quadrant state = true)
    (hhorizontal : hasHorizontal component quadrant = true) :
    state.west = state.east := by
  simp [allowedFor, hhorizontal] at hallowed
  aesop

theorem vertical_eq_of_allowedFor {component : Thick} {quadrant : Quadrant}
    {state : State} (hallowed : allowedFor component quadrant state = true)
    (hvertical : hasVertical component quadrant = true) :
    state.south = state.north := by
  simp [allowedFor, hvertical] at hallowed
  aesop

theorem horizontal_eq_of_allowed {site : QuarterIndex} {state : State}
    (hallowed : locallyAllowed site state = true)
    (hhorizontal : hasHorizontal (components site.1).2.1 site.2 = true) :
    state.west = state.east :=
  horizontal_eq_of_allowedFor hallowed hhorizontal

theorem vertical_eq_of_allowed {site : QuarterIndex} {state : State}
    (hallowed : locallyAllowed site state = true)
    (hvertical : hasVertical (components site.1).2.1 site.2 = true) :
    state.south = state.north :=
  vertical_eq_of_allowedFor hallowed hvertical

theorem crossing_opposite_of_allowed {site : QuarterIndex} {state : State}
    (hallowed : locallyAllowed site state = true)
    (hhorizontal : hasHorizontal (components site.1).2.1 site.2 = true)
    (hvertical : hasVertical (components site.1).2.1 site.2 = true) :
    state.west ≠ state.south := by
  simp [locallyAllowed, allowedFor, hhorizontal, hvertical] at hallowed
  aesop

theorem east_present_of_allowedFor {component : Thick} {quadrant : Quadrant}
    {state : State} (hallowed : allowedFor component quadrant state = true)
    (heast : hasEast component quadrant = true) :
    state.east.isSome = true := by
  simp [allowedFor, heast] at hallowed
  aesop

theorem west_present_of_allowedFor {component : Thick} {quadrant : Quadrant}
    {state : State} (hallowed : allowedFor component quadrant state = true)
    (hwest : hasWest component quadrant = true) :
    state.west.isSome = true := by
  simp [allowedFor, hwest] at hallowed
  aesop

theorem south_present_of_allowedFor {component : Thick} {quadrant : Quadrant}
    {state : State} (hallowed : allowedFor component quadrant state = true)
    (hsouth : hasSouth component quadrant = true) :
    state.south.isSome = true := by
  simp [allowedFor, hsouth] at hallowed
  aesop

theorem west_north_corner_eq_of_allowedFor {component : Thick}
    {quadrant : Quadrant} {state : State}
    (hallowed : allowedFor component quadrant state = true)
    (hwest : cornerWest component quadrant = true)
    (hnorth : cornerNorth component quadrant = true) :
    state.west = state.north := by
  cases component <;> cases quadrant <;>
    simp_all [allowedFor, cornerWest, cornerNorth]

theorem west_south_corner_eq_of_allowedFor {component : Thick}
    {quadrant : Quadrant} {state : State}
    (hallowed : allowedFor component quadrant state = true)
    (hwest : cornerWest component quadrant = true)
    (hsouth : cornerSouth component quadrant = true) :
    state.west = state.south := by
  cases component <;> cases quadrant <;>
    simp_all [allowedFor, cornerWest, cornerSouth]

theorem east_north_corner_eq_of_allowedFor {component : Thick}
    {quadrant : Quadrant} {state : State}
    (hallowed : allowedFor component quadrant state = true)
    (heast : cornerEast component quadrant = true)
    (hnorth : cornerNorth component quadrant = true) :
    state.east = state.north := by
  cases component <;> cases quadrant <;>
    simp_all [allowedFor, cornerEast, cornerNorth]

theorem crossing_opposite_of_allowedFor {component : Thick}
    {quadrant : Quadrant} {state : State}
    (hallowed : allowedFor component quadrant state = true)
    (hhorizontal : hasHorizontal component quadrant = true)
    (hvertical : hasVertical component quadrant = true) :
    state.west ≠ state.south := by
  simp [allowedFor, hhorizontal, hvertical] at hallowed
  aesop

theorem east_present_of_allowed {site : QuarterIndex} {state : State}
    (hallowed : locallyAllowed site state = true)
    (heast : hasEast (components site.1).2.1 site.2 = true) :
    state.east.isSome = true := by
  exact east_present_of_allowedFor hallowed heast

theorem east_south_corner_eq_of_allowed {site : QuarterIndex} {state : State}
    (hallowed : locallyAllowed site state = true)
    (heast : cornerEast (components site.1).2.1 site.2 = true)
    (hsouth : cornerSouth (components site.1).2.1 site.2 = true) :
    state.east = state.south := by
  rcases site with ⟨index, quadrant⟩
  generalize hcomponent : (components index).2.1 = component at *
  cases component <;> cases quadrant <;>
    simp_all [locallyAllowed, allowedFor, cornerEast, cornerSouth]

theorem east_north_corner_eq_of_allowed {site : QuarterIndex} {state : State}
    (hallowed : locallyAllowed site state = true)
    (heast : cornerEast (components site.1).2.1 site.2 = true)
    (hnorth : cornerNorth (components site.1).2.1 site.2 = true) :
    state.east = state.north := by
  rcases site with ⟨index, quadrant⟩
  generalize hcomponent : (components index).2.1 = component at *
  cases component <;> cases quadrant <;>
    simp_all [locallyAllowed, allowedFor, cornerEast, cornerNorth]

theorem west_south_corner_eq_of_allowed {site : QuarterIndex} {state : State}
    (hallowed : locallyAllowed site state = true)
    (hwest : cornerWest (components site.1).2.1 site.2 = true)
    (hsouth : cornerSouth (components site.1).2.1 site.2 = true) :
    state.west = state.south := by
  rcases site with ⟨index, quadrant⟩
  generalize hcomponent : (components index).2.1 = component at *
  cases component <;> cases quadrant <;>
    simp_all [locallyAllowed, allowedFor, cornerWest, cornerSouth]

theorem west_north_corner_eq_of_allowed {site : QuarterIndex} {state : State}
    (hallowed : locallyAllowed site state = true)
    (hwest : cornerWest (components site.1).2.1 site.2 = true)
    (hnorth : cornerNorth (components site.1).2.1 site.2 = true) :
    state.west = state.north := by
  rcases site with ⟨index, quadrant⟩
  generalize hcomponent : (components index).2.1 = component at *
  cases component <;> cases quadrant <;>
    simp_all [locallyAllowed, allowedFor, cornerWest, cornerNorth]

abbrev Site := QuarterIndex × State

def allSites : List Site :=
  Quarters.all.flatMap fun site =>
    (State.all.filter fun state => locallyAllowed site state).map fun state =>
      (site, state)

@[simp] theorem mem_allSites_iff (site : Site) :
    site ∈ allSites ↔ locallyAllowed site.1 site.2 = true := by
  rcases site with ⟨quarter, state⟩
  simp [allSites, Quarters.mem_all]

def tile (site : Site) : WangTile :=
  WangTile.product (quarterTile site.1) (State.tile site.2)

theorem tile_injective : Function.Injective tile := by
  intro first second heq
  change WangTile.product (quarterTile first.1) (State.tile first.2) =
    WangTile.product (quarterTile second.1) (State.tile second.2) at heq
  have hpair := product_eq_iff.mp heq
  apply Prod.ext
  · exact quarterTile_injective hpair.1
  · exact State.tile_injective hpair.2

@[irreducible] def tileSet : TileSet := allSites.map tile

theorem tile_mem (site : Site) (hallowed : locallyAllowed site.1 site.2 = true) :
    tile site ∈ tileSet := by
  unfold tileSet
  exact List.mem_map.2 ⟨site, (mem_allSites_iff site).2 hallowed, rfl⟩

theorem exists_site_of_mem {wang : WangTile} (hwang : wang ∈ tileSet) :
    ∃ site : Site, site ∈ allSites ∧ tile site = wang := by
  unfold tileSet at hwang
  rcases List.mem_map.1 hwang with ⟨site, hsite, rfl⟩
  exact ⟨site, hsite, rfl⟩

@[irreducible] noncomputable def decode (wang : TileIn tileSet) : Site :=
  Classical.choose (exists_site_of_mem wang.2)

theorem decode_mem (wang : TileIn tileSet) : decode wang ∈ allSites := by
  unfold decode
  exact (Classical.choose_spec (exists_site_of_mem wang.2)).1

theorem decode_tile (wang : TileIn tileSet) : tile (decode wang) = wang.1 := by
  unfold decode
  exact (Classical.choose_spec (exists_site_of_mem wang.2)).2

theorem decode_tile_site (site : Site) (hsite : tile site ∈ tileSet) :
    decode ⟨tile site, hsite⟩ = site :=
  tile_injective (decode_tile ⟨tile site, hsite⟩)

theorem decode_allowed (wang : TileIn tileSet) :
    locallyAllowed (decode wang).1 (decode wang).2 = true :=
  (mem_allSites_iff (decode wang)).1 (decode_mem wang)

set_option linter.style.nativeDecide false in
/-- Finite audit that every corrected quarter site admits a local shade state. -/
theorem allowedStateAudit (site : QuarterIndex) :
    State.all.any (fun state => locallyAllowed site state) = true := by
  rcases site with ⟨index, quadrant⟩
  revert index
  cases quadrant <;> native_decide

/-- Every corrected quarter site admits at least one local shade state. -/
theorem exists_allowed_state (site : QuarterIndex) :
    ∃ state : State, locallyAllowed site state = true := by
  rcases List.any_eq_true.1 (allowedStateAudit site) with
    ⟨state, _hstate, hallowed⟩
  exact ⟨state, hallowed⟩

abbrev ShadePlane := Int × Int → State

def sitePlane (x : Int × Int → TileIn tileSet) : Int × Int → Site :=
  fun p => decode (x p)

def quarterPlane (x : Int × Int → TileIn tileSet) : QuarterPlane :=
  fun p => (sitePlane x p).1

def shadePlane (x : Int × Int → TileIn tileSet) : ShadePlane :=
  fun p => (sitePlane x p).2

theorem plane_locallyAllowed (x : Int × Int → TileIn tileSet)
    (p : Int × Int) :
    locallyAllowed (quarterPlane x p) (shadePlane x p) = true :=
  decode_allowed (x p)

/-- Matching shaded tiles project to matching corrected quarter tiles. -/
theorem quarterPlane_valid {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) :
    ValidQuarterPlane (quarterPlane x) := by
  constructor
  · intro p
    have hproduct : WangTile.HMatches
        (tile (sitePlane x p))
        (tile (sitePlane x (p.1 + 1, p.2))) := by
      change WangTile.HMatches (tile (decode (x p)))
        (tile (decode (x (p.1 + 1, p.2))))
      rw [decode_tile, decode_tile]
      exact hx.1 p
    exact (WangTile.HMatches_product_iff _ _ _ _).1 hproduct |>.1
  · intro p
    have hproduct : WangTile.VMatches
        (tile (sitePlane x p))
        (tile (sitePlane x (p.1, p.2 + 1))) := by
      change WangTile.VMatches (tile (decode (x p)))
        (tile (decode (x (p.1, p.2 + 1))))
      rw [decode_tile, decode_tile]
      exact hx.2 p
    exact (WangTile.VMatches_product_iff _ _ _ _).1 hproduct |>.1

/-- Matching shaded tiles propagate their shade labels across path edges. -/
theorem shadePlane_matches {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) :
    (∀ p : Int × Int,
      WangTile.HMatches (State.tile (shadePlane x p))
        (State.tile (shadePlane x (p.1 + 1, p.2)))) ∧
      ∀ p : Int × Int,
        WangTile.VMatches (State.tile (shadePlane x p))
          (State.tile (shadePlane x (p.1, p.2 + 1))) := by
  constructor
  · intro p
    have hproduct : WangTile.HMatches
        (tile (sitePlane x p))
        (tile (sitePlane x (p.1 + 1, p.2))) := by
      change WangTile.HMatches (tile (decode (x p)))
        (tile (decode (x (p.1 + 1, p.2))))
      rw [decode_tile, decode_tile]
      exact hx.1 p
    exact (WangTile.HMatches_product_iff _ _ _ _).1 hproduct |>.2
  · intro p
    have hproduct : WangTile.VMatches
        (tile (sitePlane x p))
        (tile (sitePlane x (p.1, p.2 + 1))) := by
      change WangTile.VMatches (tile (decode (x p)))
        (tile (decode (x (p.1, p.2 + 1))))
      rw [decode_tile, decode_tile]
      exact hx.2 p
    exact (WangTile.VMatches_product_iff _ _ _ _).1 hproduct |>.2

theorem shadePlane_hmatch {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) (p : Int × Int) :
    (shadePlane x p).east =
      (shadePlane x (p.1 + 1, p.2)).west := by
  apply State.edgeCode_injective
  simpa [WangTile.HMatches, State.tile] using (shadePlane_matches hx).1 p

theorem shadePlane_vmatch {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) (p : Int × Int) :
    (shadePlane x p).north =
      (shadePlane x (p.1, p.2 + 1)).south := by
  apply State.edgeCode_injective
  simpa [WangTile.VMatches, State.tile] using (shadePlane_matches hx).2 p

end RedShades
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
