/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104QuarterGeometry

/-!
The finite Robinson obstruction-signal layer.

A signal is directed east/west on horizontal edges and north/south on vertical
edges. Away from a red border it is transmitted unchanged. At a red border,
the outer edge must carry a signal, while the inner edge may absorb a signal
but cannot emit one. These are Robinson's Section 7 local rules.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals

open Figure16 Quarters QuarterGeometry QuarterRegrouping

set_option maxRecDepth 20000

/-- Direction relative to the positive coordinate direction of an edge. -/
inductive Flow where
  | none
  | forward
  | backward
deriving DecidableEq, Repr

namespace Flow

def all : List Flow := [.none, .forward, .backward]

@[simp] theorem mem_all (flow : Flow) : flow ∈ all := by
  cases flow <;> decide

def code : Flow → Nat
  | .none => 0
  | .forward => 1
  | .backward => 2

theorem code_injective : Function.Injective code := by
  intro first second heq
  cases first <;> cases second <;> simp [code] at heq ⊢

end Flow

/-- Directed obstruction signals on the four edges of one quarter tile. -/
structure State where
  west : Flow
  east : Flow
  south : Flow
  north : Flow
deriving DecidableEq, Repr

namespace State

def all : List State :=
  Flow.all.flatMap fun west =>
    Flow.all.flatMap fun east =>
      Flow.all.flatMap fun south =>
        Flow.all.map fun north => ⟨west, east, south, north⟩

@[simp] theorem mem_all (state : State) : state ∈ all := by
  rcases state with ⟨west, east, south, north⟩
  simp [all]

def tile (state : State) : WangTile where
  n := state.north.code
  s := state.south.code
  e := state.east.code
  w := state.west.code

end State

/-- Which side of a vertical red border is the board interior. -/
inductive HorizontalInterior where
  | west
  | east
deriving DecidableEq, Repr

/-- Which side of a horizontal red border is the board interior. -/
inductive VerticalInterior where
  | south
  | north
deriving DecidableEq, Repr

/-- Vertical red boundary through a quarter, if any. -/
def verticalInterior? (component : Thick) (quadrant : Quadrant) :
    Option HorizontalInterior :=
  match component, quadrant with
  | .a, .southeast | .b, .northeast => some .east
  | .c, .northwest | .d, .southwest => some .west
  | component, quadrant =>
      if redVerticalAt component quadrant.xBit then
        if quadrant.xBit then some .east else some .west
      else none

/-- Horizontal red boundary through a quarter, if any. -/
def horizontalInterior? (component : Thick) (quadrant : Quadrant) :
    Option VerticalInterior :=
  match component, quadrant with
  | .a, .southeast | .d, .southwest => some .south
  | .b, .northeast | .c, .northwest => some .north
  | component, quadrant =>
      if redHorizontalAt component quadrant.yBit then
        if quadrant.yBit then some .north else some .south
      else none

/-- Horizontal transmission and vertical-red-boundary endpoint rule. -/
def horizontalAllowed (interior : Option HorizontalInterior)
    (state : State) : Bool :=
  match interior with
  | none => decide (state.west = state.east)
  | some .east =>
      decide (state.west ≠ .none ∧ state.east ≠ .forward)
  | some .west =>
      decide (state.east ≠ .none ∧ state.west ≠ .backward)

/-- Vertical transmission and horizontal-red-boundary endpoint rule. -/
def verticalAllowed (interior : Option VerticalInterior)
    (state : State) : Bool :=
  match interior with
  | none => decide (state.south = state.north)
  | some .north =>
      decide (state.south ≠ .none ∧ state.north ≠ .forward)
  | some .south =>
      decide (state.north ≠ .none ∧ state.south ≠ .backward)

/-- Robinson's local signal rule at one corrected quarter site. -/
def locallyAllowed (site : QuarterIndex) (state : State) : Bool :=
  let component := (components site.1).2.1
  horizontalAllowed (verticalInterior? component site.2) state &&
    verticalAllowed (horizontalInterior? component site.2) state

abbrev Site := QuarterIndex × State

def allSites : List Site :=
  Quarters.all.flatMap fun site =>
    (State.all.filter fun state => locallyAllowed site state).map fun state =>
      (site, state)

@[simp] theorem mem_allSites_iff (site : Site) :
    site ∈ allSites ↔ locallyAllowed site.1 site.2 = true := by
  rcases site with ⟨quarter, state⟩
  simp [allSites, Quarters.mem_all]

/-- Layer a quarter tile with its directed signal edges. -/
def tile (site : Site) : WangTile :=
  WangTile.product (quarterTile site.1) (State.tile site.2)

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

theorem decode_mem (wang : TileIn tileSet) : decode wang ∈ allSites :=
  by
    unfold decode
    exact (Classical.choose_spec (exists_site_of_mem wang.2)).1

theorem decode_tile (wang : TileIn tileSet) : tile (decode wang) = wang.1 :=
  by
    unfold decode
    exact (Classical.choose_spec (exists_site_of_mem wang.2)).2

theorem decode_allowed (wang : TileIn tileSet) :
    locallyAllowed (decode wang).1 (decode wang).2 = true :=
  (mem_allSites_iff (decode wang)).1 (decode_mem wang)

abbrev SignalPlane := Int × Int → State

def sitePlane (x : Int × Int → TileIn tileSet) : Int × Int → Site :=
  fun p => decode (x p)

def quarterPlane (x : Int × Int → TileIn tileSet) : QuarterPlane :=
  fun p => (sitePlane x p).1

def signalPlane (x : Int × Int → TileIn tileSet) : SignalPlane :=
  fun p => (sitePlane x p).2

theorem plane_locallyAllowed (x : Int × Int → TileIn tileSet)
    (p : Int × Int) :
    locallyAllowed (quarterPlane x p) (signalPlane x p) = true :=
  decode_allowed (x p)

/-- Matching decorated tiles project to matching corrected quarter tiles. -/
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

/-- Matching decorated tiles also match their directed signal edges. -/
theorem signalPlane_matches {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) :
    (∀ p : Int × Int,
      WangTile.HMatches (State.tile (signalPlane x p))
        (State.tile (signalPlane x (p.1 + 1, p.2)))) ∧
      ∀ p : Int × Int,
        WangTile.VMatches (State.tile (signalPlane x p))
          (State.tile (signalPlane x (p.1, p.2 + 1))) := by
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

end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
