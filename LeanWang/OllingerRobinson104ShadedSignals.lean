/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShades
import LeanWang.OllingerRobinson104Signals

/-!
Robinson obstruction signals over the light/dark red-wire decoration.

Only light red paths are treated as square borders. Dark paths are transparent
to obstruction signals, which is the local mechanism behind the noncrossing
light-square family used by the CIRM reduction.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSignals

open Figure16 Quarters QuarterGeometry QuarterRegrouping

set_option maxRecDepth 20000

/-- Shade of the vertical red path through a quarter, if present. -/
def verticalShade? (state : RedShades.State) : Option RedShades.Shade :=
  match state.south with
  | some shade => some shade
  | none => state.north

/-- Shade of the horizontal red path through a quarter, if present. -/
def horizontalShade? (state : RedShades.State) : Option RedShades.Shade :=
  match state.west with
  | some shade => some shade
  | none => state.east

/-- Selected vertical-border rule with the component made explicit. -/
def selectedVerticalFor (component : Thick) (quadrant : Quadrant)
    (state : RedShades.State) : Option Signals.HorizontalInterior :=
  if verticalShade? state = some .light then
    Signals.verticalInterior? component quadrant
  else none

/-- Selected horizontal-border rule with the component made explicit. -/
def selectedHorizontalFor (component : Thick) (quadrant : Quadrant)
    (state : RedShades.State) : Option Signals.VerticalInterior :=
  if horizontalShade? state = some .light then
    Signals.horizontalInterior? component quadrant
  else none

/-- A vertical red path is an obstruction border exactly when it is light. -/
def selectedVerticalInterior? (base : RedShades.Site) :
    Option Signals.HorizontalInterior :=
  selectedVerticalFor (components base.1.1).2.1 base.1.2 base.2

/-- A horizontal red path is an obstruction border exactly when it is light. -/
def selectedHorizontalInterior? (base : RedShades.Site) :
    Option Signals.VerticalInterior :=
  selectedHorizontalFor (components base.1.1).2.1 base.1.2 base.2

@[simp] theorem selectedVerticalInterior_of_light {base : RedShades.Site}
    (hlight : verticalShade? base.2 = some .light) :
    selectedVerticalInterior? base =
      Signals.verticalInterior? (components base.1.1).2.1 base.1.2 := by
  simp [selectedVerticalInterior?, selectedVerticalFor, hlight]

@[simp] theorem selectedVerticalInterior_of_not_light {base : RedShades.Site}
    (hlight : verticalShade? base.2 ≠ some .light) :
    selectedVerticalInterior? base = none := by
  simp [selectedVerticalInterior?, selectedVerticalFor, hlight]

@[simp] theorem selectedHorizontalInterior_of_light {base : RedShades.Site}
    (hlight : horizontalShade? base.2 = some .light) :
    selectedHorizontalInterior? base =
      Signals.horizontalInterior? (components base.1.1).2.1 base.1.2 := by
  simp [selectedHorizontalInterior?, selectedHorizontalFor, hlight]

theorem southwest_selected_of_allowed {state : RedShades.State}
    (hallowed : RedShades.allowedFor .b .northeast state = true)
    (hshade : state.east = some .light) :
    selectedVerticalFor .b .northeast state = some .east ∧
      selectedHorizontalFor .b .northeast state = some .north := by
  rcases state with ⟨west, east, south, north⟩
  simp [RedShades.allowedFor, RedShades.hasWest, RedShades.hasEast,
    RedShades.hasSouth, RedShades.hasNorth, RedShades.hasHorizontal,
    RedShades.hasVertical, RedShades.cornerWest, RedShades.cornerEast,
    RedShades.cornerSouth, RedShades.cornerNorth, RedShades.optionPresent,
    selectedVerticalFor, selectedHorizontalFor, verticalShade?, horizontalShade?,
    Signals.verticalInterior?, Signals.horizontalInterior?] at hallowed hshade ⊢
  aesop

theorem southeast_selected_of_allowed {state : RedShades.State}
    (hallowed : RedShades.allowedFor .c .northwest state = true)
    (hshade : state.west = some .light) :
    selectedVerticalFor .c .northwest state = some .west ∧
      selectedHorizontalFor .c .northwest state = some .north := by
  rcases state with ⟨west, east, south, north⟩
  simp [RedShades.allowedFor, RedShades.hasWest, RedShades.hasEast,
    RedShades.hasSouth, RedShades.hasNorth, RedShades.hasHorizontal,
    RedShades.hasVertical, RedShades.cornerWest, RedShades.cornerEast,
    RedShades.cornerSouth, RedShades.cornerNorth, RedShades.optionPresent,
    selectedVerticalFor, selectedHorizontalFor, verticalShade?, horizontalShade?,
    Signals.verticalInterior?, Signals.horizontalInterior?] at hallowed hshade ⊢
  aesop

theorem northeast_selected_of_allowed {state : RedShades.State}
    (hallowed : RedShades.allowedFor .d .southwest state = true)
    (hshade : state.west = some .light) :
    selectedVerticalFor .d .southwest state = some .west ∧
      selectedHorizontalFor .d .southwest state = some .south := by
  rcases state with ⟨west, east, south, north⟩
  simp [RedShades.allowedFor, RedShades.hasWest, RedShades.hasEast,
    RedShades.hasSouth, RedShades.hasNorth, RedShades.hasHorizontal,
    RedShades.hasVertical, RedShades.cornerWest, RedShades.cornerEast,
    RedShades.cornerSouth, RedShades.cornerNorth, RedShades.optionPresent,
    selectedVerticalFor, selectedHorizontalFor, verticalShade?, horizontalShade?,
    Signals.verticalInterior?, Signals.horizontalInterior?] at hallowed hshade ⊢
  aesop

theorem northwest_selected_of_allowed {state : RedShades.State}
    (hallowed : RedShades.allowedFor .a .southeast state = true)
    (hshade : state.east = some .light) :
    selectedVerticalFor .a .southeast state = some .east ∧
      selectedHorizontalFor .a .southeast state = some .south := by
  rcases state with ⟨west, east, south, north⟩
  simp [RedShades.allowedFor, RedShades.hasWest, RedShades.hasEast,
    RedShades.hasSouth, RedShades.hasNorth, RedShades.hasHorizontal,
    RedShades.hasVertical, RedShades.cornerWest, RedShades.cornerEast,
    RedShades.cornerSouth, RedShades.cornerNorth, RedShades.optionPresent,
    selectedVerticalFor, selectedHorizontalFor, verticalShade?, horizontalShade?,
    Signals.verticalInterior?, Signals.horizontalInterior?] at hallowed hshade ⊢
  aesop

@[simp] theorem selectedHorizontalInterior_of_not_light {base : RedShades.Site}
    (hlight : horizontalShade? base.2 ≠ some .light) :
    selectedHorizontalInterior? base = none := by
  simp [selectedHorizontalInterior?, selectedHorizontalFor, hlight]

/-- Robinson signal rule after selecting only light red borders. -/
def locallyAllowed (base : RedShades.Site) (signal : Signals.State) : Bool :=
  Signals.horizontalAllowed (selectedVerticalInterior? base) signal &&
    Signals.verticalAllowed (selectedHorizontalInterior? base) signal

theorem horizontalAllowed_of_locallyAllowed {base : RedShades.Site}
    {signal : Signals.State} (hallowed : locallyAllowed base signal = true) :
    Signals.horizontalAllowed (selectedVerticalInterior? base) signal = true := by
  have hparts :
      Signals.horizontalAllowed (selectedVerticalInterior? base) signal = true ∧
        Signals.verticalAllowed (selectedHorizontalInterior? base) signal = true := by
    simpa only [locallyAllowed, Bool.and_eq_true] using hallowed
  exact hparts.1

theorem verticalAllowed_of_locallyAllowed {base : RedShades.Site}
    {signal : Signals.State} (hallowed : locallyAllowed base signal = true) :
    Signals.verticalAllowed (selectedHorizontalInterior? base) signal = true := by
  have hparts :
      Signals.horizontalAllowed (selectedVerticalInterior? base) signal = true ∧
        Signals.verticalAllowed (selectedHorizontalInterior? base) signal = true := by
    simpa only [locallyAllowed, Bool.and_eq_true] using hallowed
  exact hparts.2

theorem selectedHorizontalFor_r1 {component : Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (hline : QuarterGeometry.containsLine component .r1 = true)
    (hbit : quadrant.yBit = true)
    (hshade : horizontalShade? state = some .light) :
    selectedHorizontalFor component quadrant state = some .north := by
  simp only [selectedHorizontalFor, hshade, if_true]
  rcases component <;> rcases quadrant <;>
    simp_all [Signals.horizontalInterior?, QuarterGeometry.containsLine,
      QuarterGeometry.redHorizontalAt, Figure16.Thick.lineSum?, Quadrant.yBit]

theorem selectedHorizontalFor_r3 {component : Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (hline : QuarterGeometry.containsLine component .r3 = true)
    (hbit : quadrant.yBit = false)
    (hshade : horizontalShade? state = some .light) :
    selectedHorizontalFor component quadrant state = some .south := by
  simp only [selectedHorizontalFor, hshade, if_true]
  rcases component <;> rcases quadrant <;>
    simp_all [Signals.horizontalInterior?, QuarterGeometry.containsLine,
      QuarterGeometry.redHorizontalAt, Figure16.Thick.lineSum?, Quadrant.yBit]

theorem selectedVerticalFor_r0 {component : Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (hline : QuarterGeometry.containsLine component .r0 = true)
    (hbit : quadrant.xBit = true)
    (hshade : verticalShade? state = some .light) :
    selectedVerticalFor component quadrant state = some .east := by
  simp only [selectedVerticalFor, hshade, if_true]
  rcases component <;> rcases quadrant <;>
    simp_all [Signals.verticalInterior?, QuarterGeometry.containsLine,
      QuarterGeometry.redVerticalAt, Figure16.Thick.lineSum?, Quadrant.xBit]

theorem selectedVerticalFor_r2 {component : Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (hline : QuarterGeometry.containsLine component .r2 = true)
    (hbit : quadrant.xBit = false)
    (hshade : verticalShade? state = some .light) :
    selectedVerticalFor component quadrant state = some .west := by
  simp only [selectedVerticalFor, hshade, if_true]
  rcases component <;> rcases quadrant <;>
    simp_all [Signals.verticalInterior?, QuarterGeometry.containsLine,
      QuarterGeometry.redVerticalAt, Figure16.Thick.lineSum?, Quadrant.xBit]

abbrev Site := RedShades.Site × Signals.State

def allSites : List Site :=
  RedShades.allSites.flatMap fun base =>
    (Signals.State.all.filter fun signal => locallyAllowed base signal).map fun signal =>
      (base, signal)

@[simp] theorem mem_allSites_iff (site : Site) :
    site ∈ allSites ↔
      RedShades.locallyAllowed site.1.1 site.1.2 = true ∧
        locallyAllowed site.1 site.2 = true := by
  rcases site with ⟨base, signal⟩
  simp [allSites, RedShades.mem_allSites_iff]

/-- Layer a shaded quarter tile with its obstruction-signal edges. -/
def tile (site : Site) : WangTile :=
  WangTile.product (RedShades.tile site.1) (Signals.State.tile site.2)

theorem signalStateTile_injective : Function.Injective Signals.State.tile := by
  intro first second heq
  rcases first with ⟨firstWest, firstEast, firstSouth, firstNorth⟩
  rcases second with ⟨secondWest, secondEast, secondSouth, secondNorth⟩
  have hwest := Signals.Flow.code_injective (congrArg WangTile.w heq)
  have heast := Signals.Flow.code_injective (congrArg WangTile.e heq)
  have hsouth := Signals.Flow.code_injective (congrArg WangTile.s heq)
  have hnorth := Signals.Flow.code_injective (congrArg WangTile.n heq)
  change firstWest = secondWest at hwest
  change firstEast = secondEast at heast
  change firstSouth = secondSouth at hsouth
  change firstNorth = secondNorth at hnorth
  subst secondWest
  subst secondEast
  subst secondSouth
  subst secondNorth
  rfl

theorem tile_injective : Function.Injective tile := by
  intro first second heq
  change WangTile.product (RedShades.tile first.1) (Signals.State.tile first.2) =
    WangTile.product (RedShades.tile second.1) (Signals.State.tile second.2) at heq
  have hpair := product_eq_iff.mp heq
  apply Prod.ext
  · exact RedShades.tile_injective hpair.1
  · exact signalStateTile_injective hpair.2

@[irreducible] def tileSet : TileSet := allSites.map tile

theorem tile_mem (site : Site)
    (hshade : RedShades.locallyAllowed site.1.1 site.1.2 = true)
    (hsignal : locallyAllowed site.1 site.2 = true) :
    tile site ∈ tileSet := by
  unfold tileSet
  exact List.mem_map.2
    ⟨site, (mem_allSites_iff site).2 ⟨hshade, hsignal⟩, rfl⟩

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

theorem decode_shadeAllowed (wang : TileIn tileSet) :
    RedShades.locallyAllowed (decode wang).1.1 (decode wang).1.2 = true :=
  (mem_allSites_iff (decode wang)).1 (decode_mem wang) |>.1

theorem decode_signalAllowed (wang : TileIn tileSet) :
    locallyAllowed (decode wang).1 (decode wang).2 = true :=
  (mem_allSites_iff (decode wang)).1 (decode_mem wang) |>.2

def basePlane (x : Int × Int → TileIn tileSet) :
    Int × Int → TileIn RedShades.tileSet :=
  fun p => ⟨RedShades.tile (decode (x p)).1, by
    apply RedShades.tile_mem
    exact decode_shadeAllowed (x p)⟩

theorem decode_basePlane (x : Int × Int → TileIn tileSet) (p : Int × Int) :
    RedShades.decode (basePlane x p) = (decode (x p)).1 := by
  apply RedShades.decode_tile_site

theorem shadePlane_basePlane (x : Int × Int → TileIn tileSet)
    (p : Int × Int) :
    RedShades.shadePlane (basePlane x) p = (decode (x p)).1.2 := by
  change (RedShades.decode (basePlane x p)).2 = _
  rw [decode_basePlane]

theorem quarterPlane_basePlane (x : Int × Int → TileIn tileSet)
    (p : Int × Int) :
    RedShades.quarterPlane (basePlane x) p = (decode (x p)).1.1 := by
  change (RedShades.decode (basePlane x p)).1 = _
  rw [decode_basePlane]

def signalPlane (x : Int × Int → TileIn tileSet) : Int × Int → Signals.State :=
  fun p => (decode (x p)).2

theorem basePlane_tile (x : Int × Int → TileIn tileSet) (p : Int × Int) :
    (basePlane x p).1 = RedShades.tile (decode (x p)).1 := rfl

theorem basePlane_valid {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) :
    ValidPlaneTiling RedShades.tileSet (basePlane x) := by
  constructor
  · intro p
    have hproduct : WangTile.HMatches
        (tile (decode (x p)))
        (tile (decode (x (p.1 + 1, p.2)))) := by
      rw [decode_tile, decode_tile]
      exact hx.1 p
    exact (WangTile.HMatches_product_iff _ _ _ _).1 hproduct |>.1
  · intro p
    have hproduct : WangTile.VMatches
        (tile (decode (x p)))
        (tile (decode (x (p.1, p.2 + 1)))) := by
      rw [decode_tile, decode_tile]
      exact hx.2 p
    exact (WangTile.VMatches_product_iff _ _ _ _).1 hproduct |>.1

theorem signalPlane_matches {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) :
    (∀ p : Int × Int,
      WangTile.HMatches (Signals.State.tile (signalPlane x p))
        (Signals.State.tile (signalPlane x (p.1 + 1, p.2)))) ∧
      ∀ p : Int × Int,
        WangTile.VMatches (Signals.State.tile (signalPlane x p))
          (Signals.State.tile (signalPlane x (p.1, p.2 + 1))) := by
  constructor
  · intro p
    have hproduct : WangTile.HMatches
        (tile (decode (x p)))
        (tile (decode (x (p.1 + 1, p.2)))) := by
      rw [decode_tile, decode_tile]
      exact hx.1 p
    exact (WangTile.HMatches_product_iff _ _ _ _).1 hproduct |>.2
  · intro p
    have hproduct : WangTile.VMatches
        (tile (decode (x p)))
        (tile (decode (x (p.1, p.2 + 1)))) := by
      rw [decode_tile, decode_tile]
      exact hx.2 p
    exact (WangTile.VMatches_product_iff _ _ _ _).1 hproduct |>.2

theorem signalPlane_hmatch {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) (p : Int × Int) :
    (signalPlane x p).east =
      (signalPlane x (p.1 + 1, p.2)).west := by
  apply Signals.Flow.code_injective
  simpa [WangTile.HMatches, Signals.State.tile] using
    (signalPlane_matches hx).1 p

theorem signalPlane_vmatch {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) (p : Int × Int) :
    (signalPlane x p).north =
      (signalPlane x (p.1, p.2 + 1)).south := by
  apply Signals.Flow.code_injective
  simpa [WangTile.VMatches, Signals.State.tile] using
    (signalPlane_matches hx).2 p

/-- The final signal layer still projects to a valid corrected quarter plane. -/
def quarterPlane (x : Int × Int → TileIn tileSet) : QuarterPlane :=
  RedShades.quarterPlane (basePlane x)

theorem quarterPlane_valid {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) :
    ValidQuarterPlane (quarterPlane x) :=
  RedShades.quarterPlane_valid (basePlane_valid hx)

end ShadedSignals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
