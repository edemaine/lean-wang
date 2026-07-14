/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraph

/-!
# Construct finite red-shade rectangles from parity colorings

The red layer is an XOR constraint graph: ordinary continuations have parity
zero and crossings have parity one.  This file turns a Boolean coloring of a
finite port graph into the concrete `RedShades.State` values used by the Wang
tiles.  The remaining backward geometry can therefore work only with graph
bipartiteness and unshaded edge compatibility.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphColoring

open RedCycles RedShadeGraph RedShadePaths Signals.FreeCellLocal

set_option maxRecDepth 20000

def InBounds (width height : Nat) (port : Port) : Prop :=
  port.x < width ∧ port.y < height

/-- A shade assignment satisfying the red-port graph inside one rectangle. -/
structure ValidPortLabelingOn (indexGrid : Nat → Nat → Index)
    (width height : Nat) where
  label : Port → Option RedShades.Shade
  present : ∀ port, InBounds width height port →
    (label port).isSome = portPresent indexGrid port
  related : ∀ {first second parity}, Link indexGrid first second parity →
    InBounds width height first → InBounds width height second →
      Related parity (label first) (label second)

/-- The finite analogue of `ValidShadeGrid`. -/
structure ValidShadeRectangle (indexGrid : Nat → Nat → Index)
    (stateGrid : Nat → Nat → RedShades.State) (width height : Nat) : Prop where
  allowed : ∀ x y, x < width → y < height →
    RedShades.locallyAllowed
      (indexGrid (x / 2) (y / 2), quadrantAt x y) (stateGrid x y) = true
  hmatch : ∀ x y, x + 1 < width → y < height →
    (stateGrid x y).east = (stateGrid (x + 1) y).west
  vmatch : ∀ x y, x < width → y + 1 < height →
    (stateGrid x y).north = (stateGrid x (y + 1)).south

namespace ValidPortLabelingOn

def stateGrid {indexGrid : Nat → Nat → Index} {width height : Nat}
    (labeling : ValidPortLabelingOn indexGrid width height) :
    Nat → Nat → RedShades.State := fun x y =>
  { west := labeling.label ⟨x, y, .west⟩
    east := labeling.label ⟨x, y, .east⟩
    south := labeling.label ⟨x, y, .south⟩
    north := labeling.label ⟨x, y, .north⟩ }

private theorem ne_of_related_true
    {first second : Option RedShades.Shade}
    (related : Related true first second) : first ≠ second := by
  rcases related with ⟨shade, rfl, rfl⟩
  intro equal
  simp only [Option.some.injEq] at equal
  cases shade <;> contradiction

theorem validShadeRectangle
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    (labeling : ValidPortLabelingOn indexGrid width height) :
    ValidShadeRectangle indexGrid labeling.stateGrid width height := by
  constructor
  · intro x y hx hy
    simp only [RedShades.locallyAllowed]
    apply RedShades.allowedFor_of
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .west⟩ ⟨hx, hy⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .east⟩ ⟨hx, hy⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .south⟩ ⟨hx, hy⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .north⟩ ⟨hx, hy⟩
    · intro hpath
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .east⟩
      exact labeling.related (Link.horizontal x y hpath) ⟨hx, hy⟩ ⟨hx, hy⟩
    · intro hpath
      change labeling.label ⟨x, y, .south⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.vertical x y hpath) ⟨hx, hy⟩ ⟨hx, hy⟩
    · intro heast hsouth
      change labeling.label ⟨x, y, .east⟩ =
        labeling.label ⟨x, y, .south⟩
      exact labeling.related (Link.eastSouth x y heast hsouth)
        ⟨hx, hy⟩ ⟨hx, hy⟩
    · intro heast hnorth
      change labeling.label ⟨x, y, .east⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.eastNorth x y heast hnorth)
        ⟨hx, hy⟩ ⟨hx, hy⟩
    · intro hwest hsouth
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .south⟩
      exact labeling.related (Link.westSouth x y hwest hsouth)
        ⟨hx, hy⟩ ⟨hx, hy⟩
    · intro hwest hnorth
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.westNorth x y hwest hnorth)
        ⟨hx, hy⟩ ⟨hx, hy⟩
    · intro hhorizontal hvertical
      change labeling.label ⟨x, y, .west⟩ ≠
        labeling.label ⟨x, y, .south⟩
      exact ne_of_related_true
        (labeling.related (Link.crossing x y hhorizontal hvertical)
          ⟨hx, hy⟩ ⟨hx, hy⟩)
  · intro x y hx hy
    change labeling.label ⟨x, y, .east⟩ =
      labeling.label ⟨x + 1, y, .west⟩
    exact labeling.related (Link.horizontalMatch x y)
      (by simp only [InBounds]; omega)
      (by simp only [InBounds]; omega)
  · intro x y hx hy
    change labeling.label ⟨x, y, .north⟩ =
      labeling.label ⟨x, y + 1, .south⟩
    exact labeling.related (Link.verticalMatch x y)
      (by simp only [InBounds]; omega)
      (by simp only [InBounds]; omega)

end ValidPortLabelingOn

def shadeOfBool : Bool → RedShades.Shade
  | false => .light
  | true => .dark

@[simp] theorem shadeOfBool_xor_true (color : Bool) :
    shadeOfBool (Bool.xor color true) = (shadeOfBool color).opposite := by
  cases color <;> rfl

/-- A bounded XOR coloring together with the unshaded incidence compatibility
needed at ordinary match links. -/
structure ValidParityColoringOn (indexGrid : Nat → Nat → Index)
    (width height : Nat) where
  color : Port → Bool
  present_eq : ∀ {first second parity}, Link indexGrid first second parity →
    InBounds width height first → InBounds width height second →
      portPresent indexGrid first = portPresent indexGrid second
  color_eq : ∀ {first second parity}, Link indexGrid first second parity →
    InBounds width height first → InBounds width height second →
      color second = Bool.xor (color first) parity
  odd_present : ∀ {first second}, Link indexGrid first second true →
    InBounds width height first → InBounds width height second →
      portPresent indexGrid first = true

namespace ValidParityColoringOn

def toPortLabeling
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    (coloring : ValidParityColoringOn indexGrid width height) :
    ValidPortLabelingOn indexGrid width height where
  label := fun port =>
    if portPresent indexGrid port then some (shadeOfBool (coloring.color port))
    else none
  present := by
    intro port _
    cases portPresent indexGrid port <;> rfl
  related := by
    intro first second parity link hfirst hsecond
    have hpresent := coloring.present_eq link hfirst hsecond
    have hcolor := coloring.color_eq link hfirst hsecond
    cases hparity : parity with
    | false =>
        change (if portPresent indexGrid first then
            some (shadeOfBool (coloring.color first)) else none) =
          (if portPresent indexGrid second then
            some (shadeOfBool (coloring.color second)) else none)
        rw [hparity] at hcolor
        simp only [Bool.xor_false] at hcolor
        rw [← hcolor, hpresent]
    | true =>
        have hfirstLive : portPresent indexGrid first = true :=
          coloring.odd_present (hparity ▸ link) hfirst hsecond
        have hsecondLive : portPresent indexGrid second = true := by
          rw [← hpresent]
          exact hfirstLive
        refine ⟨shadeOfBool (coloring.color first), ?_, ?_⟩
        · simp [hfirstLive]
        · simp only [hsecondLive, if_true, Option.some.injEq]
          rw [hparity] at hcolor
          calc
            shadeOfBool (coloring.color second) =
                shadeOfBool (Bool.xor (coloring.color first) true) :=
              congrArg shadeOfBool hcolor
            _ = (shadeOfBool (coloring.color first)).opposite :=
              shadeOfBool_xor_true _

theorem validShadeRectangle
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    (coloring : ValidParityColoringOn indexGrid width height) :
    ValidShadeRectangle indexGrid coloring.toPortLabeling.stateGrid
      width height :=
  coloring.toPortLabeling.validShadeRectangle

end ValidParityColoringOn

end RedShadeGraphColoring
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
