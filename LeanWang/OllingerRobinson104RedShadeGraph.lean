/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadePaths

/-!
Finite connectivity certificates for the light/dark red-wire layer.

Every local continuation preserves shade, while crossing from the horizontal
wire to the vertical wire reverses it. A graph path therefore carries one bit:
the parity of the crossings it uses.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraph

open RedCycles Signals.FreeCellLocal RedShadePaths

set_option maxRecDepth 20000

/-- A quarter-tile edge at an absolute coordinate. -/
inductive Side where
  | west
  | east
  | south
  | north
deriving DecidableEq, Repr

structure Port where
  x : Nat
  y : Nat
  side : Side
deriving DecidableEq, Repr

def value (stateGrid : Nat → Nat → RedShades.State) (port : Port) :
    Option RedShades.Shade :=
  match port.side with
  | .west => (stateGrid port.x port.y).west
  | .east => (stateGrid port.x port.y).east
  | .south => (stateGrid port.x port.y).south
  | .north => (stateGrid port.x port.y).north

/-- Whether the unshaded quarter geometry carries a red wire at a port. -/
def portPresent (grid : Nat → Nat → Index) (port : Port) : Bool :=
  let component := componentAt grid port.x port.y
  let quadrant := quadrantAt port.x port.y
  match port.side with
  | .west => RedShades.hasWest component quadrant
  | .east => RedShades.hasEast component quadrant
  | .south => RedShades.hasSouth component quadrant
  | .north => RedShades.hasNorth component quadrant

/-- Even parity means equal shades; odd parity means opposite present shades. -/
def Related (parity : Bool) (first second : Option RedShades.Shade) : Prop :=
  match parity with
  | false => first = second
  | true => ∃ shade, first = some shade ∧ second = some shade.opposite

@[simp] theorem related_false_iff {first second : Option RedShades.Shade} :
    Related false first second ↔ first = second := Iff.rfl

@[simp] theorem related_true_iff {first second : Option RedShades.Shade} :
    Related true first second ↔
      ∃ shade, first = some shade ∧ second = some shade.opposite := Iff.rfl

theorem Related.refl (edge : Option RedShades.Shade) :
    Related false edge edge := rfl

theorem Related.symm {parity : Bool} {first second : Option RedShades.Shade}
    (relation : Related parity first second) : Related parity second first := by
  cases parity
  · exact Eq.symm relation
  · rcases relation with ⟨shade, rfl, rfl⟩
    exact ⟨shade.opposite, rfl, by simp⟩

theorem Related.trans {first second third : Option RedShades.Shade}
    {firstParity secondParity : Bool}
    (firstRelation : Related firstParity first second)
    (secondRelation : Related secondParity second third) :
    Related (Bool.xor firstParity secondParity) first third := by
  cases firstParity <;> cases secondParity
  · exact Eq.trans firstRelation secondRelation
  · subst second
    exact secondRelation
  · subst second
    exact firstRelation
  · rcases firstRelation with ⟨firstShade, rfl, rfl⟩
    rcases secondRelation with ⟨secondShade, heq, hthird⟩
    simp only [Option.some.injEq] at heq
    subst secondShade
    simpa using Eq.symm hthird

theorem related_true_of_ne_of_present
    {first second : Option RedShades.Shade}
    (hfirst : first.isSome = true) (hsecond : second.isSome = true)
    (hne : first ≠ second) : Related true first second := by
  rcases first with _ | first
  · simp at hfirst
  rcases second with _ | second
  · simp at hsecond
  refine ⟨first, rfl, congrArg some ?_⟩
  exact RedShades.Shade.eq_opposite_of_ne (by
    intro heq
    apply hne
    exact congrArg some heq)

theorem east_south_corner_eq_of_allowedFor
    {component : Figure16.Thick} {quadrant : Quadrant} {state : RedShades.State}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (heast : RedShades.cornerEast component quadrant = true)
    (hsouth : RedShades.cornerSouth component quadrant = true) :
    state.east = state.south := by
  cases component <;> cases quadrant <;>
    simp_all [RedShades.allowedFor, RedShades.cornerEast, RedShades.cornerSouth]

/-- One local shade-preserving or shade-reversing connection. -/
inductive Link (indexGrid : Nat → Nat → Index) : Port → Port → Bool → Prop where
  | horizontalMatch (x y : Nat) :
      Link indexGrid ⟨x, y, .east⟩ ⟨x + 1, y, .west⟩ false
  | verticalMatch (x y : Nat) :
      Link indexGrid ⟨x, y, .north⟩ ⟨x, y + 1, .south⟩ false
  | horizontal (x y : Nat)
      (hpath : RedShades.hasHorizontal
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .east⟩ false
  | vertical (x y : Nat)
      (hpath : RedShades.hasVertical
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .south⟩ ⟨x, y, .north⟩ false
  | westNorth (x y : Nat)
      (hwest : RedShades.cornerWest
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hnorth : RedShades.cornerNorth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .north⟩ false
  | westSouth (x y : Nat)
      (hwest : RedShades.cornerWest
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hsouth : RedShades.cornerSouth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .south⟩ false
  | eastNorth (x y : Nat)
      (heast : RedShades.cornerEast
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hnorth : RedShades.cornerNorth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .east⟩ ⟨x, y, .north⟩ false
  | eastSouth (x y : Nat)
      (heast : RedShades.cornerEast
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hsouth : RedShades.cornerSouth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .east⟩ ⟨x, y, .south⟩ false
  | crossing (x y : Nat)
      (hhorizontal : RedShades.hasHorizontal
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hvertical : RedShades.hasVertical
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .south⟩ true
  | symm {first second : Port} {parity : Bool} :
      Link indexGrid first second parity → Link indexGrid second first parity

theorem Link.sound {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid)
    {first second : Port} {parity : Bool}
    (link : Link indexGrid first second parity) :
    Related parity (value stateGrid first) (value stateGrid second) := by
  induction link with
  | horizontalMatch x y => exact valid.hmatch x y
  | verticalMatch x y => exact valid.vmatch x y
  | horizontal x y hpath => exact valid.horizontal_eq x y hpath
  | vertical x y hpath => exact valid.vertical_eq x y hpath
  | westNorth x y hwest hnorth =>
      exact valid.west_north_corner_eq x y hwest hnorth
  | westSouth x y hwest hsouth =>
      exact valid.west_south_corner_eq x y hwest hsouth
  | eastNorth x y heast hnorth =>
      exact valid.east_north_corner_eq x y heast hnorth
  | eastSouth x y heast hsouth =>
      have hallowed := valid.allowed x y
      unfold RedShades.locallyAllowed at hallowed
      dsimp only at hallowed
      unfold componentAt at heast hsouth
      exact east_south_corner_eq_of_allowedFor hallowed heast hsouth
  | crossing x y hhorizontal hvertical =>
      apply related_true_of_ne_of_present
      · exact valid.west_present x y (by
          simp only [RedShades.hasWest, hhorizontal, Bool.true_or])
      · exact valid.south_present x y (by
          simp only [RedShades.hasSouth, hvertical, Bool.true_or])
      · exact valid.crossing_opposite x y hhorizontal hvertical
  | symm link ih => exact Related.symm ih

/-- A parity-consistent assignment to all red-graph ports.  Incidence is part
of the data because match links exist independently of whether the shared
edge carries a red wire. -/
structure ValidPortLabeling (indexGrid : Nat → Nat → Index) where
  label : Port → Option RedShades.Shade
  present : ∀ port, (label port).isSome = portPresent indexGrid port
  related : ∀ {first second parity}, Link indexGrid first second parity →
    Related parity (label first) (label second)

namespace ValidPortLabeling

/-- Regroup four labeled ports into the corresponding quarter shade state. -/
def stateGrid {indexGrid : Nat → Nat → Index}
    (labeling : ValidPortLabeling indexGrid) :
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

/-- Port incidence and parity-link consistency are exactly the local shade
tile and edge-matching rules. -/
theorem validShadeGrid {indexGrid : Nat → Nat → Index}
    (labeling : ValidPortLabeling indexGrid) :
    ValidShadeGrid indexGrid labeling.stateGrid := by
  constructor
  · intro x y
    simp only [RedShades.locallyAllowed]
    apply RedShades.allowedFor_of
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .west⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .east⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .south⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .north⟩
    · intro hpath
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .east⟩
      exact labeling.related (Link.horizontal x y hpath)
    · intro hpath
      change labeling.label ⟨x, y, .south⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.vertical x y hpath)
    · intro heast hsouth
      change labeling.label ⟨x, y, .east⟩ =
        labeling.label ⟨x, y, .south⟩
      exact labeling.related (Link.eastSouth x y heast hsouth)
    · intro heast hnorth
      change labeling.label ⟨x, y, .east⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.eastNorth x y heast hnorth)
    · intro hwest hsouth
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .south⟩
      exact labeling.related (Link.westSouth x y hwest hsouth)
    · intro hwest hnorth
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.westNorth x y hwest hnorth)
    · intro hhorizontal hvertical
      change labeling.label ⟨x, y, .west⟩ ≠
        labeling.label ⟨x, y, .south⟩
      exact ne_of_related_true
        (labeling.related (Link.crossing x y hhorizontal hvertical))
  · intro x y
    change labeling.label ⟨x, y, .east⟩ =
      labeling.label ⟨x + 1, y, .west⟩
    exact labeling.related (Link.horizontalMatch x y)
  · intro x y
    change labeling.label ⟨x, y, .north⟩ =
      labeling.label ⟨x, y + 1, .south⟩
    exact labeling.related (Link.verticalMatch x y)

end ValidPortLabeling

/-- A finite red-wire walk, labelled by the parity of its crossings. -/
inductive Path (indexGrid : Nat → Nat → Index) : Port → Port → Bool → Prop where
  | refl (port : Port) : Path indexGrid port port false
  | ofLink {first second : Port} {parity : Bool} :
      Link indexGrid first second parity → Path indexGrid first second parity
  | trans {first second third : Port} {firstParity secondParity : Bool} :
      Path indexGrid first second firstParity →
      Path indexGrid second third secondParity →
      Path indexGrid first third (Bool.xor firstParity secondParity)

theorem Path.sound {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid)
    {first second : Port} {parity : Bool}
    (path : Path indexGrid first second parity) :
    Related parity (value stateGrid first) (value stateGrid second) := by
  induction path with
  | refl port => exact Related.refl _
  | ofLink link => exact link.sound valid
  | trans firstPath secondPath firstIH secondIH =>
      exact Related.trans firstIH secondIH

end RedShadeGraph
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
