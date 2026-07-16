/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.RoutedPointedCoreLabeling

/-!
# Routed pointed labelings from carrier potentials

A concrete scaffold need only assign coordinates at active crossings and one
symbolic label along each horizontal or vertical carrier.  The orthogonal
sides of channel cells are copied from their immediate neighbors.  This turns
the full four-sided core-labeling obligation into two one-dimensional local
compatibility conditions.
-/

namespace LeanWang

namespace RoutedPointedCarrierLabeling

open RoutedPointedCoreLabeling

/-- A finite scaffold box equipped with the two one-dimensional potentials
needed to route any pointed payload plane. -/
structure Potential (S : RoutedScaffold) (r : Nat) where
  base : BoxPattern S.tiles r
  base_valid : ValidBoxTiling S.tiles r base
  point : Box r → Int × Int
  horizontal : Box r → EdgeLabel
  vertical : Box r → EdgeLabel
  corner_zero : ∀ p : Box r,
    S.role (base p).1 = .corner → point p = (0, 0)
  hcompatible :
    ∀ p : Box r, ∀ next : InBox r (p.1.1 + 1, p.1.2),
      (S.role (base p).1).isHorizontalCarrier = true →
      (S.role (base ⟨(p.1.1 + 1, p.1.2), next⟩).1).isHorizontalCarrier = true →
      EdgeLabel.Compatible
        (match S.role (base p).1 with
          | .active | .corner => .east (point p)
          | .horizontal => horizontal p
          | .inactive | .vertical => .zero)
        (match S.role
            (base ⟨(p.1.1 + 1, p.1.2), next⟩).1 with
          | .active | .corner =>
              .west (point ⟨(p.1.1 + 1, p.1.2), next⟩)
          | .horizontal =>
              horizontal ⟨(p.1.1 + 1, p.1.2), next⟩
          | .inactive | .vertical => .zero)
  vcompatible :
    ∀ p : Box r, ∀ next : InBox r (p.1.1, p.1.2 + 1),
      (S.role (base p).1).isVerticalCarrier = true →
      (S.role (base ⟨(p.1.1, p.1.2 + 1), next⟩).1).isVerticalCarrier = true →
      EdgeLabel.Compatible
        (match S.role (base p).1 with
          | .active | .corner => .north (point p)
          | .vertical => vertical p
          | .inactive | .horizontal => .zero)
        (match S.role
            (base ⟨(p.1.1, p.1.2 + 1), next⟩).1 with
          | .active | .corner =>
              .south (point ⟨(p.1.1, p.1.2 + 1), next⟩)
          | .vertical => vertical ⟨(p.1.1, p.1.2 + 1), next⟩
          | .inactive | .horizontal => .zero)

namespace Potential

variable {S : RoutedScaffold} {r : Nat} (potential : Potential S r)

def hEast (p : Box r) : EdgeLabel :=
  match S.role (potential.base p).1 with
  | .active | .corner => .east (potential.point p)
  | .horizontal => potential.horizontal p
  | .inactive | .vertical => .zero

def hWest (p : Box r) : EdgeLabel :=
  match S.role (potential.base p).1 with
  | .active | .corner => .west (potential.point p)
  | .horizontal => potential.horizontal p
  | .inactive | .vertical => .zero

def vNorth (p : Box r) : EdgeLabel :=
  match S.role (potential.base p).1 with
  | .active | .corner => .north (potential.point p)
  | .vertical => potential.vertical p
  | .inactive | .horizontal => .zero

def vSouth (p : Box r) : EdgeLabel :=
  match S.role (potential.base p).1 with
  | .active | .corner => .south (potential.point p)
  | .vertical => potential.vertical p
  | .inactive | .horizontal => .zero

/-- Horizontal label crossing the east side of a vertical channel. -/
def eastCross (p : Box r) : EdgeLabel :=
  if hnext : InBox r (p.1.1 + 1, p.1.2) then
    let next : Box r := ⟨(p.1.1 + 1, p.1.2), hnext⟩
    if (S.role (potential.base next).1).isHorizontalCarrier then
      potential.hWest next
    else .zero
  else .zero

/-- Horizontal label crossing the west side of a vertical channel. -/
def westCross (p : Box r) : EdgeLabel :=
  if hprevious : InBox r (p.1.1 - 1, p.1.2) then
    let previous : Box r := ⟨(p.1.1 - 1, p.1.2), hprevious⟩
    if (S.role (potential.base previous).1).isHorizontalCarrier then
      potential.hEast previous
    else .zero
  else .zero

/-- Vertical label crossing the north side of a horizontal channel. -/
def northCross (p : Box r) : EdgeLabel :=
  if hnext : InBox r (p.1.1, p.1.2 + 1) then
    let next : Box r := ⟨(p.1.1, p.1.2 + 1), hnext⟩
    if (S.role (potential.base next).1).isVerticalCarrier then
      potential.vSouth next
    else .zero
  else .zero

/-- Vertical label crossing the south side of a horizontal channel. -/
def southCross (p : Box r) : EdgeLabel :=
  if hprevious : InBox r (p.1.1, p.1.2 - 1) then
    let previous : Box r := ⟨(p.1.1, p.1.2 - 1), hprevious⟩
    if (S.role (potential.base previous).1).isVerticalCarrier then
      potential.vNorth previous
    else .zero
  else .zero

/-- The full four-sided symbolic label derived from the carrier potential. -/
def label (p : Box r) : Label :=
  match S.role (potential.base p).1 with
  | .inactive => .inactive
  | .horizontal =>
      .channel (potential.northCross p) (potential.southCross p)
        (potential.horizontal p) (potential.horizontal p)
  | .vertical =>
      .channel (potential.vertical p) (potential.vertical p)
        (potential.eastCross p) (potential.westCross p)
  | .active | .corner => .tile (potential.point p)

theorem label_fits (p : Box r) :
    (potential.label p).FitsRole (S.role (potential.base p).1) := by
  cases hrole : S.role (potential.base p).1 with
  | inactive => simp [label, hrole, Label.FitsRole]
  | horizontal => simp [label, hrole, Label.FitsRole]
  | vertical => simp [label, hrole, Label.FitsRole]
  | active => simp [label, hrole, Label.FitsRole]
  | corner =>
      simpa [label, hrole, Label.FitsRole] using
        potential.corner_zero p hrole

theorem label_hcompatible
    (p : Box r) (next : InBox r (p.1.1 + 1, p.1.2))
    (left : (S.role (potential.base p).1).isConstrained = true)
    (right :
      (S.role
        (potential.base ⟨(p.1.1 + 1, p.1.2), next⟩).1).isConstrained = true) :
    Label.HCompatible (potential.label p)
      (potential.label ⟨(p.1.1 + 1, p.1.2), next⟩) := by
  let q : Box r := ⟨(p.1.1 + 1, p.1.2), next⟩
  have carrier := potential.hcompatible p next
  cases hp : S.role (potential.base p).1 <;>
    cases hq : S.role (potential.base q).1 <;>
      simp_all [q, RouteRole.isConstrained, RouteRole.isHorizontalCarrier,
        label, Label.HCompatible, Label.east, Label.west,
        hEast, hWest, eastCross, westCross, p.property]
  all_goals exact EdgeLabel.Compatible.refl _

theorem label_vcompatible
    (p : Box r) (next : InBox r (p.1.1, p.1.2 + 1))
    (lower : (S.role (potential.base p).1).isConstrained = true)
    (upper :
      (S.role
        (potential.base ⟨(p.1.1, p.1.2 + 1), next⟩).1).isConstrained = true) :
    Label.VCompatible (potential.label p)
      (potential.label ⟨(p.1.1, p.1.2 + 1), next⟩) := by
  let q : Box r := ⟨(p.1.1, p.1.2 + 1), next⟩
  have carrier := potential.vcompatible p next
  cases hp : S.role (potential.base p).1 <;>
    cases hq : S.role (potential.base q).1 <;>
      simp_all [q, RouteRole.isConstrained, RouteRole.isVerticalCarrier,
        label, Label.VCompatible, Label.north, Label.south,
        vNorth, vSouth, northCross, southCross, p.property]
  all_goals exact EdgeLabel.Compatible.refl _

def toLabeling : RoutedPointedCoreLabeling.Labeling S r where
  base := potential.base
  label := potential.label
  base_valid := potential.base_valid
  fits := potential.label_fits
  hcompatible := potential.label_hcompatible
  vcompatible := potential.label_vcompatible

end Potential

/-- Pure carrier-potential geometry sufficient for all finite pointed core
labelings. -/
def HasRoutedPointedCarrierPotentials (S : RoutedScaffold) : Prop :=
  ∀ r : Nat, Nonempty (Potential S r)

theorem hasRoutedPointedCoreLabelings_of_carrierPotentials
    {S : RoutedScaffold}
    (potentials : HasRoutedPointedCarrierPotentials S) :
    RoutedPointedCoreLabeling.HasRoutedPointedCoreLabelings S := by
  intro r
  rcases potentials r with ⟨potential⟩
  exact ⟨potential.toLabeling⟩

theorem realizesRoutedPointedPlanes_of_carrierPotentials
    {S : RoutedScaffold}
    (potentials : HasRoutedPointedCarrierPotentials S) :
    RealizesRoutedPointedPlanes S :=
  RoutedPointedCoreLabeling.realizesRoutedPointedPlanes_of_labelings
    (hasRoutedPointedCoreLabelings_of_carrierPotentials potentials)

end RoutedPointedCarrierLabeling
end LeanWang
