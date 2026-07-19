/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedPayloadCorridors

/-!
# Robinson obstruction geometry

The geometric content of Robinson's Section 7 argument is that the nearest
red boundary seen from a free line faces outward. The one-dimensional lemmas
below show that this finite geometric certificate forces a nonempty obstruction
signal at every crossing with a non-free line.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionGeometry

open OrientedRedCycles RedCycles RedShadeCycles RedShadePaths
  ShadedPlaneSignalGrid ShadedPayloadCorridors Signals.FreeCellLocal

set_option maxRecDepth 20000

structure Geometry
    (indexGrid : Nat -> Nat -> Index)
    (shadeGrid : Nat -> Nat -> RedShades.State)
    (west east south north : Nat) : Prop where
  verticalBoundary : forall {column row : Nat},
    quarterWest west < column -> column < quarterEast east ->
    quarterSouth south < row -> row < quarterNorth north ->
    IsFreeRow indexGrid shadeGrid west east row ->
    ¬IsFreeColumn indexGrid shadeGrid south north column ->
      ShadedSignals.selectedHorizontalFor
          (componentAt indexGrid column row) (quadrantAt column row)
          (shadeGrid column row) ≠ none ∨
      (∃ boundary, row < boundary ∧ boundary < quarterNorth north ∧
        ShadedSignals.selectedHorizontalFor
          (componentAt indexGrid column boundary) (quadrantAt column boundary)
          (shadeGrid column boundary) = some .north ∧
        ∀ y, row < y -> y < boundary ->
          ShadedSignals.selectedHorizontalFor
            (componentAt indexGrid column y) (quadrantAt column y)
            (shadeGrid column y) = none) ∨
      (∃ boundary, quarterSouth south < boundary ∧ boundary < row ∧
        ShadedSignals.selectedHorizontalFor
          (componentAt indexGrid column boundary) (quadrantAt column boundary)
          (shadeGrid column boundary) = some .south ∧
        ∀ y, boundary < y -> y < row ->
          ShadedSignals.selectedHorizontalFor
            (componentAt indexGrid column y) (quadrantAt column y)
            (shadeGrid column y) = none)
  horizontalBoundary : forall {column row : Nat},
    quarterWest west < column -> column < quarterEast east ->
    quarterSouth south < row -> row < quarterNorth north ->
    IsFreeColumn indexGrid shadeGrid south north column ->
    ¬IsFreeRow indexGrid shadeGrid west east row ->
      ShadedSignals.selectedVerticalFor
          (componentAt indexGrid column row) (quadrantAt column row)
          (shadeGrid column row) ≠ none ∨
      (∃ boundary, column < boundary ∧ boundary < quarterEast east ∧
        ShadedSignals.selectedVerticalFor
          (componentAt indexGrid boundary row) (quadrantAt boundary row)
          (shadeGrid boundary row) = some .east ∧
        ∀ x, column < x -> x < boundary ->
          ShadedSignals.selectedVerticalFor
            (componentAt indexGrid x row) (quadrantAt x row)
            (shadeGrid x row) = none) ∨
      (∃ boundary, quarterWest west < boundary ∧ boundary < column ∧
        ShadedSignals.selectedVerticalFor
          (componentAt indexGrid boundary row) (quadrantAt boundary row)
          (shadeGrid boundary row) = some .west ∧
        ∀ x, boundary < x -> x < column ->
          ShadedSignals.selectedVerticalFor
            (componentAt indexGrid x row) (quadrantAt x row)
          (shadeGrid x row) = none)

private theorem blocked_at_selected_boundary {α : Type*}
    {selected : Option α} {before after : Signals.Flow}
    (hselected : selected ≠ none)
    (houter : ∀ value, selected = some value →
      before ≠ .none ∨ after ≠ .none) :
    before ≠ .none ∨ after ≠ .none := by
  cases hvalue : selected with
  | none => contradiction
  | some value => exact houter value hvalue

theorem vertical_blocked_at_boundary
    {indexGrid : Nat -> Nat -> Index}
    {shadeGrid : Nat -> Nat -> RedShades.State}
    {signalGrid : Nat -> Nat -> Signals.State}
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {column row : Nat}
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column row) (quadrantAt column row)
      (shadeGrid column row) ≠ none) :
    (signalGrid column row).south ≠ .none ∨
      (signalGrid column row).north ≠ .none := by
  apply blocked_at_selected_boundary hselected
  intro interior hvalue
  cases interior with
  | north =>
      exact Or.inl (Signals.vertical_interiorNorth_rules (by
        simpa only [hvalue] using valid.verticalAllowed column row)).1
  | south =>
      exact Or.inr (Signals.vertical_interiorSouth_rules (by
        simpa only [hvalue] using valid.verticalAllowed column row)).1

theorem horizontal_blocked_at_boundary
    {indexGrid : Nat -> Nat -> Index}
    {shadeGrid : Nat -> Nat -> RedShades.State}
    {signalGrid : Nat -> Nat -> Signals.State}
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {column row : Nat}
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid column row) (quadrantAt column row)
      (shadeGrid column row) ≠ none) :
    (signalGrid column row).west ≠ .none ∨
      (signalGrid column row).east ≠ .none := by
  apply blocked_at_selected_boundary hselected
  intro interior hvalue
  cases interior with
  | west =>
      exact Or.inr (Signals.horizontal_interiorWest_rules (by
        simpa only [hvalue] using valid.horizontalAllowed column row)).1
  | east =>
      exact Or.inl (Signals.horizontal_interiorEast_rules (by
        simpa only [hvalue] using valid.horizontalAllowed column row)).1

theorem vertical_blocked_of_upper
    {indexGrid : Nat -> Nat -> Index}
    {shadeGrid : Nat -> Nat -> RedShades.State}
    {signalGrid : Nat -> Nat -> Signals.State}
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {column row boundary : Nat}
    (hrb : row < boundary)
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column boundary) (quadrantAt column boundary)
      (shadeGrid column boundary) = some .north)
    (hbetween : ∀ y, row < y -> y < boundary ->
      ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid column y) (quadrantAt column y)
        (shadeGrid column y) = none) :
    (signalGrid column row).north ≠ .none := by
  have houter : (signalGrid column boundary).south ≠ .none :=
    (Signals.vertical_interiorNorth_rules (by
      simpa only [hselected] using valid.verticalAllowed column boundary)).1
  have hflow := Signals.value_between
    (state := fun y => signalGrid column y)
    Signals.State.north Signals.State.south hrb
    (fun y _ _ => valid.vmatch column y)
    (fun y hry hyr => Signals.vertical_transmits_of_allowed (by
      have hnone := hbetween y hry hyr
      simpa only [hnone] using valid.verticalAllowed column y))
  exact hflow ▸ houter

theorem vertical_blocked_of_lower
    {indexGrid : Nat -> Nat -> Index}
    {shadeGrid : Nat -> Nat -> RedShades.State}
    {signalGrid : Nat -> Nat -> Signals.State}
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {column row boundary : Nat}
    (hbr : boundary < row)
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column boundary) (quadrantAt column boundary)
      (shadeGrid column boundary) = some .south)
    (hbetween : ∀ y, boundary < y -> y < row ->
      ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid column y) (quadrantAt column y)
        (shadeGrid column y) = none) :
    (signalGrid column row).south ≠ .none := by
  have houter : (signalGrid column boundary).north ≠ .none :=
    (Signals.vertical_interiorSouth_rules (by
      simpa only [hselected] using valid.verticalAllowed column boundary)).1
  have hflow := Signals.value_between
    (state := fun y => signalGrid column y)
    Signals.State.north Signals.State.south hbr
    (fun y _ _ => valid.vmatch column y)
    (fun y hby hyr => Signals.vertical_transmits_of_allowed (by
      have hnone := hbetween y hby hyr
      simpa only [hnone] using valid.verticalAllowed column y))
  exact hflow.symm ▸ houter

theorem horizontal_blocked_of_right
    {indexGrid : Nat -> Nat -> Index}
    {shadeGrid : Nat -> Nat -> RedShades.State}
    {signalGrid : Nat -> Nat -> Signals.State}
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {column row boundary : Nat}
    (hcb : column < boundary)
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid boundary row) (quadrantAt boundary row)
      (shadeGrid boundary row) = some .east)
    (hbetween : ∀ x, column < x -> x < boundary ->
      ShadedSignals.selectedVerticalFor
        (componentAt indexGrid x row) (quadrantAt x row)
        (shadeGrid x row) = none) :
    (signalGrid column row).east ≠ .none := by
  have houter : (signalGrid boundary row).west ≠ .none :=
    (Signals.horizontal_interiorEast_rules (by
      simpa only [hselected] using valid.horizontalAllowed boundary row)).1
  have hflow := Signals.value_between
    (state := fun x => signalGrid x row)
    Signals.State.east Signals.State.west hcb
    (fun x _ _ => valid.hmatch x row)
    (fun x hcx hxb => Signals.horizontal_transmits_of_allowed (by
      have hnone := hbetween x hcx hxb
      simpa only [hnone] using valid.horizontalAllowed x row))
  exact hflow ▸ houter

theorem horizontal_blocked_of_left
    {indexGrid : Nat -> Nat -> Index}
    {shadeGrid : Nat -> Nat -> RedShades.State}
    {signalGrid : Nat -> Nat -> Signals.State}
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    {column row boundary : Nat}
    (hbc : boundary < column)
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid boundary row) (quadrantAt boundary row)
      (shadeGrid boundary row) = some .west)
    (hbetween : ∀ x, boundary < x -> x < column ->
      ShadedSignals.selectedVerticalFor
        (componentAt indexGrid x row) (quadrantAt x row)
        (shadeGrid x row) = none) :
    (signalGrid column row).west ≠ .none := by
  have houter : (signalGrid boundary row).east ≠ .none :=
    (Signals.horizontal_interiorWest_rules (by
      simpa only [hselected] using valid.horizontalAllowed boundary row)).1
  have hflow := Signals.value_between
    (state := fun x => signalGrid x row)
    Signals.State.east Signals.State.west hbc
    (fun x _ _ => valid.hmatch x row)
    (fun x hbx hxc => Signals.horizontal_transmits_of_allowed (by
      have hnone := hbetween x hbx hxc
      simpa only [hnone] using valid.horizontalAllowed x row))
  exact hflow.symm ▸ houter

private theorem not_both_of_either_not {p q : Prop} :
    (¬p ∨ ¬q) → ¬(p ∧ q) := by
  aesop

theorem Geometry.crossingObstruction
    {indexGrid : Nat -> Nat -> Index}
    {shadeGrid : Nat -> Nat -> RedShades.State}
    {signalGrid : Nat -> Nat -> Signals.State}
    {west east south north : Nat}
    (geometry : Geometry indexGrid shadeGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid) :
    CrossingObstruction indexGrid shadeGrid signalGrid west east south north := by
  constructor
  · intro column row hwest heast hsouth hnorth hfreeRow hnotFreeColumn
    rcases geometry.verticalBoundary hwest heast hsouth hnorth
      hfreeRow hnotFreeColumn with hat | hupper | hlower
    · exact not_both_of_either_not (vertical_blocked_at_boundary valid hat)
    · rcases hupper with ⟨boundary, hrb, _, hselected, hbetween⟩
      exact not_both_of_either_not
        (Or.inr (vertical_blocked_of_upper valid hrb hselected hbetween))
    · rcases hlower with ⟨boundary, _, hbr, hselected, hbetween⟩
      exact not_both_of_either_not
        (Or.inl (vertical_blocked_of_lower valid hbr hselected hbetween))
  · intro column row hwest heast hsouth hnorth hfreeColumn hnotFreeRow
    rcases geometry.horizontalBoundary hwest heast hsouth hnorth
      hfreeColumn hnotFreeRow with hat | hright | hleft
    · exact not_both_of_either_not (horizontal_blocked_at_boundary valid hat)
    · rcases hright with ⟨boundary, hcb, _, hselected, hbetween⟩
      exact not_both_of_either_not
        (Or.inr (horizontal_blocked_of_right valid hcb hselected hbetween))
    · rcases hleft with ⟨boundary, _, hbc, hselected, hbetween⟩
      exact not_both_of_either_not
        (Or.inl (horizontal_blocked_of_left valid hbc hselected hbetween))

end ShadedObstructionGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
