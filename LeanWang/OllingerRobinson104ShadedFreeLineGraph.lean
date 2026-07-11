/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphBoards
import LeanWang.OllingerRobinson104ShadedLightBoardFreeLines

/-!
Turn odd red-path reachability from a light board into free rows and columns.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineGraph

open OrientedRedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadePaths ShadedPlaneSignalGrid Signals.FreeCellLocal

set_option maxRecDepth 20000

set_option linter.flexible false in
theorem hasVertical_of_interior_of_both_present
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (interior : Signals.verticalInterior? component quadrant ≠ none)
    (southPresent : state.south.isSome = true)
    (northPresent : state.north.isSome = true) :
    RedShades.hasVertical component quadrant = true := by
  cases component <;> cases quadrant <;>
    simp_all [RedShades.allowedFor, Signals.verticalInterior?,
      RedShades.hasVertical, RedShades.hasSouth, RedShades.hasNorth,
      RedShades.cornerSouth, RedShades.cornerNorth, RedShades.optionPresent]

set_option linter.flexible false in
theorem hasHorizontal_of_interior_of_both_present
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (interior : Signals.horizontalInterior? component quadrant ≠ none)
    (westPresent : state.west.isSome = true)
    (eastPresent : state.east.isSome = true) :
    RedShades.hasHorizontal component quadrant = true := by
  cases component <;> cases quadrant <;>
    simp_all [RedShades.allowedFor, Signals.horizontalInterior?,
      RedShades.hasHorizontal, RedShades.hasWest, RedShades.hasEast,
      RedShades.cornerWest, RedShades.cornerEast, RedShades.optionPresent]

theorem selectedVerticalFor_eq_none_of_dark
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (interior : Signals.verticalInterior? component quadrant ≠ none)
    (dark : state.south = some .dark ∨ state.north = some .dark) :
    ShadedSignals.selectedVerticalFor component quadrant state = none := by
  rcases dark with hsouth | hnorth
  · simp [ShadedSignals.selectedVerticalFor,
      ShadedSignals.verticalShade?, hsouth]
  · cases hsouth : state.south with
    | none =>
        simp [ShadedSignals.selectedVerticalFor,
          ShadedSignals.verticalShade?, hsouth, hnorth]
    | some southShade =>
        have hvertical := hasVertical_of_interior_of_both_present
          allowed interior (by simp [hsouth]) (by simp [hnorth])
        have heq := RedShades.vertical_eq_of_allowedFor allowed hvertical
        have hsouthDark : state.south = some .dark := heq.trans hnorth
        simp [ShadedSignals.selectedVerticalFor,
          ShadedSignals.verticalShade?, hsouthDark]

theorem selectedHorizontalFor_eq_none_of_dark
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (interior : Signals.horizontalInterior? component quadrant ≠ none)
    (dark : state.west = some .dark ∨ state.east = some .dark) :
    ShadedSignals.selectedHorizontalFor component quadrant state = none := by
  rcases dark with hwest | heast
  · simp [ShadedSignals.selectedHorizontalFor,
      ShadedSignals.horizontalShade?, hwest]
  · cases hwest : state.west with
    | none =>
        simp [ShadedSignals.selectedHorizontalFor,
          ShadedSignals.horizontalShade?, hwest, heast]
    | some westShade =>
        have hhorizontal := hasHorizontal_of_interior_of_both_present
          allowed interior (by simp [hwest]) (by simp [heast])
        have heq := RedShades.horizontal_eq_of_allowedFor allowed hhorizontal
        have hwestDark : state.west = some .dark := heq.trans heast
        simp [ShadedSignals.selectedHorizontalFor,
          ShadedSignals.horizontalShade?, hwestDark]

/-- Every perpendicular red segment on a row reaches the light board oddly. -/
def RowCertificate (grid : Nat → Nat → Index)
    (west east south north row : Nat) : Prop :=
  ∀ quarterX, quarterWest west < quarterX → quarterX < quarterEast east →
    Signals.verticalInterior?
        (componentAt grid quarterX row) (quadrantAt quarterX row) ≠ none →
      ∃ start : Port,
        OnCycle west east south north start ∧
          (Path grid start ⟨quarterX, row, .south⟩ true ∨
            Path grid start ⟨quarterX, row, .north⟩ true)

/-- Every perpendicular red segment on a column reaches the light board oddly. -/
def ColumnCertificate (grid : Nat → Nat → Index)
    (west east south north column : Nat) : Prop :=
  ∀ quarterY, quarterSouth south < quarterY → quarterY < quarterNorth north →
    Signals.horizontalInterior?
        (componentAt grid column quarterY) (quadrantAt column quarterY) ≠ none →
      ∃ start : Port,
        OnCycle west east south north start ∧
          (Path grid start ⟨column, quarterY, .west⟩ true ∨
            Path grid start ⟨column, quarterY, .east⟩ true)

theorem isFreeRow_of_certificate
    {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    {west east south north row : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (cycle : CycleOn grid west east south north)
    (shaded : CycleShade stateGrid west east south north .light)
    (certificate : RowCertificate grid west east south north row) :
    IsFreeRow grid stateGrid west east row := by
  intro quarterX hwest heast
  by_cases hinterior : Signals.verticalInterior?
      (componentAt grid quarterX row) (quadrantAt quarterX row) = none
  · exact ShadedSignals.selectedVerticalFor_of_none _ hinterior
  · rcases certificate quarterX hwest heast hinterior with
      ⟨start, onCycle, path | path⟩
    · have hdark := dark_at_end_of_light_cycle
        valid cycle shaded onCycle path
      have hallowed : RedShades.allowedFor
          (componentAt grid quarterX row) (quadrantAt quarterX row)
          (stateGrid quarterX row) = true := by
        simpa only [RedShades.locallyAllowed, componentAt] using
          valid.allowed quarterX row
      exact selectedVerticalFor_eq_none_of_dark hallowed hinterior
        (Or.inl (by simpa only [value] using hdark))
    · have hdark := dark_at_end_of_light_cycle
        valid cycle shaded onCycle path
      have hallowed : RedShades.allowedFor
          (componentAt grid quarterX row) (quadrantAt quarterX row)
          (stateGrid quarterX row) = true := by
        simpa only [RedShades.locallyAllowed, componentAt] using
          valid.allowed quarterX row
      exact selectedVerticalFor_eq_none_of_dark hallowed hinterior
        (Or.inr (by simpa only [value] using hdark))

theorem isFreeColumn_of_certificate
    {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    {west east south north column : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (cycle : CycleOn grid west east south north)
    (shaded : CycleShade stateGrid west east south north .light)
    (certificate : ColumnCertificate grid west east south north column) :
    IsFreeColumn grid stateGrid south north column := by
  intro quarterY hsouth hnorth
  by_cases hinterior : Signals.horizontalInterior?
      (componentAt grid column quarterY) (quadrantAt column quarterY) = none
  · exact ShadedSignals.selectedHorizontalFor_of_none _ hinterior
  · rcases certificate quarterY hsouth hnorth hinterior with
      ⟨start, onCycle, path | path⟩
    · have hdark := dark_at_end_of_light_cycle
        valid cycle shaded onCycle path
      have hallowed : RedShades.allowedFor
          (componentAt grid column quarterY) (quadrantAt column quarterY)
          (stateGrid column quarterY) = true := by
        simpa only [RedShades.locallyAllowed, componentAt] using
          valid.allowed column quarterY
      exact selectedHorizontalFor_eq_none_of_dark hallowed hinterior
        (Or.inl (by simpa only [value] using hdark))
    · have hdark := dark_at_end_of_light_cycle
        valid cycle shaded onCycle path
      have hallowed : RedShades.allowedFor
          (componentAt grid column quarterY) (quadrantAt column quarterY)
          (stateGrid column quarterY) = true := by
        simpa only [RedShades.locallyAllowed, componentAt] using
          valid.allowed column quarterY
      exact selectedHorizontalFor_eq_none_of_dark hallowed hinterior
        (Or.inr (by simpa only [value] using hdark))

end ShadedFreeLineGraph
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
