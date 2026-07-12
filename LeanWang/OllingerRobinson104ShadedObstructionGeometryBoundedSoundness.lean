/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedObstructionGeometryBase
import LeanWang.OllingerRobinson104RedShadeGraphTranslation

/-!
# Transport the obstruction audit into a bounded target grid

The finite graph search never leaves its `32 x 32` window.  Consequently its
paths remain sound in any target grid with the same thick components inside
that window.  This is the interface needed for actual hierarchy neighborhoods,
whose surrounding coarse parents need not equal the audited parent.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionGeometryBoundedSoundness

open OrientedRedCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphTranslation RedShadeCycles
  RedShadeGraphRefinement RedShadePaths ShadedFreeLineGraphBase
  ShadedObstructionGeometryBaseAudit
  ShadedObstructionGeometryBaseSoundness Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem reachedWithParity_has_bounded_path
    (parent : Index) {port : Port} {parity : Bool}
    (hportX : port.x < 32)
    (hreached : reachedWithParity parent (reachedBitmap (nodes parent))
      port parity = true) :
    ∃ start ∈ boardPorts,
      BoundedPath (localGrid parent) 32 32 start port parity := by
  rcases ShadedObstructionGeometryBaseSoundness.reachedWithParity_has_node
      parent hportX hreached with ⟨node, hnode, hcurrent, hparity⟩
  have sound := exploreFast_bounded_sound
    (fun candidate hcandidate => boardPorts_inBounds hcandidate) hnode
  refine ⟨node.origin, sound.1, ?_⟩
  have path := sound.2
  rw [hcurrent, hparity] at path
  exact path

theorem value_eq_light_of_reached
    (parent : Index)
    {targetGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (componentsEq : ∀ x y, x < 32 → y < 32 →
      componentAt (localGrid parent) x y = componentAt targetGrid x y)
    (valid : ValidShadeGrid targetGrid stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn targetGrid 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    {port : Port} (hportX : port.x < 32)
    (hreached : reachedWithParity parent (reachedBitmap (nodes parent))
      port (!parentLight) = true) :
    value stateGrid port = some .light := by
  rcases reachedWithParity_has_bounded_path parent hportX hreached with
    ⟨start, hstart, path⟩
  have startValue := (onCycle_of_mem_boardPorts hstart).value_eq
    cycle shaded valid
  have targetPath :=
    RedShadeGraphTranslation.BoundedPath.congr_of_component_eq componentsEq path
  have relation := targetPath.path.sound valid
  cases parentLight with
  | false =>
      simp only [Bool.not_false, related_true_iff] at relation
      rcases relation with ⟨shade, hfirst, hfinish⟩
      have hshade : shade = .dark :=
        Option.some.inj (hfirst.symm.trans startValue)
      subst shade
      simpa [RedShades.Shade.opposite] using hfinish
  | true =>
      simp only [Bool.not_true, related_false_iff] at relation
      exact relation.symm.trans startValue

theorem value_eq_dark_of_reached
    (parent : Index)
    {targetGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (componentsEq : ∀ x y, x < 32 → y < 32 →
      componentAt (localGrid parent) x y = componentAt targetGrid x y)
    (valid : ValidShadeGrid targetGrid stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn targetGrid 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    {port : Port} (hportX : port.x < 32)
    (hreached : reachedWithParity parent (reachedBitmap (nodes parent))
      port parentLight = true) :
    value stateGrid port = some .dark := by
  rcases reachedWithParity_has_bounded_path parent hportX hreached with
    ⟨start, hstart, path⟩
  have startValue := (onCycle_of_mem_boardPorts hstart).value_eq
    cycle shaded valid
  have targetPath :=
    RedShadeGraphTranslation.BoundedPath.congr_of_component_eq componentsEq path
  have relation := targetPath.path.sound valid
  cases parentLight with
  | false =>
      simp only [related_false_iff] at relation
      exact relation.symm.trans startValue
  | true =>
      simp only [related_true_iff] at relation
      rcases relation with ⟨shade, hfirst, hfinish⟩
      have hshade : shade = .light :=
        Option.some.inj (hfirst.symm.trans startValue)
      subst shade
      simpa [RedShades.Shade.opposite] using hfinish

private theorem horizontalShade_eq_light_of_east
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.VerticalInterior}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hinterior : Signals.horizontalInterior? component quadrant = some interior)
    (heast : state.east = some .light) :
    ShadedSignals.horizontalShade? state = some .light := by
  rcases state with ⟨west, east, south, north⟩
  cases component <;> cases quadrant <;>
    simp_all [RedShades.allowedFor, RedShades.hasWest, RedShades.hasEast,
      RedShades.hasSouth, RedShades.hasNorth, RedShades.hasHorizontal,
      RedShades.hasVertical, RedShades.cornerWest, RedShades.cornerEast,
      RedShades.cornerSouth, RedShades.cornerNorth, RedShades.optionPresent,
      QuarterGeometry.redHorizontalAt, QuarterGeometry.redVerticalAt,
      QuarterGeometry.containsLine, Figure16.Thick.lineSum?, Quadrant.xBit,
      Quadrant.yBit, Signals.horizontalInterior?,
      ShadedSignals.horizontalShade?]

private theorem verticalShade_eq_light_of_north
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.HorizontalInterior}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hinterior : Signals.verticalInterior? component quadrant = some interior)
    (hnorth : state.north = some .light) :
    ShadedSignals.verticalShade? state = some .light := by
  rcases state with ⟨west, east, south, north⟩
  cases component <;> cases quadrant <;>
    simp_all [RedShades.allowedFor, RedShades.hasWest, RedShades.hasEast,
      RedShades.hasSouth, RedShades.hasNorth, RedShades.hasHorizontal,
      RedShades.hasVertical, RedShades.cornerWest, RedShades.cornerEast,
      RedShades.cornerSouth, RedShades.cornerNorth, RedShades.optionPresent,
      QuarterGeometry.redHorizontalAt, QuarterGeometry.redVerticalAt,
      QuarterGeometry.containsLine, Figure16.Thick.lineSum?, Quadrant.xBit,
      Quadrant.yBit, Signals.verticalInterior?, ShadedSignals.verticalShade?]

theorem selectedHorizontal_semantic
    (parent : Index)
    {targetGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (componentsEq : ∀ x y, x < 32 → y < 32 →
      componentAt (localGrid parent) x y = componentAt targetGrid x y)
    (valid : ValidShadeGrid targetGrid stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn targetGrid 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hselected : selectedHorizontal parent (reachedBitmap (nodes parent))
      parentLight column row = true) :
    ShadedSignals.selectedHorizontalFor
      (componentAt targetGrid column row) (quadrantAt column row)
      (stateGrid column row) ≠ none := by
  have hcolumnBound :=
    (ShadedObstructionGeometryBaseSoundness.mem_coordinates_iff.1 hcolumn).2.trans
      (by decide : 24 < 32)
  have hrowBound :=
    (ShadedObstructionGeometryBaseSoundness.mem_coordinates_iff.1 hrow).2.trans
      (by decide : 24 < 32)
  have hparts :
      (Signals.horizontalInterior? (componentAt (localGrid parent) column row)
        (quadrantAt column row)).isSome = true ∧
      (reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .west⟩ (!parentLight) = true ∨
        reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .east⟩ (!parentLight) = true) := by
    simpa only [selectedHorizontal, Bool.and_eq_true, Bool.or_eq_true] using hselected
  cases hinterior : Signals.horizontalInterior?
      (componentAt (localGrid parent) column row) (quadrantAt column row) with
  | none => simp [hinterior] at hparts
  | some interior =>
      have hinteriorTarget : Signals.horizontalInterior?
          (componentAt targetGrid column row) (quadrantAt column row) =
          some interior := by
        rw [← componentsEq column row hcolumnBound hrowBound]
        exact hinterior
      have hshade : ShadedSignals.horizontalShade? (stateGrid column row) =
          some .light := by
        rcases hparts.2 with hwest | heast
        · have hwestLight : (stateGrid column row).west = some .light := by
            simpa only [value] using value_eq_light_of_reached parent componentsEq
              valid parentLight cycle shaded hcolumnBound hwest
          simp [ShadedSignals.horizontalShade?, hwestLight]
        · have heastLight : (stateGrid column row).east = some .light := by
            simpa only [value] using value_eq_light_of_reached parent componentsEq
              valid parentLight cycle shaded hcolumnBound heast
          have hallowed := valid.allowed column row
          unfold RedShades.locallyAllowed at hallowed
          dsimp only at hallowed
          exact horizontalShade_eq_light_of_east hallowed hinteriorTarget heastLight
      simp [ShadedSignals.selectedHorizontalFor, hshade, hinteriorTarget]

theorem selectedVertical_semantic
    (parent : Index)
    {targetGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (componentsEq : ∀ x y, x < 32 → y < 32 →
      componentAt (localGrid parent) x y = componentAt targetGrid x y)
    (valid : ValidShadeGrid targetGrid stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn targetGrid 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hselected : selectedVertical parent (reachedBitmap (nodes parent))
      parentLight column row = true) :
    ShadedSignals.selectedVerticalFor
      (componentAt targetGrid column row) (quadrantAt column row)
      (stateGrid column row) ≠ none := by
  have hcolumnBound :=
    (ShadedObstructionGeometryBaseSoundness.mem_coordinates_iff.1 hcolumn).2.trans
      (by decide : 24 < 32)
  have hrowBound :=
    (ShadedObstructionGeometryBaseSoundness.mem_coordinates_iff.1 hrow).2.trans
      (by decide : 24 < 32)
  have hparts :
      (Signals.verticalInterior? (componentAt (localGrid parent) column row)
        (quadrantAt column row)).isSome = true ∧
      (reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .south⟩ (!parentLight) = true ∨
        reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .north⟩ (!parentLight) = true) := by
    simpa only [selectedVertical, Bool.and_eq_true, Bool.or_eq_true] using hselected
  cases hinterior : Signals.verticalInterior?
      (componentAt (localGrid parent) column row) (quadrantAt column row) with
  | none => simp [hinterior] at hparts
  | some interior =>
      have hinteriorTarget : Signals.verticalInterior?
          (componentAt targetGrid column row) (quadrantAt column row) =
          some interior := by
        rw [← componentsEq column row hcolumnBound hrowBound]
        exact hinterior
      have hshade : ShadedSignals.verticalShade? (stateGrid column row) =
          some .light := by
        rcases hparts.2 with hsouth | hnorth
        · have hsouthLight : (stateGrid column row).south = some .light := by
            simpa only [value] using value_eq_light_of_reached parent componentsEq
              valid parentLight cycle shaded hcolumnBound hsouth
          simp [ShadedSignals.verticalShade?, hsouthLight]
        · have hnorthLight : (stateGrid column row).north = some .light := by
            simpa only [value] using value_eq_light_of_reached parent componentsEq
              valid parentLight cycle shaded hcolumnBound hnorth
          have hallowed := valid.allowed column row
          unfold RedShades.locallyAllowed at hallowed
          dsimp only at hallowed
          exact verticalShade_eq_light_of_north hallowed hinteriorTarget hnorthLight
      simp [ShadedSignals.selectedVerticalFor, hshade, hinteriorTarget]

private theorem horizontal_not_reached_same
    (parent : Index)
    {targetGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (componentsEq : ∀ x y, x < 32 → y < 32 →
      componentAt (localGrid parent) x y = componentAt targetGrid x y)
    (valid : ValidShadeGrid targetGrid stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn targetGrid 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    {column row : Nat} (hcolumnBound : column < 32)
    (hrowBound : row < 32) {side : Side}
    (hside : side = .west ∨ side = .east)
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt targetGrid column row) (quadrantAt column row)
      (stateGrid column row) ≠ none)
    (hreached : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, side⟩ parentLight = true) : False := by
  have hdark := value_eq_dark_of_reached parent componentsEq valid parentLight
    cycle shaded hcolumnBound hreached
  have hallowed := valid.allowed column row
  unfold RedShades.locallyAllowed at hallowed
  dsimp only at hallowed
  rcases hside with rfl | rfl
  · have hparts :
        (reachedBitmap (nodes parent))[stateCode 32
          (⟨column, row, .west⟩, parentLight)]?.getD false = true ∧
        portPresent (localGrid parent) ⟨column, row, .west⟩ = true := by
      simpa only [reachedWithParity, Bool.and_eq_true] using hreached
    have hwestLocal : RedShades.hasWest
        (componentAt (localGrid parent) column row) (quadrantAt column row) = true := by
      simpa only [portPresent] using hparts.2
    have hwest : RedShades.hasWest
        (componentAt targetGrid column row) (quadrantAt column row) = true := by
      rw [← componentsEq column row hcolumnBound hrowBound]
      exact hwestLocal
    have hlight := horizontal_west_light_of_selected hallowed hselected hwest
    simp only [value] at hdark
    simp_all
  · have hparts :
        (reachedBitmap (nodes parent))[stateCode 32
          (⟨column, row, .east⟩, parentLight)]?.getD false = true ∧
        portPresent (localGrid parent) ⟨column, row, .east⟩ = true := by
      simpa only [reachedWithParity, Bool.and_eq_true] using hreached
    have heastLocal : RedShades.hasEast
        (componentAt (localGrid parent) column row) (quadrantAt column row) = true := by
      simpa only [portPresent] using hparts.2
    have heast : RedShades.hasEast
        (componentAt targetGrid column row) (quadrantAt column row) = true := by
      rw [← componentsEq column row hcolumnBound hrowBound]
      exact heastLocal
    have hlight := horizontal_east_light_of_selected hallowed hselected heast
    simp only [value] at hdark
    simp_all

private theorem vertical_not_reached_same
    (parent : Index)
    {targetGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (componentsEq : ∀ x y, x < 32 → y < 32 →
      componentAt (localGrid parent) x y = componentAt targetGrid x y)
    (valid : ValidShadeGrid targetGrid stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn targetGrid 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    {column row : Nat} (hcolumnBound : column < 32)
    (hrowBound : row < 32) {side : Side}
    (hside : side = .south ∨ side = .north)
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt targetGrid column row) (quadrantAt column row)
      (stateGrid column row) ≠ none)
    (hreached : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, side⟩ parentLight = true) : False := by
  have hdark := value_eq_dark_of_reached parent componentsEq valid parentLight
    cycle shaded hcolumnBound hreached
  have hallowed := valid.allowed column row
  unfold RedShades.locallyAllowed at hallowed
  dsimp only at hallowed
  rcases hside with rfl | rfl
  · have hparts :
        (reachedBitmap (nodes parent))[stateCode 32
          (⟨column, row, .south⟩, parentLight)]?.getD false = true ∧
        portPresent (localGrid parent) ⟨column, row, .south⟩ = true := by
      simpa only [reachedWithParity, Bool.and_eq_true] using hreached
    have hsouthLocal : RedShades.hasSouth
        (componentAt (localGrid parent) column row) (quadrantAt column row) = true := by
      simpa only [portPresent] using hparts.2
    have hsouth : RedShades.hasSouth
        (componentAt targetGrid column row) (quadrantAt column row) = true := by
      rw [← componentsEq column row hcolumnBound hrowBound]
      exact hsouthLocal
    have hlight := vertical_south_light_of_selected hallowed hselected hsouth
    simp only [value] at hdark
    simp_all
  · have hparts :
        (reachedBitmap (nodes parent))[stateCode 32
          (⟨column, row, .north⟩, parentLight)]?.getD false = true ∧
        portPresent (localGrid parent) ⟨column, row, .north⟩ = true := by
      simpa only [reachedWithParity, Bool.and_eq_true] using hreached
    have hnorthLocal : RedShades.hasNorth
        (componentAt (localGrid parent) column row) (quadrantAt column row) = true := by
      simpa only [portPresent] using hparts.2
    have hnorth : RedShades.hasNorth
        (componentAt targetGrid column row) (quadrantAt column row) = true := by
      rw [← componentsEq column row hcolumnBound hrowBound]
      exact hnorthLocal
    have hlight := vertical_north_light_of_selected hallowed hselected hnorth
    simp only [value] at hdark
    simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Coverage elimination expands four parity alternatives and endpoint contradictions.
theorem selectedHorizontal_of_semantic
    (parent : Index)
    {targetGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (componentsEq : ∀ x y, x < 32 → y < 32 →
      componentAt (localGrid parent) x y = componentAt targetGrid x y)
    (valid : ValidShadeGrid targetGrid stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn targetGrid 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt targetGrid column row) (quadrantAt column row)
      (stateGrid column row) ≠ none) :
    selectedHorizontal parent (reachedBitmap (nodes parent))
      parentLight column row = true := by
  have hcolumnBound := (mem_coordinates_iff.1 hcolumn).2.trans
    (by decide : 24 < 32)
  have hrowBound := (mem_coordinates_iff.1 hrow).2.trans
    (by decide : 24 < 32)
  have hinteriorTarget := horizontalInterior_isSome_of_selected hselected
  have hinteriorLocal :
      (Signals.horizontalInterior? (componentAt (localGrid parent) column row)
        (quadrantAt column row)).isSome = true := by
    rw [componentsEq column row hcolumnBound hrowBound]
    exact hinteriorTarget
  have hcovered := coverage.horizontal hcolumn hrow hinteriorLocal
  by_cases hwest : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, .west⟩ (!parentLight) = true
  · simp [selectedHorizontal, hinteriorLocal, hwest]
  by_cases heast : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, .east⟩ (!parentLight) = true
  · simp [selectedHorizontal, hinteriorLocal, heast]
  have hsame :
      reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .west⟩ parentLight = true ∨
        reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .east⟩ parentLight = true := by
    cases parentLight
    · simp only [Bool.not_false] at hwest heast
      rcases hcovered with ((hwestSame | hwestOpposite) | heastSame) |
        heastOpposite
      · exact Or.inl hwestSame
      · exact (hwest hwestOpposite).elim
      · exact Or.inr heastSame
      · exact (heast heastOpposite).elim
    · simp only [Bool.not_true] at hwest heast
      rcases hcovered with ((hwestOpposite | hwestSame) | heastOpposite) |
        heastSame
      · exact (hwest hwestOpposite).elim
      · exact Or.inl hwestSame
      · exact (heast heastOpposite).elim
      · exact Or.inr heastSame
  rcases hsame with hsame | hsame
  · exact False.elim (horizontal_not_reached_same parent componentsEq valid
      parentLight cycle shaded hcolumnBound hrowBound (Or.inl rfl) hselected hsame)
  · exact False.elim (horizontal_not_reached_same parent componentsEq valid
      parentLight cycle shaded hcolumnBound hrowBound (Or.inr rfl) hselected hsame)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Coverage elimination expands four parity alternatives and endpoint contradictions.
theorem selectedVertical_of_semantic
    (parent : Index)
    {targetGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (componentsEq : ∀ x y, x < 32 → y < 32 →
      componentAt (localGrid parent) x y = componentAt targetGrid x y)
    (valid : ValidShadeGrid targetGrid stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn targetGrid 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt targetGrid column row) (quadrantAt column row)
      (stateGrid column row) ≠ none) :
    selectedVertical parent (reachedBitmap (nodes parent))
      parentLight column row = true := by
  have hcolumnBound := (mem_coordinates_iff.1 hcolumn).2.trans
    (by decide : 24 < 32)
  have hrowBound := (mem_coordinates_iff.1 hrow).2.trans
    (by decide : 24 < 32)
  have hinteriorTarget := verticalInterior_isSome_of_selected hselected
  have hinteriorLocal :
      (Signals.verticalInterior? (componentAt (localGrid parent) column row)
        (quadrantAt column row)).isSome = true := by
    rw [componentsEq column row hcolumnBound hrowBound]
    exact hinteriorTarget
  have hcovered := coverage.vertical hcolumn hrow hinteriorLocal
  by_cases hsouth : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, .south⟩ (!parentLight) = true
  · simp [selectedVertical, hinteriorLocal, hsouth]
  by_cases hnorth : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, .north⟩ (!parentLight) = true
  · simp [selectedVertical, hinteriorLocal, hnorth]
  have hsame :
      reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .south⟩ parentLight = true ∨
        reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .north⟩ parentLight = true := by
    cases parentLight
    · simp only [Bool.not_false] at hsouth hnorth
      rcases hcovered with ((hsouthSame | hsouthOpposite) | hnorthSame) |
        hnorthOpposite
      · exact Or.inl hsouthSame
      · exact (hsouth hsouthOpposite).elim
      · exact Or.inr hnorthSame
      · exact (hnorth hnorthOpposite).elim
    · simp only [Bool.not_true] at hsouth hnorth
      rcases hcovered with ((hsouthOpposite | hsouthSame) | hnorthOpposite) |
        hnorthSame
      · exact (hsouth hsouthOpposite).elim
      · exact Or.inl hsouthSame
      · exact (hnorth hnorthOpposite).elim
      · exact Or.inr hnorthSame
  rcases hsame with hsame | hsame
  · exact False.elim (vertical_not_reached_same parent componentsEq valid
      parentLight cycle shaded hcolumnBound hrowBound (Or.inl rfl) hselected hsame)
  · exact False.elim (vertical_not_reached_same parent componentsEq valid
      parentLight cycle shaded hcolumnBound hrowBound (Or.inr rfl) hselected hsame)

theorem selectedHorizontal_iff_semantic
    (parent : Index)
    {targetGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (componentsEq : ∀ x y, x < 32 → y < 32 →
      componentAt (localGrid parent) x y = componentAt targetGrid x y)
    (valid : ValidShadeGrid targetGrid stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn targetGrid 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates) :
    selectedHorizontal parent (reachedBitmap (nodes parent))
        parentLight column row = true ↔
      ShadedSignals.selectedHorizontalFor
        (componentAt targetGrid column row) (quadrantAt column row)
        (stateGrid column row) ≠ none := by
  constructor
  · exact selectedHorizontal_semantic parent componentsEq valid parentLight
      cycle shaded hcolumn hrow
  · exact selectedHorizontal_of_semantic parent componentsEq valid parentLight
      cycle shaded coverage hcolumn hrow

theorem selectedVertical_iff_semantic
    (parent : Index)
    {targetGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (componentsEq : ∀ x y, x < 32 → y < 32 →
      componentAt (localGrid parent) x y = componentAt targetGrid x y)
    (valid : ValidShadeGrid targetGrid stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn targetGrid 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates) :
    selectedVertical parent (reachedBitmap (nodes parent))
        parentLight column row = true ↔
      ShadedSignals.selectedVerticalFor
        (componentAt targetGrid column row) (quadrantAt column row)
        (stateGrid column row) ≠ none := by
  constructor
  · exact selectedVertical_semantic parent componentsEq valid parentLight
      cycle shaded hcolumn hrow
  · exact selectedVertical_of_semantic parent componentsEq valid parentLight
      cycle shaded coverage hcolumn hrow

end ShadedObstructionGeometryBoundedSoundness
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
