/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedRoutedScaffoldForward
import LeanWang.OllingerRobinson104ShadedObstructionGeometryOddBaseBoundedSoundness

/-!
# Pair-cover recurrence for canonical Robinson boards

The two possible light boards are the even family beginning at depth one and
the odd family beginning at depth zero.  This module isolates the exact common
successor theorem and proves that the two resulting families discharge the
forward routed-scaffold cover obligation.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionPairCoverRecurrence

open RedCycles RedShadeCycles RedShadePaths ShadedFreeLineRecurrence
  ShadedObstructionGeometryCover ShadedRoutedScaffoldForward
  SparseFreeLinePlaneBase

set_option maxRecDepth 20000

/-- Every board of one phase and recurrence depth has audited pair covers in
every ambient coarse grid and valid shade decoration. -/
def Holds (phase : Phase) (depth : Nat) : Prop :=
  ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State),
    ValidShadeGrid (refinedGrid phase depth grid) shadeGrid →
      PairCover (refinedGrid phase depth grid) shadeGrid
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)

/-- A hierarchy hypothesis supplies the same canonical cover in every aligned
refinement block of an arbitrary ambient grid. -/
theorem Holds.at_block
    {phase : Phase} {depth : Nat} (holds : Holds phase depth)
    {grid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (refinedGrid phase depth grid) shadeGrid)
    (blockX blockY : Nat) :
    PairCover (refinedGrid phase depth grid) shadeGrid
      (2 ^ refinementDepth phase depth * blockX + west phase depth)
      (2 ^ refinementDepth phase depth * blockX + east phase depth)
      (2 ^ refinementDepth phase depth * blockY + west phase depth)
      (2 ^ refinementDepth phase depth * blockY + east phase depth) := by
  let quarterOffsetX :=
    2 ^ (refinementDepth phase depth + 1) * blockX
  let quarterOffsetY :=
    2 ^ (refinementDepth phase depth + 1) * blockY
  have localValid := ShadedFreeLineTranslation.validShadeGrid_shift
    (refinementDepth phase depth) grid (by
      simpa only [refinedGrid] using valid) blockX blockY
  have localCover := holds
    (RefinementTranslation.shiftGrid grid blockX blockY)
    (ShadedFreeLineTranslation.shiftQuarterGrid shadeGrid
      quarterOffsetX quarterOffsetY) (by
        simpa only [refinedGrid, quarterOffsetX, quarterOffsetY] using localValid)
  have translated := ShadedObstructionGeometryCover.PairCover.translate localCover
  simpa only [refinedGrid] using translated

/-- The existing translated depth-four audit is exactly the even base. -/
theorem even_one : Holds .even 1 := by
  intro grid shadeGrid valid
  have cover := pairCover_at_block grid (by
    simpa [refinedGrid, refinementDepth, Phase.extra] using valid) 0 0
  simpa [refinedGrid, refinementDepth, Phase.extra, west, east, scale,
    Phase.factor] using cover

/-- The checked odd obstruction audit supplies the odd base in every coarse
grid. -/
theorem odd_zero : Holds .odd 0 := by
  intro grid shadeGrid valid
  have valid' : ValidShadeGrid (iterateRefine 3 grid) shadeGrid := by
    simpa [refinedGrid, refinementDepth, Phase.extra] using valid
  have geometry :=
    ShadedObstructionGeometryOddBaseBoundedSoundness.geometry_shift
      grid valid' 0 0
  have cover := pairCover_of_geometry geometry
  have hgrid : RefinementTranslation.shiftGrid grid 0 0 = grid :=
    shiftGrid_zero grid
  have hshade : ShadedFreeLineTranslation.shiftQuarterGrid shadeGrid 0 0 =
      shadeGrid := by
    funext x y
    simp [ShadedFreeLineTranslation.shiftQuarterGrid]
  rw [hgrid, hshade] at cover
  simpa only [refinedGrid, refinementDepth, Phase.extra,
    west, east, scale, Phase.factor, pow_zero, mul_one] using cover

/-- One common two-substitution recurrence advances either shade phase. -/
def Step : Prop :=
  ∀ (phase : Phase) (depth : Nat), Holds phase depth → Holds phase (depth + 1)

theorem refinedGrid_succ (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) :
    refinedGrid phase (depth + 1) grid =
      iterateRefine 2 (refinedGrid phase depth grid) := by
  unfold refinedGrid
  rw [show refinementDepth phase (depth + 1) =
      2 + refinementDepth phase depth by
    simp [refinementDepth]
    omega]
  exact (PlaneRedBoards.iterateRefine_add 2
    (refinementDepth phase depth) grid).symm

/-- Refining the ambient grid commutes with the fixed hierarchy refinement. -/
theorem refinedGrid_iterateRefine_two (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) :
    refinedGrid phase depth (iterateRefine 2 grid) =
      iterateRefine 2 (refinedGrid phase depth grid) := by
  unfold refinedGrid
  rw [PlaneRedBoards.iterateRefine_add, PlaneRedBoards.iterateRefine_add]
  congr 1
  omega

/-- All aligned copies of the current hierarchy cover inside its two-level
refinement.  These are already covers of the fine shade grid; no geometry has
to be transported back from a projected coarse shade grid. -/
def ChildCovers (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State) : Prop :=
  ∀ blockX blockY,
    PairCover (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (2 ^ refinementDepth phase depth * blockX + west phase depth)
      (2 ^ refinementDepth phase depth * blockX + east phase depth)
      (2 ^ refinementDepth phase depth * blockY + west phase depth)
      (2 ^ refinementDepth phase depth * blockY + east phase depth)

/-- An induction hypothesis supplies every aligned child cover needed by the
successor board. -/
theorem Holds.childCovers
    {phase : Phase} {depth : Nat} (holds : Holds phase depth)
    {grid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid) :
    ChildCovers phase depth grid shadeGrid := by
  intro blockX blockY
  have valid' : ValidShadeGrid
      (refinedGrid phase depth (iterateRefine 2 grid)) shadeGrid := by
    rw [refinedGrid_iterateRefine_two]
    exact valid
  have cover := holds.at_block valid' blockX blockY
  simpa only [refinedGrid_iterateRefine_two] using cover

/-- A vertical query fits one aligned child board, including the horizontal
containment needed when that child's geometry is returned to the parent. -/
def FitsVerticalChild (phase : Phase) (depth column row boundary : Nat) : Prop :=
  ∃ blockX blockY,
    quarterWest (4 * west phase depth) ≤ quarterWest
      (2 ^ refinementDepth phase depth * blockX + west phase depth) ∧
    quarterEast
      (2 ^ refinementDepth phase depth * blockX + east phase depth) ≤
        quarterEast (4 * east phase depth) ∧
    quarterWest
      (2 ^ refinementDepth phase depth * blockX + west phase depth) < column ∧
    column < quarterEast
      (2 ^ refinementDepth phase depth * blockX + east phase depth) ∧
    quarterSouth
      (2 ^ refinementDepth phase depth * blockY + west phase depth) < row ∧
    row < quarterNorth
      (2 ^ refinementDepth phase depth * blockY + east phase depth) ∧
    quarterSouth
      (2 ^ refinementDepth phase depth * blockY + west phase depth) < boundary ∧
    boundary < quarterNorth
      (2 ^ refinementDepth phase depth * blockY + east phase depth)

/-- A horizontal query fits one aligned child board, including the vertical
containment needed when that child's geometry is returned to the parent. -/
def FitsHorizontalChild (phase : Phase) (depth column row boundary : Nat) : Prop :=
  ∃ blockX blockY,
    quarterSouth (4 * west phase depth) ≤ quarterSouth
      (2 ^ refinementDepth phase depth * blockY + west phase depth) ∧
    quarterNorth
      (2 ^ refinementDepth phase depth * blockY + east phase depth) ≤
        quarterNorth (4 * east phase depth) ∧
    quarterWest
      (2 ^ refinementDepth phase depth * blockX + west phase depth) < column ∧
    column < quarterEast
      (2 ^ refinementDepth phase depth * blockX + east phase depth) ∧
    quarterSouth
      (2 ^ refinementDepth phase depth * blockY + west phase depth) < row ∧
    row < quarterNorth
      (2 ^ refinementDepth phase depth * blockY + east phase depth) ∧
    quarterWest
      (2 ^ refinementDepth phase depth * blockX + west phase depth) < boundary ∧
    boundary < quarterEast
      (2 ^ refinementDepth phase depth * blockX + east phase depth)

def VerticalGeometryWitness (phase : Phase) (depth : Nat)
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (column row boundary : Nat) : Prop :=
  ∃ localWest localEast localSouth localNorth,
    quarterWest (4 * west phase depth) ≤ quarterWest localWest ∧
    quarterEast localEast ≤ quarterEast (4 * east phase depth) ∧
    quarterWest localWest < column ∧ column < quarterEast localEast ∧
    quarterSouth localSouth < row ∧ row < quarterNorth localNorth ∧
    quarterSouth localSouth < boundary ∧
    boundary < quarterNorth localNorth ∧
    ShadedObstructionGeometry.Geometry indexGrid shadeGrid
      localWest localEast localSouth localNorth

def HorizontalGeometryWitness (phase : Phase) (depth : Nat)
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (column row boundary : Nat) : Prop :=
  ∃ localWest localEast localSouth localNorth,
    quarterSouth (4 * west phase depth) ≤ quarterSouth localSouth ∧
    quarterNorth localNorth ≤ quarterNorth (4 * east phase depth) ∧
    quarterWest localWest < column ∧ column < quarterEast localEast ∧
    quarterSouth localSouth < row ∧ row < quarterNorth localNorth ∧
    quarterWest localWest < boundary ∧
    boundary < quarterEast localEast ∧
    ShadedObstructionGeometry.Geometry indexGrid shadeGrid
      localWest localEast localSouth localNorth

/-- The genuinely new local content at a successor level.  If a queried pair
does not fit one recursive child, a bounded seam argument chooses geometry
covering that particular pair. -/
structure SeamCover : Prop where
  vertical : ∀ (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    ChildCovers phase depth grid shadeGrid →
    quarterWest (4 * west phase depth) < column →
    column < quarterEast (4 * east phase depth) →
    quarterSouth (4 * west phase depth) < row →
    row < quarterNorth (4 * east phase depth) →
    quarterSouth (4 * west phase depth) < boundary →
    boundary < quarterNorth (4 * east phase depth) →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none →
    ¬FitsVerticalChild phase depth column row boundary →
    VerticalGeometryWitness phase depth
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      column row boundary
  horizontal : ∀ (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    ChildCovers phase depth grid shadeGrid →
    quarterWest (4 * west phase depth) < column →
    column < quarterEast (4 * east phase depth) →
    quarterSouth (4 * west phase depth) < row →
    row < quarterNorth (4 * east phase depth) →
    quarterWest (4 * west phase depth) < boundary →
    boundary < quarterEast (4 * east phase depth) →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none →
    ¬FitsHorizontalChild phase depth column row boundary →
    HorizontalGeometryWitness phase depth
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      column row boundary

/-- The remaining bounded combinatorial content of one recurrence step:
aligned child covers handle inherited regions, and a finite local audit only
has to cover the seams between them. -/
def ChildLift : Prop :=
  ∀ (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State),
    ValidShadeGrid
        (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    ChildCovers phase depth grid shadeGrid →
    PairCover (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
        (4 * west phase depth) (4 * east phase depth)
        (4 * west phase depth) (4 * east phase depth)

/-- Child covers discharge the recursive cases, leaving only seam covers. -/
theorem childLift_of_seamCover (seams : SeamCover) : ChildLift := by
  intro phase depth grid shadeGrid valid children
  apply PairCover.of_subcovers
  · intro column row boundary hwest heast hsouth hnorth
      hboundarySouth hboundaryNorth hselected
    by_cases fits : FitsVerticalChild phase depth column row boundary
    · rcases fits with ⟨blockX, blockY, houterWest, houterEast,
        hlocalWest, hlocalEast, hlocalSouth, hlocalNorth,
        hboundaryLocalSouth, hboundaryLocalNorth⟩
      exact ⟨_, _, _, _, houterWest, houterEast,
        hlocalWest, hlocalEast, hlocalSouth, hlocalNorth,
        hboundaryLocalSouth, hboundaryLocalNorth, children blockX blockY⟩
    · rcases seams.vertical phase depth grid shadeGrid valid children
        hwest heast hsouth hnorth hboundarySouth hboundaryNorth hselected fits
        with ⟨localWest, localEast, localSouth, localNorth,
          houterWest, houterEast, hlocalWest, hlocalEast,
          hlocalSouth, hlocalNorth, hboundaryLocalSouth,
          hboundaryLocalNorth, geometry⟩
      exact ⟨localWest, localEast, localSouth, localNorth,
        houterWest, houterEast, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hboundaryLocalSouth,
        hboundaryLocalNorth, pairCover_of_geometry geometry⟩
  · intro column row boundary hwest heast hsouth hnorth
      hboundaryWest hboundaryEast hselected
    by_cases fits : FitsHorizontalChild phase depth column row boundary
    · rcases fits with ⟨blockX, blockY, houterSouth, houterNorth,
        hlocalWest, hlocalEast, hlocalSouth, hlocalNorth,
        hboundaryLocalWest, hboundaryLocalEast⟩
      exact ⟨_, _, _, _, houterSouth, houterNorth,
        hlocalWest, hlocalEast, hlocalSouth, hlocalNorth,
        hboundaryLocalWest, hboundaryLocalEast, children blockX blockY⟩
    · rcases seams.horizontal phase depth grid shadeGrid valid children
        hwest heast hsouth hnorth hboundaryWest hboundaryEast hselected fits
        with ⟨localWest, localEast, localSouth, localNorth,
          houterSouth, houterNorth, hlocalWest, hlocalEast,
          hlocalSouth, hlocalNorth, hboundaryLocalWest,
          hboundaryLocalEast, geometry⟩
      exact ⟨localWest, localEast, localSouth, localNorth,
        houterSouth, houterNorth, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hboundaryLocalWest,
        hboundaryLocalEast, pairCover_of_geometry geometry⟩

/-- A bounded child-cover lift establishes the common recurrence step. -/
theorem step_of_childLift (lift : ChildLift) : Step := by
  intro phase depth holds grid shadeGrid valid
  have fineValid : ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid := by
    simpa only [refinedGrid_succ] using valid
  have children := holds.childCovers fineValid
  have fineCover := lift phase depth grid shadeGrid fineValid children
  simpa only [refinedGrid_succ, west_succ, east_succ] using fineCover

/-- Both phase families at every depth used by the unbounded-board theorem. -/
def AllHolds : Prop :=
  ∀ size : Nat, Holds .even (1 + size) ∧ Holds .odd size

theorem allHolds_of_bases_of_step
    (odd_zero : Holds .odd 0) (step : Step) : AllHolds := by
  intro size
  constructor
  · induction size with
    | zero => simpa using even_one
    | succ size ih =>
        simpa [Nat.add_assoc] using step .even (1 + size) ih
  · induction size with
    | zero => exact odd_zero
    | succ size ih => simpa using step .odd size ih

theorem allHolds_of_step (step : Step) : AllHolds :=
  allHolds_of_bases_of_step odd_zero step

set_option maxHeartbeats 1000000 in
-- Normalizing the even and odd recurrence grids against the common tower grid.
/-- The two complete pair-cover families supply the exact forward hierarchy
obligation. -/
theorem lightBoardPairCovers_of_allHolds
    (holds : AllHolds) : LightBoardPairCovers := by
  intro T seed x decoded size coarseOrigin
  let level := 2 * (1 + size)
  let coarse := ShadedPlaneShadeGrid.coarseGrid decoded
    (level + 2) coarseOrigin
  let state := ShadedPlaneShadeGrid.stateGrid decoded
    (ShadedPlaneShadeGrid.fineParentOrigin decoded
      (level + 2) coarseOrigin)
  have valid : ValidShadeGrid (iterateRefine (level + 2) coarse) state :=
    ShadedPlaneShadeGrid.refined_stateGrid_valid decoded
      (level + 2) coarseOrigin
  have hlargePow : 2 ^ level = 4 ^ (1 + size) := by
    dsimp [level]
    rw [pow_mul]
    norm_num
  have hsmallPow : 2 ^ (level - 1) = 2 * 4 ^ size := by
    dsimp [level]
    rw [show 2 * (1 + size) - 1 = 1 + 2 * size by omega, pow_add, pow_mul]
    norm_num
  have hdepthEven : refinementDepth .even (1 + size) = level + 2 := by
    simp [refinementDepth, Phase.extra, level]
  have hwestEven : west .even (1 + size) = 2 ^ level := by
    simp [west, scale, Phase.factor, hlargePow]
  have heastEven : east .even (1 + size) = 3 * 2 ^ level := by
    simp [east, scale, Phase.factor, hlargePow]
  let shifted := iterateRefine 1 coarse
  have hgridOdd : refinedGrid .odd size shifted =
      iterateRefine (level + 2) coarse := by
    unfold refinedGrid
    dsimp [shifted]
    rw [PlaneRedBoards.iterateRefine_add]
    congr 1
    simp [refinementDepth, Phase.extra, level]
    omega
  have hwestOdd : west .odd size = 2 ^ (level - 1) := by
    simp [west, scale, Phase.factor, hsmallPow]
  have heastOdd : east .odd size = 3 * 2 ^ (level - 1) := by
    simp [east, scale, Phase.factor, hsmallPow]
  have evenValid : ValidShadeGrid
      (refinedGrid .even (1 + size) coarse) state := by
    simpa only [refinedGrid, hdepthEven] using valid
  have oddValid : ValidShadeGrid (refinedGrid .odd size shifted) state := by
    rw [hgridOdd]
    exact valid
  have evenCover := (holds size).1 coarse state evenValid
  have oddCover := (holds size).2 shifted state oddValid
  constructor
  · intro _
    simpa only [refinedGrid, hdepthEven, hwestEven, heastEven] using evenCover
  · intro _
    simpa only [hgridOdd, hwestOdd, heastOdd] using oddCover

/-- The common recurrence is now the sole forward scaffold obligation. -/
theorem forcesRoutedFixedCornerSquares_of_step (step : Step) :
    ForcesRoutedFixedCornerSquares ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares
    (lightBoardPairCovers_of_allHolds
      (allHolds_of_step step))

end ShadedObstructionPairCoverRecurrence
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang

end
