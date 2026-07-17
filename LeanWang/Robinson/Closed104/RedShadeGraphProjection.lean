/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphPathRefinement

/-!
# Project refined red-shade grids to their sparse coarse copy

The side-sensitive refined port of a coarse red edge has exactly the same
incidence as the original edge.  This finite fact is the local foundation for
projecting a valid shade decoration through two substitutions.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphProjection

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphTranslation
  RedShadePaths RefinementTranslation Signals.FreeCellLocal

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
/-- Every east/north external macro port preserves its coarse incidence. -/
theorem externalPort_present_eq_all :
    ∀ (parent : Index) (side : ExitSide) (offset : Fin 2),
      portPresent (fineGrid parent) (externalPort side offset) =
        portPresent (coarseGrid parent) (internalPort side offset) := by
  intro parent side offset
  cases side <;> fin_cases offset <;> revert parent <;> native_decide

theorem externalPort_present_eq
    (parent : Index) (side : ExitSide) (offset : Nat)
    (hoffset : offset < 2) :
    portPresent (fineGrid parent) (externalPort side offset) =
      portPresent (coarseGrid parent) (internalPort side offset) := by
  simpa using externalPort_present_eq_all parent side ⟨offset, hoffset⟩

/-- Literal sparse copies preserve all four red-port incidences. -/
theorem portPresent_sparsePort
    (grid : Nat → Nat → Index) (port : Port) :
    portPresent (iterateRefine 2 grid) (sparsePort port) =
      portPresent grid port := by
  rcases port with ⟨x, y, side⟩
  cases side <;>
    simp [portPresent, sparsePort, componentAt_iterateRefine_two_sparse,
      quadrantAt_sparseCoordinate]

theorem portPresent_shift_eq_constant
    (grid : Nat → Nat → Index) (blockX blockY : Nat) (port : Port)
    (hx : port.x < 8) (hy : port.y < 8) :
    portPresent (iterateRefine 2 (shiftGrid grid blockX blockY)) port =
      portPresent (fineGrid (grid blockX blockY)) port := by
  rcases port with ⟨x, y, side⟩
  cases side <;> simp only [portPresent] <;>
    rw [componentAt_shift_eq_constant 2 grid blockX blockY x y hx hy]
  all_goals rfl

/-- The side-sensitive image of every coarse port preserves its incidence. -/
theorem portPresent_refinedPort
    (grid : Nat → Nat → Index) (port : Port) :
    portPresent (iterateRefine 2 grid) (refinedPort port) =
      portPresent grid port := by
  cases hside : port.side with
  | west => simpa [refinedPort, hside] using portPresent_sparsePort grid port
  | south => simpa [refinedPort, hside] using portPresent_sparsePort grid port
  | east =>
      by_cases hexit : localCoordinate port.x = 1
      · let blockX := port.x / 2
        let blockY := port.y / 2
        let offset := localCoordinate port.y
        have hoffset : offset < 2 := localCoordinate_lt_two port.y
        have hlocal := portPresent_shift_eq_constant grid blockX blockY
          (externalPort .east offset) (by simp [externalPort]) (by simp [externalPort]; omega)
        have htranslate := portPresent_translate 2 grid blockX blockY
          (externalPort .east offset)
        have hfinite := externalPort_present_eq (grid blockX blockY)
          .east offset hoffset
        have hcoarse : portPresent (coarseGrid (grid blockX blockY))
            (internalPort .east offset) = portPresent grid port := by
          simpa [blockX, blockY, offset, internalPort, hside, hexit] using
            portPresent_coarseGrid_local grid port
        simpa [refinedPort, hside, exitCoordinate, hexit, blockX, blockY,
          offset, externalPort, internalPort, translatePort, sparseCoordinate,
          macroOrigin]
          using htranslate.symm.trans (hlocal.trans (hfinite.trans hcoarse))
      · have hrefined : refinedPort port = sparsePort port := by
          rcases port with ⟨portX, portY, portSide⟩
          simp_all [refinedPort, exitCoordinate, sparsePort]
        rw [hrefined]
        exact portPresent_sparsePort grid port
  | north =>
      by_cases hexit : localCoordinate port.y = 1
      · let blockX := port.x / 2
        let blockY := port.y / 2
        let offset := localCoordinate port.x
        have hoffset : offset < 2 := localCoordinate_lt_two port.x
        have hlocal := portPresent_shift_eq_constant grid blockX blockY
          (externalPort .north offset) (by simp [externalPort]; omega) (by simp [externalPort])
        have htranslate := portPresent_translate 2 grid blockX blockY
          (externalPort .north offset)
        have hfinite := externalPort_present_eq (grid blockX blockY)
          .north offset hoffset
        have hcoarse : portPresent (coarseGrid (grid blockX blockY))
            (internalPort .north offset) = portPresent grid port := by
          simpa [blockX, blockY, offset, internalPort, hside, hexit] using
            portPresent_coarseGrid_local grid port
        simpa [refinedPort, hside, exitCoordinate, hexit, blockX, blockY,
          offset, externalPort, internalPort, translatePort, sparseCoordinate,
          macroOrigin]
          using htranslate.symm.trans (hlocal.trans (hfinite.trans hcoarse))
      · have hrefined : refinedPort port = sparsePort port := by
          rcases port with ⟨portX, portY, portSide⟩
          simp_all [refinedPort, exitCoordinate, sparsePort]
        rw [hrefined]
        exact portPresent_sparsePort grid port

theorem value_isSome_eq_portPresent
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid) (port : Port) :
    (value stateGrid port).isSome = portPresent grid port := by
  have hallowed := valid.allowed port.x port.y
  unfold RedShades.locallyAllowed at hallowed
  dsimp only at hallowed
  unfold RedShades.allowedFor at hallowed
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hallowed
  have hincidence := hallowed.1.1.1.1.1.1.1
  have hwest : RedShades.optionPresent (stateGrid port.x port.y).west =
      RedShades.hasWest (componentAt grid port.x port.y)
        (quadrantAt port.x port.y) := hincidence.1.1.1
  have heast : RedShades.optionPresent (stateGrid port.x port.y).east =
      RedShades.hasEast (componentAt grid port.x port.y)
        (quadrantAt port.x port.y) := hincidence.1.1.2
  have hsouth : RedShades.optionPresent (stateGrid port.x port.y).south =
      RedShades.hasSouth (componentAt grid port.x port.y)
        (quadrantAt port.x port.y) := hincidence.1.2
  have hnorth : RedShades.optionPresent (stateGrid port.x port.y).north =
      RedShades.hasNorth (componentAt grid port.x port.y)
        (quadrantAt port.x port.y) := hincidence.2
  rcases port with ⟨x, y, side⟩
  cases side
  · simpa only [value, portPresent, RedShades.optionPresent, componentAt] using hwest
  · simpa only [value, portPresent, RedShades.optionPresent, componentAt] using heast
  · simpa only [value, portPresent, RedShades.optionPresent, componentAt] using hsouth
  · simpa only [value, portPresent, RedShades.optionPresent, componentAt] using hnorth

/-- A valid fine shading gives equal values to a coarse port's literal sparse
copy and its side-sensitive macrocell-boundary image. -/
theorem value_refinedPort_eq_sparsePort
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid) (port : Port) :
    value stateGrid (refinedPort port) = value stateGrid (sparsePort port) := by
  by_cases hlive : portPresent grid port = true
  · exact ((livePortPath grid port hlive).sound valid).symm
  · have hsparsePresent :
        portPresent (iterateRefine 2 grid) (sparsePort port) = false := by
      rw [portPresent_sparsePort]
      exact Bool.eq_false_of_not_eq_true hlive
    have hrefinedPresent :
        portPresent (iterateRefine 2 grid) (refinedPort port) = false := by
      rw [portPresent_refinedPort]
      exact Bool.eq_false_of_not_eq_true hlive
    have hsparseSome := value_isSome_eq_portPresent valid (sparsePort port)
    have hrefinedSome := value_isSome_eq_portPresent valid (refinedPort port)
    rw [hsparsePresent] at hsparseSome
    rw [hrefinedPresent] at hrefinedSome
    cases hsparse : value stateGrid (sparsePort port) with
    | none =>
        cases hrefined : value stateGrid (refinedPort port) with
        | none => rfl
        | some shade => simp [hrefined] at hrefinedSome
    | some shade => simp [hsparse] at hsparseSome

/-- Read one coarse shade state from the side-sensitive ports of its refined
macrocell. -/
def projectStateGrid (stateGrid : Nat → Nat → RedShades.State) :
    Nat → Nat → RedShades.State := fun x y =>
  { west := value stateGrid (refinedPort ⟨x, y, .west⟩)
    east := value stateGrid (refinedPort ⟨x, y, .east⟩)
    south := value stateGrid (refinedPort ⟨x, y, .south⟩)
    north := value stateGrid (refinedPort ⟨x, y, .north⟩) }

private theorem state_eq_of_edges {first second : RedShades.State}
    (hwest : first.west = second.west) (heast : first.east = second.east)
    (hsouth : first.south = second.south) (hnorth : first.north = second.north) :
    first = second := by
  rcases first with ⟨firstWest, firstEast, firstSouth, firstNorth⟩
  rcases second with ⟨secondWest, secondEast, secondSouth, secondNorth⟩
  simp_all

theorem projectStateGrid_eq_sparse
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid) (x y : Nat) :
    projectStateGrid stateGrid x y =
      stateGrid (sparseCoordinate x) (sparseCoordinate y) := by
  apply state_eq_of_edges
  · rfl
  · simpa [projectStateGrid, value, refinedPort, sparsePort] using
      value_refinedPort_eq_sparsePort valid ⟨x, y, .east⟩
  · rfl
  · simpa [projectStateGrid, value, refinedPort, sparsePort] using
      value_refinedPort_eq_sparsePort valid ⟨x, y, .north⟩

/-- Every valid twice-refined shade decoration projects to a valid decoration
of the coarse grid. -/
theorem projectStateGrid_valid
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid) :
    ValidShadeGrid grid (projectStateGrid stateGrid) := by
  constructor
  · intro x y
    rw [projectStateGrid_eq_sparse valid]
    have hfine := valid.allowed (sparseCoordinate x) (sparseCoordinate y)
    unfold RedShades.locallyAllowed at hfine ⊢
    dsimp only at hfine ⊢
    change RedShades.allowedFor (componentAt (iterateRefine 2 grid)
      (sparseCoordinate x) (sparseCoordinate y))
        (quadrantAt (sparseCoordinate x) (sparseCoordinate y)) _ = true at hfine
    change RedShades.allowedFor (componentAt grid x y) (quadrantAt x y) _ = true
    rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate] at hfine
    exact hfine
  · intro x y
    simpa [projectStateGrid, value, refinedPort, sparsePort,
      exitCoordinate_succ] using
      valid.hmatch (exitCoordinate x) (sparseCoordinate y)
  · intro x y
    simpa [projectStateGrid, value, refinedPort, sparsePort,
      exitCoordinate_succ] using
      valid.vmatch (sparseCoordinate x) (exitCoordinate y)

end RedShadeGraphProjection
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
