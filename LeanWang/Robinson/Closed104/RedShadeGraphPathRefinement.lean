/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphRefinement
import LeanWang.Robinson.Closed104.RedShadeGraphBoards

/-!
Lift parity-labelled red paths through two substitutions.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphRefinement

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem portPresent_west_of_hasWest {grid : Nat → Nat → Index} {x y : Nat}
    (h : RedShades.hasWest (componentAt grid x y) (quadrantAt x y) = true) :
    portPresent grid ⟨x, y, .west⟩ = true := by
  simpa [portPresent] using h

theorem portPresent_east_of_hasEast {grid : Nat → Nat → Index} {x y : Nat}
    (h : RedShades.hasEast (componentAt grid x y) (quadrantAt x y) = true) :
    portPresent grid ⟨x, y, .east⟩ = true := by
  simpa [portPresent] using h

theorem portPresent_south_of_hasSouth {grid : Nat → Nat → Index} {x y : Nat}
    (h : RedShades.hasSouth (componentAt grid x y) (quadrantAt x y) = true) :
    portPresent grid ⟨x, y, .south⟩ = true := by
  simpa [portPresent] using h

theorem portPresent_north_of_hasNorth {grid : Nat → Nat → Index} {x y : Nat}
    (h : RedShades.hasNorth (componentAt grid x y) (quadrantAt x y) = true) :
    portPresent grid ⟨x, y, .north⟩ = true := by
  simpa [portPresent] using h

theorem path_of_sparseLink
    {grid : Nat → Nat → Index} {first second : Port} {parity : Bool}
    (hfirst : portPresent grid first = true)
    (hsecond : portPresent grid second = true)
    (core : Link (iterateRefine 2 grid)
      (sparsePort first) (sparsePort second) parity) :
    Path (iterateRefine 2 grid) (refinedPort first) (refinedPort second) parity := by
  have firstPath := path_symm (livePortPath grid first hfirst)
  have secondPath := livePortPath grid second hsecond
  simpa using Path.trans firstPath (Path.trans (Path.ofLink core) secondPath)

theorem horizontalMatch_refine (grid : Nat → Nat → Index) (x y : Nat) :
    Path (iterateRefine 2 grid)
      (refinedPort ⟨x, y, .east⟩) (refinedPort ⟨x + 1, y, .west⟩) false := by
  have link := Link.horizontalMatch (indexGrid := iterateRefine 2 grid)
    (exitCoordinate x) (sparseCoordinate y)
  simpa [refinedPort, sparsePort, exitCoordinate_succ] using Path.ofLink link

theorem verticalMatch_refine (grid : Nat → Nat → Index) (x y : Nat) :
    Path (iterateRefine 2 grid)
      (refinedPort ⟨x, y, .north⟩) (refinedPort ⟨x, y + 1, .south⟩) false := by
  have link := Link.verticalMatch (indexGrid := iterateRefine 2 grid)
    (sparseCoordinate x) (exitCoordinate y)
  simpa [refinedPort, sparsePort, exitCoordinate_succ] using Path.ofLink link

theorem hasHorizontal_sparse {grid : Nat → Nat → Index} {x y : Nat}
    (h : RedShades.hasHorizontal
      (componentAt grid x y) (quadrantAt x y) = true) :
    RedShades.hasHorizontal
      (componentAt (iterateRefine 2 grid) (sparseCoordinate x) (sparseCoordinate y))
      (quadrantAt (sparseCoordinate x) (sparseCoordinate y)) = true := by
  rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]
  exact h

theorem hasVertical_sparse {grid : Nat → Nat → Index} {x y : Nat}
    (h : RedShades.hasVertical
      (componentAt grid x y) (quadrantAt x y) = true) :
    RedShades.hasVertical
      (componentAt (iterateRefine 2 grid) (sparseCoordinate x) (sparseCoordinate y))
      (quadrantAt (sparseCoordinate x) (sparseCoordinate y)) = true := by
  rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]
  exact h

theorem cornerWest_sparse {grid : Nat → Nat → Index} {x y : Nat}
    (h : RedShades.cornerWest
      (componentAt grid x y) (quadrantAt x y) = true) :
    RedShades.cornerWest
      (componentAt (iterateRefine 2 grid) (sparseCoordinate x) (sparseCoordinate y))
      (quadrantAt (sparseCoordinate x) (sparseCoordinate y)) = true := by
  rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]
  exact h

theorem cornerEast_sparse {grid : Nat → Nat → Index} {x y : Nat}
    (h : RedShades.cornerEast
      (componentAt grid x y) (quadrantAt x y) = true) :
    RedShades.cornerEast
      (componentAt (iterateRefine 2 grid) (sparseCoordinate x) (sparseCoordinate y))
      (quadrantAt (sparseCoordinate x) (sparseCoordinate y)) = true := by
  rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]
  exact h

theorem cornerSouth_sparse {grid : Nat → Nat → Index} {x y : Nat}
    (h : RedShades.cornerSouth
      (componentAt grid x y) (quadrantAt x y) = true) :
    RedShades.cornerSouth
      (componentAt (iterateRefine 2 grid) (sparseCoordinate x) (sparseCoordinate y))
      (quadrantAt (sparseCoordinate x) (sparseCoordinate y)) = true := by
  rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]
  exact h

theorem cornerNorth_sparse {grid : Nat → Nat → Index} {x y : Nat}
    (h : RedShades.cornerNorth
      (componentAt grid x y) (quadrantAt x y) = true) :
    RedShades.cornerNorth
      (componentAt (iterateRefine 2 grid) (sparseCoordinate x) (sparseCoordinate y))
      (quadrantAt (sparseCoordinate x) (sparseCoordinate y)) = true := by
  rw [componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]
  exact h

/-- Every coarse link lifts to a same-parity path after two substitutions. -/
theorem link_refine {grid : Nat → Nat → Index} {first second : Port}
    {parity : Bool} (link : Link grid first second parity) :
    Path (iterateRefine 2 grid) (refinedPort first) (refinedPort second) parity := by
  induction link with
  | horizontalMatch x y => exact horizontalMatch_refine grid x y
  | verticalMatch x y => exact verticalMatch_refine grid x y
  | horizontal x y hpath =>
      have hwest : RedShades.hasWest
          (componentAt grid x y) (quadrantAt x y) = true := by
        simp [RedShades.hasWest, hpath]
      have heast : RedShades.hasEast
          (componentAt grid x y) (quadrantAt x y) = true := by
        simp [RedShades.hasEast, hpath]
      apply path_of_sparseLink
        (portPresent_west_of_hasWest hwest) (portPresent_east_of_hasEast heast)
      simpa [sparsePort] using
        Link.horizontal (sparseCoordinate x) (sparseCoordinate y)
          (hasHorizontal_sparse hpath)
  | vertical x y hpath =>
      have hsouth : RedShades.hasSouth
          (componentAt grid x y) (quadrantAt x y) = true := by
        simp [RedShades.hasSouth, hpath]
      have hnorth : RedShades.hasNorth
          (componentAt grid x y) (quadrantAt x y) = true := by
        simp [RedShades.hasNorth, hpath]
      apply path_of_sparseLink
        (portPresent_south_of_hasSouth hsouth) (portPresent_north_of_hasNorth hnorth)
      simpa [sparsePort] using
        Link.vertical (sparseCoordinate x) (sparseCoordinate y)
          (hasVertical_sparse hpath)
  | westNorth x y hwest hnorth =>
      apply path_of_sparseLink
        (portPresent_west_of_hasWest (by simp [RedShades.hasWest, hwest]))
        (portPresent_north_of_hasNorth (by simp [RedShades.hasNorth, hnorth]))
      simpa [sparsePort] using Link.westNorth
        (sparseCoordinate x) (sparseCoordinate y)
        (cornerWest_sparse hwest) (cornerNorth_sparse hnorth)
  | westSouth x y hwest hsouth =>
      apply path_of_sparseLink
        (portPresent_west_of_hasWest (by simp [RedShades.hasWest, hwest]))
        (portPresent_south_of_hasSouth (by simp [RedShades.hasSouth, hsouth]))
      simpa [sparsePort] using Link.westSouth
        (sparseCoordinate x) (sparseCoordinate y)
        (cornerWest_sparse hwest) (cornerSouth_sparse hsouth)
  | eastNorth x y heast hnorth =>
      apply path_of_sparseLink
        (portPresent_east_of_hasEast (by simp [RedShades.hasEast, heast]))
        (portPresent_north_of_hasNorth (by simp [RedShades.hasNorth, hnorth]))
      simpa [sparsePort] using Link.eastNorth
        (sparseCoordinate x) (sparseCoordinate y)
        (cornerEast_sparse heast) (cornerNorth_sparse hnorth)
  | eastSouth x y heast hsouth =>
      apply path_of_sparseLink
        (portPresent_east_of_hasEast (by simp [RedShades.hasEast, heast]))
        (portPresent_south_of_hasSouth (by simp [RedShades.hasSouth, hsouth]))
      simpa [sparsePort] using Link.eastSouth
        (sparseCoordinate x) (sparseCoordinate y)
        (cornerEast_sparse heast) (cornerSouth_sparse hsouth)
  | crossing x y hhorizontal hvertical =>
      apply path_of_sparseLink
        (portPresent_west_of_hasWest (by simp [RedShades.hasWest, hhorizontal]))
        (portPresent_south_of_hasSouth (by simp [RedShades.hasSouth, hvertical]))
      simpa [sparsePort] using Link.crossing
        (sparseCoordinate x) (sparseCoordinate y)
        (hasHorizontal_sparse hhorizontal) (hasVertical_sparse hvertical)
  | symm link ih => exact path_symm ih

/-- Every parity-labelled path lifts through two substitutions. -/
theorem path_refine {grid : Nat → Nat → Index} {first second : Port}
    {parity : Bool} (path : Path grid first second parity) :
    Path (iterateRefine 2 grid) (refinedPort first) (refinedPort second) parity := by
  induction path with
  | refl port => exact Path.refl _
  | ofLink link => exact link_refine link
  | trans firstPath secondPath firstIH secondIH =>
      exact Path.trans firstIH secondIH

@[simp] theorem sparseCoordinate_quarterWest (west : Nat) :
    sparseCoordinate (quarterWest west) = quarterWest (4 * west) := by
  simp [sparseCoordinate, macroOrigin, localCoordinate, quarterWest]
  omega

@[simp] theorem sparseCoordinate_quarterEast (east : Nat) :
    sparseCoordinate (quarterEast east) = quarterEast (4 * east) := by
  simp [sparseCoordinate, macroOrigin, localCoordinate, quarterEast]
  omega

@[simp] theorem sparseCoordinate_quarterSouth (south : Nat) :
    sparseCoordinate (quarterSouth south) = quarterSouth (4 * south) := by
  simp [sparseCoordinate, macroOrigin, localCoordinate, quarterSouth]
  omega

@[simp] theorem sparseCoordinate_quarterNorth (north : Nat) :
    sparseCoordinate (quarterNorth north) = quarterNorth (4 * north) := by
  simp [sparseCoordinate, macroOrigin, localCoordinate, quarterNorth]
  omega

end RedShadeGraphRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
