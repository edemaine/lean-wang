/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamShadePaths
import LeanWang.OllingerRobinson104RedShadeGraphSearchSoundness

/-!
# Executable even-path certificates for seam boundaries

These wrappers search from a selected horizontal or vertical boundary to a
perpendicular interior on the queried free line.  Their soundness theorems
turn a successful Boolean result into the exact parity-zero graph path used by
`PairCoverSeamShadePaths`.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathSearch

open RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadePaths PairCoverSeamShadePaths
  ShadedPlaneSignalGrid
  Signals.FreeCellLocal

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def verticalTarget (grid : Nat → Nat → Index)
    (west east row : Nat) (port : Port) : Bool :=
  decide (quarterWest west < port.x) &&
    decide (port.x < quarterEast east) &&
    decide (port.y = row) &&
    decide (port = verticalPort grid port.x row) &&
    (Signals.verticalInterior?
      (componentAt grid port.x row) (quadrantAt port.x row)).isSome

def horizontalTarget (grid : Nat → Nat → Index)
    (south north column : Nat) (port : Port) : Bool :=
  decide (quarterSouth south < port.y) &&
    decide (port.y < quarterNorth north) &&
    decide (port.x = column) &&
    decide (port = horizontalPort grid column port.y) &&
    (Signals.horizontalInterior?
      (componentAt grid column port.y) (quadrantAt column port.y)).isSome

def verticalSearch (grid : Nat → Nat → Index) (width height fuel : Nat)
    (west east column boundary row : Nat) :=
  search grid width height fuel (horizontalPort grid column boundary)
    fun port parity => !parity && verticalTarget grid west east row port

def horizontalSearch (grid : Nat → Nat → Index) (width height fuel : Nat)
    (south north boundary row column : Nat) :=
  search grid width height fuel (verticalPort grid boundary row)
    fun port parity => !parity && horizontalTarget grid south north column port

def verticalPathCheck (grid : Nat → Nat → Index) (width height fuel : Nat)
    (west east column boundary row : Nat) : Bool :=
  match verticalSearch grid width height fuel west east column boundary row with
  | none => false
  | some (finish, parity, _) =>
      !parity && verticalTarget grid west east row finish

def horizontalPathCheck (grid : Nat → Nat → Index) (width height fuel : Nat)
    (south north boundary row column : Nat) : Bool :=
  match horizontalSearch grid width height fuel south north boundary row column with
  | none => false
  | some (finish, parity, _) =>
      !parity && horizontalTarget grid south north column finish

theorem verticalPathCheck_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {west east column boundary row : Nat}
    (checked : verticalPathCheck grid width height fuel
      west east column boundary row = true) :
    ∃ targetX,
      quarterWest west < targetX ∧ targetX < quarterEast east ∧
      Signals.verticalInterior?
        (componentAt grid targetX row) (quadrantAt targetX row) ≠ none ∧
      Path grid (horizontalPort grid column boundary)
        (verticalPort grid targetX row) false := by
  unfold verticalPathCheck at checked
  cases hsearch : verticalSearch grid width height fuel
      west east column boundary row with
  | none => simp [hsearch] at checked
  | some result =>
      rcases result with ⟨finish, parity, moves⟩
      simp only [hsearch, Bool.and_eq_true] at checked
      have target := checked.2
      simp only [verticalTarget, Bool.and_eq_true, decide_eq_true_eq] at target
      have hwest := target.1.1.1.1
      have heast := target.1.1.1.2
      have hrow := target.1.1.2
      have hfinish := target.1.2
      have hinterior := target.2
      have path := search_sound (show
        search grid width height fuel (horizontalPort grid column boundary)
          (fun port parity => !parity && verticalTarget grid west east row port) =
            some (finish, parity, moves) from hsearch)
      have hparity : parity = false := by
        exact Bool.eq_false_of_not_eq_true' checked.1
      have pathFalse : Path grid (horizontalPort grid column boundary)
          finish false := by
        simpa only [hparity] using path
      refine ⟨finish.x, hwest, heast,
        Option.isSome_iff_ne_none.mp hinterior, ?_⟩
      rw [← hfinish]
      exact pathFalse

theorem horizontalPathCheck_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {south north boundary row column : Nat}
    (checked : horizontalPathCheck grid width height fuel
      south north boundary row column = true) :
    ∃ targetY,
      quarterSouth south < targetY ∧ targetY < quarterNorth north ∧
      Signals.horizontalInterior?
        (componentAt grid column targetY) (quadrantAt column targetY) ≠ none ∧
      Path grid (verticalPort grid boundary row)
        (horizontalPort grid column targetY) false := by
  unfold horizontalPathCheck at checked
  cases hsearch : horizontalSearch grid width height fuel
      south north boundary row column with
  | none => simp [hsearch] at checked
  | some result =>
      rcases result with ⟨finish, parity, moves⟩
      simp only [hsearch, Bool.and_eq_true] at checked
      have target := checked.2
      simp only [horizontalTarget, Bool.and_eq_true, decide_eq_true_eq] at target
      have hsouth := target.1.1.1.1
      have hnorth := target.1.1.1.2
      have hcolumn := target.1.1.2
      have hfinish := target.1.2
      have hinterior := target.2
      have path := search_sound (show
        search grid width height fuel (verticalPort grid boundary row)
          (fun port parity => !parity &&
            horizontalTarget grid south north column port) =
              some (finish, parity, moves) from hsearch)
      have hparity : parity = false := by
        exact Bool.eq_false_of_not_eq_true' checked.1
      have pathFalse : Path grid (verticalPort grid boundary row)
          finish false := by
        simpa only [hparity] using path
      refine ⟨finish.y, hsouth, hnorth,
        Option.isSome_iff_ne_none.mp hinterior, ?_⟩
      rw [← hfinish]
      exact pathFalse

theorem false_of_verticalPathCheck_of_freeRow
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {width height fuel west east column boundary row : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeRow : IsFreeRow grid stateGrid west east row)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (checked : verticalPathCheck grid width height fuel
      west east column boundary row = true) : False := by
  rcases verticalPathCheck_sound checked with
    ⟨targetX, hwest, heast, hinterior, path⟩
  exact freeRow_forbids_even_path valid freeRow hwest heast
    selected hinterior path

theorem false_of_horizontalPathCheck_of_freeColumn
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {width height fuel south north boundary row column : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeColumn : IsFreeColumn grid stateGrid south north column)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (checked : horizontalPathCheck grid width height fuel
      south north boundary row column = true) : False := by
  rcases horizontalPathCheck_sound checked with
    ⟨targetY, hsouth, hnorth, hinterior, path⟩
  exact freeColumn_forbids_even_path valid freeColumn hsouth hnorth
    selected hinterior path

end PairCoverSeamPathSearch
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
