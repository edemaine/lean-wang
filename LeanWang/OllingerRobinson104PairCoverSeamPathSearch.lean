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

def StrictBetween (first second value : Nat) : Prop :=
  (first < value ∧ value < second) ∨ (second < value ∧ value < first)

instance (first second value : Nat) :
    Decidable (StrictBetween first second value) := by
  unfold StrictBetween
  infer_instance

def horizontalBetweenTarget (grid : Nat → Nat → Index)
    (column first second : Nat) (port : Port) : Bool :=
  decide (StrictBetween first second port.y) &&
    decide (port.x = column) &&
    decide (port = horizontalPort grid column port.y) &&
    (Signals.horizontalInterior?
      (componentAt grid column port.y) (quadrantAt column port.y)).isSome

def verticalBetweenTarget (grid : Nat → Nat → Index)
    (row first second : Nat) (port : Port) : Bool :=
  decide (StrictBetween first second port.x) &&
    decide (port.y = row) &&
    decide (port = verticalPort grid port.x row) &&
    (Signals.verticalInterior?
      (componentAt grid port.x row) (quadrantAt port.x row)).isSome

def verticalSeamTarget (grid : Nat → Nat → Index)
    (west east column row boundary : Nat) (port : Port) : Bool :=
  verticalTarget grid west east row port ||
    horizontalBetweenTarget grid column row boundary port

def horizontalSeamTarget (grid : Nat → Nat → Index)
    (south north row column boundary : Nat) (port : Port) : Bool :=
  horizontalTarget grid south north column port ||
    verticalBetweenTarget grid row column boundary port

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

def verticalFlood (grid : Nat → Nat → Index) (width height fuel : Nat)
    (column boundary : Nat) : List Node :=
  exploreFast grid width height fuel [horizontalPort grid column boundary]

def horizontalFlood (grid : Nat → Nat → Index) (width height fuel : Nat)
    (boundary row : Nat) : List Node :=
  exploreFast grid width height fuel [verticalPort grid boundary row]

def verticalFloodCheck (grid : Nat → Nat → Index) (width height fuel : Nat)
    (west east column boundary row : Nat) : Bool :=
  (verticalFlood grid width height fuel column boundary).any fun node =>
    !node.parity && verticalTarget grid west east row node.current

def horizontalFloodCheck (grid : Nat → Nat → Index) (width height fuel : Nat)
    (south north boundary row column : Nat) : Bool :=
  (horizontalFlood grid width height fuel boundary row).any fun node =>
    !node.parity && horizontalTarget grid south north column node.current

def verticalSeamFloodCheck (grid : Nat → Nat → Index)
    (width height fuel west east column row boundary : Nat) : Bool :=
  (verticalFlood grid width height fuel column boundary).any fun node =>
    !node.parity &&
      verticalSeamTarget grid west east column row boundary node.current

def horizontalSeamFloodCheck (grid : Nat → Nat → Index)
    (width height fuel south north row column boundary : Nat) : Bool :=
  (horizontalFlood grid width height fuel boundary row).any fun node =>
    !node.parity &&
      horizontalSeamTarget grid south north row column boundary node.current

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

theorem verticalFloodCheck_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {west east column boundary row : Nat}
    (checked : verticalFloodCheck grid width height fuel
      west east column boundary row = true) :
    ∃ targetX,
      quarterWest west < targetX ∧ targetX < quarterEast east ∧
      Signals.verticalInterior?
        (componentAt grid targetX row) (quadrantAt targetX row) ≠ none ∧
      Path grid (horizontalPort grid column boundary)
        (verticalPort grid targetX row) false := by
  simp only [verticalFloodCheck, List.any_eq_true] at checked
  rcases checked with ⟨node, hnode, hchecked⟩
  simp only [Bool.and_eq_true] at hchecked
  have target := hchecked.2
  simp only [verticalTarget, Bool.and_eq_true, decide_eq_true_eq] at target
  have hwest := target.1.1.1.1
  have heast := target.1.1.1.2
  have hrow := target.1.1.2
  have hfinish := target.1.2
  have hinterior := target.2
  have sound := exploreFast_sound (show node ∈
      exploreFast grid width height fuel
        [horizontalPort grid column boundary] from hnode)
  have horigin : node.origin = horizontalPort grid column boundary := by
    simpa using sound.1
  have hparity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hchecked.1
  have path : Path grid (horizontalPort grid column boundary)
      node.current false := by
    simpa only [horigin, hparity] using sound.2
  refine ⟨node.current.x, hwest, heast,
    Option.isSome_iff_ne_none.mp hinterior, ?_⟩
  rw [← hfinish]
  exact path

theorem horizontalFloodCheck_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {south north boundary row column : Nat}
    (checked : horizontalFloodCheck grid width height fuel
      south north boundary row column = true) :
    ∃ targetY,
      quarterSouth south < targetY ∧ targetY < quarterNorth north ∧
      Signals.horizontalInterior?
        (componentAt grid column targetY) (quadrantAt column targetY) ≠ none ∧
      Path grid (verticalPort grid boundary row)
        (horizontalPort grid column targetY) false := by
  simp only [horizontalFloodCheck, List.any_eq_true] at checked
  rcases checked with ⟨node, hnode, hchecked⟩
  simp only [Bool.and_eq_true] at hchecked
  have target := hchecked.2
  simp only [horizontalTarget, Bool.and_eq_true, decide_eq_true_eq] at target
  have hsouth := target.1.1.1.1
  have hnorth := target.1.1.1.2
  have hcolumn := target.1.1.2
  have hfinish := target.1.2
  have hinterior := target.2
  have sound := exploreFast_sound (show node ∈
      exploreFast grid width height fuel
        [verticalPort grid boundary row] from hnode)
  have horigin : node.origin = verticalPort grid boundary row := by
    simpa using sound.1
  have hparity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hchecked.1
  have path : Path grid (verticalPort grid boundary row)
      node.current false := by
    simpa only [horigin, hparity] using sound.2
  refine ⟨node.current.y, hsouth, hnorth,
    Option.isSome_iff_ne_none.mp hinterior, ?_⟩
  rw [← hfinish]
  exact path

def VerticalSeamPath (grid : Nat → Nat → Index)
    (west east column row boundary : Nat) : Prop :=
  (∃ targetX,
    quarterWest west < targetX ∧ targetX < quarterEast east ∧
    Signals.verticalInterior?
      (componentAt grid targetX row) (quadrantAt targetX row) ≠ none ∧
    Path grid (horizontalPort grid column boundary)
      (verticalPort grid targetX row) false) ∨
  (∃ targetY, StrictBetween row boundary targetY ∧
    Signals.horizontalInterior?
      (componentAt grid column targetY) (quadrantAt column targetY) ≠ none ∧
    Path grid (horizontalPort grid column boundary)
      (horizontalPort grid column targetY) false)

def HorizontalSeamPath (grid : Nat → Nat → Index)
    (south north row column boundary : Nat) : Prop :=
  (∃ targetY,
    quarterSouth south < targetY ∧ targetY < quarterNorth north ∧
    Signals.horizontalInterior?
      (componentAt grid column targetY) (quadrantAt column targetY) ≠ none ∧
    Path grid (verticalPort grid boundary row)
      (horizontalPort grid column targetY) false) ∨
  (∃ targetX, StrictBetween column boundary targetX ∧
    Signals.verticalInterior?
      (componentAt grid targetX row) (quadrantAt targetX row) ≠ none ∧
    Path grid (verticalPort grid boundary row)
      (verticalPort grid targetX row) false)

theorem verticalSeamFloodCheck_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {west east column row boundary : Nat}
    (checked : verticalSeamFloodCheck grid width height fuel
      west east column row boundary = true) :
    VerticalSeamPath grid west east column row boundary := by
  simp only [verticalSeamFloodCheck, List.any_eq_true] at checked
  rcases checked with ⟨node, hnode, hchecked⟩
  simp only [Bool.and_eq_true] at hchecked
  have sound := exploreFast_sound (show node ∈
      exploreFast grid width height fuel
        [horizontalPort grid column boundary] from hnode)
  have horigin : node.origin = horizontalPort grid column boundary := by
    simpa using sound.1
  have hparity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hchecked.1
  have path : Path grid (horizontalPort grid column boundary)
      node.current false := by
    simpa only [horigin, hparity] using sound.2
  simp only [verticalSeamTarget, Bool.or_eq_true] at hchecked
  rcases hchecked.2 with hvertical | hbetween
  · simp only [verticalTarget, Bool.and_eq_true, decide_eq_true_eq] at hvertical
    have hwest := hvertical.1.1.1.1
    have heast := hvertical.1.1.1.2
    have hrow := hvertical.1.1.2
    have hfinish := hvertical.1.2
    have hinterior := hvertical.2
    left
    refine ⟨node.current.x, hwest, heast,
      Option.isSome_iff_ne_none.mp hinterior, ?_⟩
    rw [← hfinish]
    exact path
  · simp only [horizontalBetweenTarget, Bool.and_eq_true,
      decide_eq_true_eq] at hbetween
    have hstrict := hbetween.1.1.1
    have hcolumn := hbetween.1.1.2
    have hfinish := hbetween.1.2
    have hinterior := hbetween.2
    right
    refine ⟨node.current.y, hstrict,
      Option.isSome_iff_ne_none.mp hinterior, ?_⟩
    rw [← hfinish]
    exact path

theorem horizontalSeamFloodCheck_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {south north row column boundary : Nat}
    (checked : horizontalSeamFloodCheck grid width height fuel
      south north row column boundary = true) :
    HorizontalSeamPath grid south north row column boundary := by
  simp only [horizontalSeamFloodCheck, List.any_eq_true] at checked
  rcases checked with ⟨node, hnode, hchecked⟩
  simp only [Bool.and_eq_true] at hchecked
  have sound := exploreFast_sound (show node ∈
      exploreFast grid width height fuel
        [verticalPort grid boundary row] from hnode)
  have horigin : node.origin = verticalPort grid boundary row := by
    simpa using sound.1
  have hparity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hchecked.1
  have path : Path grid (verticalPort grid boundary row)
      node.current false := by
    simpa only [horigin, hparity] using sound.2
  simp only [horizontalSeamTarget, Bool.or_eq_true] at hchecked
  rcases hchecked.2 with hhorizontal | hbetween
  · simp only [horizontalTarget, Bool.and_eq_true,
      decide_eq_true_eq] at hhorizontal
    have hsouth := hhorizontal.1.1.1.1
    have hnorth := hhorizontal.1.1.1.2
    have hcolumn := hhorizontal.1.1.2
    have hfinish := hhorizontal.1.2
    have hinterior := hhorizontal.2
    left
    refine ⟨node.current.y, hsouth, hnorth,
      Option.isSome_iff_ne_none.mp hinterior, ?_⟩
    rw [← hfinish]
    exact path
  · simp only [verticalBetweenTarget, Bool.and_eq_true,
      decide_eq_true_eq] at hbetween
    have hstrict := hbetween.1.1.1
    have hrow := hbetween.1.1.2
    have hfinish := hbetween.1.2
    have hinterior := hbetween.2
    right
    refine ⟨node.current.x, hstrict,
      Option.isSome_iff_ne_none.mp hinterior, ?_⟩
    rw [← hfinish]
    exact path

theorem false_of_verticalSeamPath
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east column row boundary : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeRow : IsFreeRow grid stateGrid west east row)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (noneBetween : ∀ y, StrictBetween row boundary y →
      ShadedSignals.selectedHorizontalFor
        (componentAt grid column y) (quadrantAt column y)
        (stateGrid column y) = none)
    (paths : VerticalSeamPath grid west east column row boundary) : False := by
  rcases paths with perpendicular | between
  · rcases perpendicular with ⟨targetX, hwest, heast, hinterior, path⟩
    exact freeRow_forbids_even_path valid freeRow hwest heast
      selected hinterior path
  · rcases between with ⟨targetY, hbetween, hinterior, path⟩
    have sourceLight := horizontalPort_value_eq_light valid selected
    have related := path.sound valid
    have relatedEq : value stateGrid (horizontalPort grid column boundary) =
        value stateGrid (horizontalPort grid column targetY) := related
    have targetLight : value stateGrid (horizontalPort grid column targetY) =
        some .light := relatedEq.symm.trans sourceLight
    have targetSelected := selectedHorizontal_of_port_light
      valid hinterior targetLight
    exact targetSelected (noneBetween targetY hbetween)

theorem false_of_horizontalSeamPath
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {south north row column boundary : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeColumn : IsFreeColumn grid stateGrid south north column)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (noneBetween : ∀ x, StrictBetween column boundary x →
      ShadedSignals.selectedVerticalFor
        (componentAt grid x row) (quadrantAt x row)
        (stateGrid x row) = none)
    (paths : HorizontalSeamPath grid south north row column boundary) : False := by
  rcases paths with perpendicular | between
  · rcases perpendicular with ⟨targetY, hsouth, hnorth, hinterior, path⟩
    exact freeColumn_forbids_even_path valid freeColumn hsouth hnorth
      selected hinterior path
  · rcases between with ⟨targetX, hbetween, hinterior, path⟩
    have sourceLight := verticalPort_value_eq_light valid selected
    have related := path.sound valid
    have relatedEq : value stateGrid (verticalPort grid boundary row) =
        value stateGrid (verticalPort grid targetX row) := related
    have targetLight : value stateGrid (verticalPort grid targetX row) =
        some .light := relatedEq.symm.trans sourceLight
    have targetSelected := selectedVertical_of_port_light
      valid hinterior targetLight
    exact targetSelected (noneBetween targetX hbetween)

theorem false_of_verticalSeamFloodCheck
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {width height fuel west east column row boundary : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeRow : IsFreeRow grid stateGrid west east row)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (noneBetween : ∀ y, StrictBetween row boundary y →
      ShadedSignals.selectedHorizontalFor
        (componentAt grid column y) (quadrantAt column y)
        (stateGrid column y) = none)
    (checked : verticalSeamFloodCheck grid width height fuel
      west east column row boundary = true) : False :=
  false_of_verticalSeamPath valid freeRow selected noneBetween
    (verticalSeamFloodCheck_sound checked)

theorem false_of_horizontalSeamFloodCheck
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {width height fuel south north row column boundary : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeColumn : IsFreeColumn grid stateGrid south north column)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (noneBetween : ∀ x, StrictBetween column boundary x →
      ShadedSignals.selectedVerticalFor
        (componentAt grid x row) (quadrantAt x row)
        (stateGrid x row) = none)
    (checked : horizontalSeamFloodCheck grid width height fuel
      south north row column boundary = true) : False :=
  false_of_horizontalSeamPath valid freeColumn selected noneBetween
    (horizontalSeamFloodCheck_sound checked)

end PairCoverSeamPathSearch
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
