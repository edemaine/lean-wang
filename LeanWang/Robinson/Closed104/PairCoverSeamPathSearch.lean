/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPorts
import LeanWang.Robinson.Closed104.RedShadeCycles
import LeanWang.Robinson.Closed104.RedShadeGraphSearchSoundness
import LeanWang.Robinson.Closed104.RedShadeGraphWeightedSearch

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

open RedShadeCycles RedShadeGraph RedShadeGraphSearch RedShadeGraphWeightedSearch
  RedShadeGraphSearchSoundness RedShadePaths PairCoverSeamShadePaths
  Signals.FreeCellLocal

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def searchWeightedReachAux (grid : Nat → Nat → Index)
    (width height : Nat) (accept : ReachNode → Bool) :
    Nat → List ReachNode → Array Bool → Option ReachNode
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, node :: stack, visited =>
      if accept node then some node
      else
        let marked := markFreshReachList width visited
          (nextReachNodes grid width height node)
        searchWeightedReachAux grid width height accept fuel
          (stack ++ marked.1) marked.2

def searchFastWeightedReach (grid : Nat → Nat → Index)
    (width height fuel : Nat) (starts : List WeightedStart)
    (accept : ReachNode → Bool) : Option ReachNode :=
  let nodes := starts.map initialReachNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshReachList width emptyVisited nodes
  searchWeightedReachAux grid width height accept fuel marked.1 marked.2

theorem searchWeightedReachAux_sound
    {grid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {accept : ReachNode → Bool} :
    ∀ (fuel : Nat) (stack : List ReachNode) (visited : Array Bool)
      (result : ReachNode),
      (∀ node ∈ stack, SoundReachFromWeighted grid starts node) →
      searchWeightedReachAux grid width height accept fuel stack visited =
        some result →
      SoundReachFromWeighted grid starts result := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack visited result _ hresult
      simp [searchWeightedReachAux] at hresult
  | succ fuel ih =>
      intro stack visited result hstack hresult
      cases stack with
      | nil => simp [searchWeightedReachAux] at hresult
      | cons first rest =>
          rw [searchWeightedReachAux] at hresult
          split at hresult
          · simp only [Option.some.injEq] at hresult
            subst result
            exact hstack first (by simp)
          · let marked := markFreshReachList width visited
              (nextReachNodes grid width height first)
            apply ih (rest ++ marked.1) marked.2 result
            · intro node hnode
              rcases List.mem_append.1 hnode with hnode | hnode
              · exact hstack node (by simp [hnode])
              · exact markFreshReachList_sound
                  (nodes := nextReachNodes grid width height first)
                  (visited := visited)
                  (fun next hnext => nextReachNodes_sound
                    (hstack first (by simp)) hnext)
                  node hnode
            · exact hresult

theorem searchFastWeightedReach_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {starts : List WeightedStart} {accept : ReachNode → Bool}
    {result : ReachNode}
    (hresult : searchFastWeightedReach grid width height fuel starts accept =
      some result) :
    SoundReachFromWeighted grid starts result := by
  unfold searchFastWeightedReach at hresult
  let nodes := starts.map initialReachNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshReachList width emptyVisited nodes
  apply searchWeightedReachAux_sound fuel marked.1 marked.2 result
  · exact markFreshReachList_sound
      (nodes := nodes) (visited := emptyVisited) (by
        intro initial hinitial
        rcases List.mem_map.1 hinitial with ⟨start, hstart, rfl⟩
        exact initialReachNode_sound hstart)
  · exact hresult

def exploreWeightedReachCoverAux {Query : Type}
    (grid : Nat → Nat → Index) (width height : Nat)
    (covers : ReachNode → Query → Bool) :
    Nat → List ReachNode → Array Bool → List Query →
      List ReachNode → List ReachNode
  | 0, _, _, _, found => found
  | _ + 1, [], _, _, found => found
  | fuel + 1, node :: stack, visited, remaining, found =>
      let found' := node :: found
      let remaining' := remaining.filter fun query => !covers node query
      if remaining'.isEmpty then found'
      else
        let marked := markFreshReachList width visited
          (nextReachNodes grid width height node)
        exploreWeightedReachCoverAux grid width height covers fuel
          (stack ++ marked.1) marked.2 remaining' found'

def exploreFastWeightedReachCover {Query : Type}
    (grid : Nat → Nat → Index) (width height fuel : Nat)
    (starts : List WeightedStart) (queries : List Query)
    (covers : ReachNode → Query → Bool) : List ReachNode :=
  let nodes := starts.map initialReachNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshReachList width emptyVisited nodes
  exploreWeightedReachCoverAux grid width height covers fuel
    marked.1 marked.2 queries []

theorem exploreWeightedReachCoverAux_sound
    {Query : Type}
    {grid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {covers : ReachNode → Query → Bool} :
    ∀ (fuel : Nat) (stack : List ReachNode) (visited : Array Bool)
      (remaining : List Query) (found : List ReachNode),
      (∀ node ∈ stack, SoundReachFromWeighted grid starts node) →
      (∀ node ∈ found, SoundReachFromWeighted grid starts node) →
      ∀ node ∈ exploreWeightedReachCoverAux grid width height covers
        fuel stack visited remaining found,
        SoundReachFromWeighted grid starts node := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack visited remaining found _ hfound node hnode
      exact hfound node (by
        simpa [exploreWeightedReachCoverAux] using hnode)
  | succ fuel ih =>
      intro stack visited remaining found hstack hfound node hnode
      cases stack with
      | nil => exact hfound node (by
          simpa [exploreWeightedReachCoverAux] using hnode)
      | cons first rest =>
          rw [exploreWeightedReachCoverAux] at hnode
          split at hnode
          · simp only [List.mem_cons] at hnode
            rcases hnode with rfl | hnode
            · exact hstack _ (by simp)
            · exact hfound node hnode
          · let marked := markFreshReachList width visited
              (nextReachNodes grid width height first)
            apply ih (rest ++ marked.1) marked.2
              (remaining.filter fun query => !covers first query)
              (first :: found)
            · intro candidate hcandidate
              rcases List.mem_append.1 hcandidate with hcandidate | hcandidate
              · exact hstack candidate (by simp [hcandidate])
              · exact markFreshReachList_sound
                  (nodes := nextReachNodes grid width height first)
                  (visited := visited)
                  (fun next hnext => nextReachNodes_sound
                    (hstack first (by simp)) hnext)
                  candidate hcandidate
            · intro candidate hcandidate
              simp only [List.mem_cons] at hcandidate
              rcases hcandidate with rfl | hcandidate
              · exact hstack _ (by simp)
              · exact hfound candidate hcandidate
            · exact hnode

theorem exploreFastWeightedReachCover_sound
    {Query : Type}
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {starts : List WeightedStart} {queries : List Query}
    {covers : ReachNode → Query → Bool}
    {node : ReachNode}
    (hnode : node ∈ exploreFastWeightedReachCover grid width height fuel
      starts queries covers) :
    SoundReachFromWeighted grid starts node := by
  unfold exploreFastWeightedReachCover at hnode
  let nodes := starts.map initialReachNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshReachList width emptyVisited nodes
  apply exploreWeightedReachCoverAux_sound fuel marked.1 marked.2 queries []
  · exact markFreshReachList_sound
      (nodes := nodes) (visited := emptyVisited) (by
        intro initial hinitial
        rcases List.mem_map.1 hinitial with ⟨start, hstart, rfl⟩
        exact initialReachNode_sound hstart)
  · simp
  · exact hnode

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

def verticalSeamSearch (grid : Nat → Nat → Index) (width height fuel : Nat)
    (west east column row boundary : Nat) :=
  search grid width height fuel (horizontalPort grid column boundary)
    fun port parity => !parity &&
      verticalSeamTarget grid west east column row boundary port

def horizontalSeamSearch (grid : Nat → Nat → Index) (width height fuel : Nat)
    (south north row column boundary : Nat) :=
  search grid width height fuel (verticalPort grid boundary row)
    fun port parity => !parity &&
      horizontalSeamTarget grid south north row column boundary port

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

def verticalSeamPathCheck (grid : Nat → Nat → Index)
    (width height fuel west east column row boundary : Nat) : Bool :=
  match verticalSeamSearch grid width height fuel
      west east column row boundary with
  | none => false
  | some (finish, parity, _) =>
      !parity && verticalSeamTarget grid west east column row boundary finish

def horizontalSeamPathCheck (grid : Nat → Nat → Index)
    (width height fuel south north row column boundary : Nat) : Bool :=
  match horizontalSeamSearch grid width height fuel
      south north row column boundary with
  | none => false
  | some (finish, parity, _) =>
      !parity && horizontalSeamTarget grid south north row column boundary finish

def verticalFlood (grid : Nat → Nat → Index) (width height fuel : Nat)
    (column boundary : Nat) : List Node :=
  exploreFast grid width height fuel [horizontalPort grid column boundary]

def horizontalFlood (grid : Nat → Nat → Index) (width height fuel : Nat)
    (boundary row : Nat) : List Node :=
  exploreFast grid width height fuel [verticalPort grid boundary row]

def verticalReachFlood (grid : Nat → Nat → Index)
    (width height fuel column boundary : Nat) : List ReachNode :=
  exploreFastWeightedReach grid width height fuel
    [⟨horizontalPort grid column boundary, false⟩]

def horizontalReachFlood (grid : Nat → Nat → Index)
    (width height fuel boundary row : Nat) : List ReachNode :=
  exploreFastWeightedReach grid width height fuel
    [⟨verticalPort grid boundary row, false⟩]

def verticalReachSearch (grid : Nat → Nat → Index)
    (width height fuel west east column row boundary : Nat) :
    Option ReachNode :=
  searchFastWeightedReach grid width height fuel
    [⟨horizontalPort grid column boundary, false⟩] fun node =>
      !node.parity &&
        verticalSeamTarget grid west east column row boundary node.current

def horizontalReachSearch (grid : Nat → Nat → Index)
    (width height fuel south north row column boundary : Nat) :
    Option ReachNode :=
  searchFastWeightedReach grid width height fuel
    [⟨verticalPort grid boundary row, false⟩] fun node =>
      !node.parity &&
        horizontalSeamTarget grid south north row column boundary node.current

def verticalReachPathCheck (grid : Nat → Nat → Index)
    (width height fuel west east column row boundary : Nat) : Bool :=
  match verticalReachSearch grid width height fuel
      west east column row boundary with
  | none => false
  | some node => !node.parity &&
      verticalSeamTarget grid west east column row boundary node.current

def horizontalReachPathCheck (grid : Nat → Nat → Index)
    (width height fuel south north row column boundary : Nat) : Bool :=
  match horizontalReachSearch grid width height fuel
      south north row column boundary with
  | none => false
  | some node => !node.parity &&
      horizontalSeamTarget grid south north row column boundary node.current

def verticalReachSeamCheck (grid : Nat → Nat → Index)
    (west east column row boundary : Nat) (found : List ReachNode) : Bool :=
  found.any fun node => !node.parity &&
    verticalSeamTarget grid west east column row boundary node.current

def horizontalReachSeamCheck (grid : Nat → Nat → Index)
    (south north row column boundary : Nat) (found : List ReachNode) : Bool :=
  found.any fun node => !node.parity &&
    horizontalSeamTarget grid south north row column boundary node.current

def verticalReachCover (grid : Nat → Nat → Index)
    (width height fuel west east column boundary : Nat)
    (rows : List Nat) : List ReachNode :=
  exploreFastWeightedReachCover grid width height fuel
    [⟨horizontalPort grid column boundary, false⟩] rows fun node row =>
      !node.parity &&
        verticalSeamTarget grid west east column row boundary node.current

def horizontalReachCover (grid : Nat → Nat → Index)
    (width height fuel south north row boundary : Nat)
    (columns : List Nat) : List ReachNode :=
  exploreFastWeightedReachCover grid width height fuel
    [⟨verticalPort grid boundary row, false⟩] columns fun node column =>
      !node.parity &&
        horizontalSeamTarget grid south north row column boundary node.current

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

private theorem verticalSeamPath_of_target
    {grid : Nat → Nat → Index} {west east column row boundary : Nat}
    {finish : Port}
    (path : Path grid (horizontalPort grid column boundary) finish false)
    (target : verticalSeamTarget grid west east
      column row boundary finish = true) :
    VerticalSeamPath grid west east column row boundary := by
  simp only [verticalSeamTarget, Bool.or_eq_true] at target
  rcases target with hvertical | hbetween
  · simp only [verticalTarget, Bool.and_eq_true, decide_eq_true_eq] at hvertical
    left
    refine ⟨finish.x, hvertical.1.1.1.1, hvertical.1.1.1.2,
      Option.isSome_iff_ne_none.mp hvertical.2, ?_⟩
    rw [← hvertical.1.2]
    exact path
  · simp only [horizontalBetweenTarget, Bool.and_eq_true,
      decide_eq_true_eq] at hbetween
    right
    refine ⟨finish.y, hbetween.1.1.1,
      Option.isSome_iff_ne_none.mp hbetween.2, ?_⟩
    rw [← hbetween.1.2]
    exact path

private theorem horizontalSeamPath_of_target
    {grid : Nat → Nat → Index} {south north row column boundary : Nat}
    {finish : Port}
    (path : Path grid (verticalPort grid boundary row) finish false)
    (target : horizontalSeamTarget grid south north
      row column boundary finish = true) :
    HorizontalSeamPath grid south north row column boundary := by
  simp only [horizontalSeamTarget, Bool.or_eq_true] at target
  rcases target with hhorizontal | hbetween
  · simp only [horizontalTarget, Bool.and_eq_true,
      decide_eq_true_eq] at hhorizontal
    left
    refine ⟨finish.y, hhorizontal.1.1.1.1, hhorizontal.1.1.1.2,
      Option.isSome_iff_ne_none.mp hhorizontal.2, ?_⟩
    rw [← hhorizontal.1.2]
    exact path
  · simp only [verticalBetweenTarget, Bool.and_eq_true,
      decide_eq_true_eq] at hbetween
    right
    refine ⟨finish.x, hbetween.1.1.1,
      Option.isSome_iff_ne_none.mp hbetween.2, ?_⟩
    rw [← hbetween.1.2]
    exact path

theorem verticalReachPathCheck_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {west east column row boundary : Nat}
    (checked : verticalReachPathCheck grid width height fuel
      west east column row boundary = true) :
    VerticalSeamPath grid west east column row boundary := by
  unfold verticalReachPathCheck at checked
  cases hsearch : verticalReachSearch grid width height fuel
      west east column row boundary with
  | none => simp [hsearch] at checked
  | some node =>
      simp only [hsearch, Bool.and_eq_true] at checked
      have sound := searchFastWeightedReach_sound (show
        searchFastWeightedReach grid width height fuel
          [⟨horizontalPort grid column boundary, false⟩]
          (fun candidate => !candidate.parity &&
            verticalSeamTarget grid west east column row boundary
              candidate.current) = some node from hsearch)
      rcases sound with ⟨start, hstart, path⟩
      simp only [List.mem_singleton] at hstart
      subst start
      have nodeParity : node.parity = false :=
        Bool.eq_false_of_not_eq_true' checked.1
      have pathFalse : Path grid (horizontalPort grid column boundary)
          node.current false := by
        simpa [nodeParity] using path
      exact verticalSeamPath_of_target pathFalse checked.2

theorem horizontalReachPathCheck_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {south north row column boundary : Nat}
    (checked : horizontalReachPathCheck grid width height fuel
      south north row column boundary = true) :
    HorizontalSeamPath grid south north row column boundary := by
  unfold horizontalReachPathCheck at checked
  cases hsearch : horizontalReachSearch grid width height fuel
      south north row column boundary with
  | none => simp [hsearch] at checked
  | some node =>
      simp only [hsearch, Bool.and_eq_true] at checked
      have sound := searchFastWeightedReach_sound (show
        searchFastWeightedReach grid width height fuel
          [⟨verticalPort grid boundary row, false⟩]
          (fun candidate => !candidate.parity &&
            horizontalSeamTarget grid south north row column boundary
              candidate.current) = some node from hsearch)
      rcases sound with ⟨start, hstart, path⟩
      simp only [List.mem_singleton] at hstart
      subst start
      have nodeParity : node.parity = false :=
        Bool.eq_false_of_not_eq_true' checked.1
      have pathFalse : Path grid (verticalPort grid boundary row)
          node.current false := by
        simpa [nodeParity] using path
      exact horizontalSeamPath_of_target pathFalse checked.2

theorem verticalReachSeamCheck_sound_of_paths
    {grid : Nat → Nat → Index} {west east column row boundary : Nat}
    {found : List ReachNode}
    (paths : ∀ node ∈ found,
      Path grid (horizontalPort grid column boundary)
        node.current node.parity)
    (checked : verticalReachSeamCheck grid west east
      column row boundary found = true) :
    VerticalSeamPath grid west east column row boundary := by
  simp only [verticalReachSeamCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, hnode, hparity, htarget⟩
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hparity
  have pathFalse : Path grid (horizontalPort grid column boundary)
      node.current false := by
    simpa [nodeParity] using paths node hnode
  exact verticalSeamPath_of_target pathFalse htarget

theorem horizontalReachSeamCheck_sound_of_paths
    {grid : Nat → Nat → Index} {south north row column boundary : Nat}
    {found : List ReachNode}
    (paths : ∀ node ∈ found,
      Path grid (verticalPort grid boundary row) node.current node.parity)
    (checked : horizontalReachSeamCheck grid south north
      row column boundary found = true) :
    HorizontalSeamPath grid south north row column boundary := by
  simp only [horizontalReachSeamCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, hnode, hparity, htarget⟩
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hparity
  have pathFalse : Path grid (verticalPort grid boundary row)
      node.current false := by
    simpa [nodeParity] using paths node hnode
  exact horizontalSeamPath_of_target pathFalse htarget

theorem verticalReachCover_node_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {west east column boundary : Nat} {rows : List Nat} {node : ReachNode}
    (hnode : node ∈ verticalReachCover grid width height fuel
      west east column boundary rows) :
    Path grid (horizontalPort grid column boundary)
      node.current node.parity := by
  have sound := exploreFastWeightedReachCover_sound (show node ∈
      exploreFastWeightedReachCover grid width height fuel
        [⟨horizontalPort grid column boundary, false⟩] rows
        (fun candidate row => !candidate.parity &&
          verticalSeamTarget grid west east column row boundary
            candidate.current) from hnode)
  rcases sound with ⟨start, hstart, path⟩
  simp only [List.mem_singleton] at hstart
  subst start
  simpa using path

theorem horizontalReachCover_node_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {south north row boundary : Nat} {columns : List Nat} {node : ReachNode}
    (hnode : node ∈ horizontalReachCover grid width height fuel
      south north row boundary columns) :
    Path grid (verticalPort grid boundary row) node.current node.parity := by
  have sound := exploreFastWeightedReachCover_sound (show node ∈
      exploreFastWeightedReachCover grid width height fuel
        [⟨verticalPort grid boundary row, false⟩] columns
        (fun candidate column => !candidate.parity &&
          horizontalSeamTarget grid south north row column boundary
            candidate.current) from hnode)
  rcases sound with ⟨start, hstart, path⟩
  simp only [List.mem_singleton] at hstart
  subst start
  simpa using path

theorem verticalReachCover_check_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {west east column row boundary : Nat} {rows : List Nat}
    (checked : verticalReachSeamCheck grid west east column row boundary
      (verticalReachCover grid width height fuel
        west east column boundary rows) = true) :
    VerticalSeamPath grid west east column row boundary :=
  verticalReachSeamCheck_sound_of_paths
    (fun _ hnode => verticalReachCover_node_sound hnode) checked

theorem horizontalReachCover_check_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {south north row column boundary : Nat} {columns : List Nat}
    (checked : horizontalReachSeamCheck grid south north row column boundary
      (horizontalReachCover grid width height fuel
        south north row boundary columns) = true) :
    HorizontalSeamPath grid south north row column boundary :=
  horizontalReachSeamCheck_sound_of_paths
    (fun _ hnode => horizontalReachCover_node_sound hnode) checked

theorem verticalReachSeamCheck_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {west east column row boundary : Nat} {found : List ReachNode}
    (hfound : found = verticalReachFlood grid width height fuel column boundary)
    (checked : verticalReachSeamCheck grid west east
      column row boundary found = true) :
    VerticalSeamPath grid west east column row boundary := by
  subst found
  simp only [verticalReachSeamCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, hnode, hparity, htarget⟩
  have sound := exploreFastWeightedReach_sound (show node ∈
      exploreFastWeightedReach grid width height fuel
        [⟨horizontalPort grid column boundary, false⟩] from hnode)
  rcases sound with ⟨start, hstart, path⟩
  simp only [List.mem_singleton] at hstart
  subst start
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hparity
  have pathFalse : Path grid (horizontalPort grid column boundary)
      node.current false := by
    simpa [nodeParity] using path
  exact verticalSeamPath_of_target pathFalse htarget

theorem horizontalReachSeamCheck_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {south north row column boundary : Nat} {found : List ReachNode}
    (hfound : found = horizontalReachFlood grid width height fuel boundary row)
    (checked : horizontalReachSeamCheck grid south north
      row column boundary found = true) :
    HorizontalSeamPath grid south north row column boundary := by
  subst found
  simp only [horizontalReachSeamCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, hnode, hparity, htarget⟩
  have sound := exploreFastWeightedReach_sound (show node ∈
      exploreFastWeightedReach grid width height fuel
        [⟨verticalPort grid boundary row, false⟩] from hnode)
  rcases sound with ⟨start, hstart, path⟩
  simp only [List.mem_singleton] at hstart
  subst start
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hparity
  have pathFalse : Path grid (verticalPort grid boundary row)
      node.current false := by
    simpa [nodeParity] using path
  exact horizontalSeamPath_of_target pathFalse htarget

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

end PairCoverSeamPathSearch
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
