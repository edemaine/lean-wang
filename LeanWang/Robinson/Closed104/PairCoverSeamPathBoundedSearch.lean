/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPathSearch
import LeanWang.Robinson.Closed104.RedShadeGraphWeightedReachBounded

/-!
# Bounded soundness for seam-path cover searches

The executable seam checker searches inside a finite parent block.  This file
retains that bound in its semantic certificate, which is needed to transport a
constant-parent search path into the corresponding block of an arbitrary
coarse grid.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathBoundedSearch

open RedShadeGraph RedShadeGraphSearch RedShadeGraphWeightedSearch
  RedShadeGraphSearchSoundness RedShadeGraphWeightedReachBounded
  PairCoverSeamPathSearch PairCoverSeamShadePaths

theorem exploreWeightedReachCoverAux_boundedSound
    {Query : Type}
    {grid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {covers : ReachNode → Query → Bool} :
    ∀ (fuel : Nat) (stack : List ReachNode) (visited : Array Bool)
      (remaining : List Query) (found : List ReachNode),
      (∀ node ∈ stack,
        BoundedSoundReachFromWeighted grid width height starts node) →
      (∀ node ∈ found,
        BoundedSoundReachFromWeighted grid width height starts node) →
      ∀ node ∈ exploreWeightedReachCoverAux grid width height covers
        fuel stack visited remaining found,
        BoundedSoundReachFromWeighted grid width height starts node := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack visited remaining found _ hfound node hnode
      exact hfound node (by
        simpa [exploreWeightedReachCoverAux] using hnode)
  | succ fuel ih =>
      intro stack visited remaining found hstack hfound node hnode
      cases stack with
      | nil =>
          exact hfound node (by
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
              · exact markFreshReachList_boundedSound
                  (nodes := nextReachNodes grid width height first)
                  (visited := visited)
                  (fun next hnext => nextReachNodes_boundedSound
                    (hstack first (by simp)) hnext)
                  candidate hcandidate
            · intro candidate hcandidate
              simp only [List.mem_cons] at hcandidate
              rcases hcandidate with rfl | hcandidate
              · exact hstack _ (by simp)
              · exact hfound candidate hcandidate
            · exact hnode

theorem exploreFastWeightedReachCover_bounded_sound
    {Query : Type}
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {starts : List WeightedStart} {queries : List Query}
    {covers : ReachNode → Query → Bool} {node : ReachNode}
    (hstarts : ∀ start ∈ starts, PortInBounds start.port width height)
    (hnode : node ∈ exploreFastWeightedReachCover grid width height fuel
      starts queries covers) :
    BoundedSoundReachFromWeighted grid width height starts node := by
  unfold exploreFastWeightedReachCover at hnode
  let nodes := starts.map initialReachNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshReachList width emptyVisited nodes
  apply exploreWeightedReachCoverAux_boundedSound fuel marked.1 marked.2 queries []
  · exact markFreshReachList_boundedSound
      (nodes := nodes) (visited := emptyVisited) (by
        intro initial hinitial
        rcases List.mem_map.1 hinitial with ⟨start, hstart, rfl⟩
        exact initialReachNode_boundedSound hstart (hstarts start hstart))
  · simp
  · exact hnode

theorem verticalReachCover_node_bounded_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {west east column boundary : Nat} {rows : List Nat} {node : ReachNode}
    (startBound : PortInBounds (horizontalPort grid column boundary) width height)
    (hnode : node ∈ verticalReachCover grid width height fuel
      west east column boundary rows) :
    BoundedPath grid width height (horizontalPort grid column boundary)
      node.current node.parity := by
  have sound := exploreFastWeightedReachCover_bounded_sound
    (starts := [⟨horizontalPort grid column boundary, false⟩])
    (by
      intro start hstart
      simp only [List.mem_singleton] at hstart
      subst start
      exact startBound)
    (show node ∈ exploreFastWeightedReachCover grid width height fuel
      [⟨horizontalPort grid column boundary, false⟩] rows
      (fun candidate row => !candidate.parity &&
        verticalSeamTarget grid west east column row boundary
          candidate.current) from hnode)
  rcases sound with ⟨start, hstart, path⟩
  simp only [List.mem_singleton] at hstart
  subst start
  simpa using path

theorem horizontalReachCover_node_bounded_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {south north row boundary : Nat} {columns : List Nat} {node : ReachNode}
    (startBound : PortInBounds (verticalPort grid boundary row) width height)
    (hnode : node ∈ horizontalReachCover grid width height fuel
      south north row boundary columns) :
    BoundedPath grid width height (verticalPort grid boundary row)
      node.current node.parity := by
  have sound := exploreFastWeightedReachCover_bounded_sound
    (starts := [⟨verticalPort grid boundary row, false⟩])
    (by
      intro start hstart
      simp only [List.mem_singleton] at hstart
      subst start
      exact startBound)
    (show node ∈ exploreFastWeightedReachCover grid width height fuel
      [⟨verticalPort grid boundary row, false⟩] columns
      (fun candidate column => !candidate.parity &&
        horizontalSeamTarget grid south north row column boundary
          candidate.current) from hnode)
  rcases sound with ⟨start, hstart, path⟩
  simp only [List.mem_singleton] at hstart
  subst start
  simpa using path

end PairCoverSeamPathBoundedSearch
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
