/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphWeightedSearch

/-! Bounded-path soundness for the lightweight weighted flood. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphWeightedReachBounded

open RedShadeGraph RedShadeGraphCertificate RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch

def BoundedSoundReachFromWeighted (indexGrid : Nat → Nat → Index)
    (width height : Nat) (starts : List WeightedStart) (node : ReachNode) : Prop :=
  ∃ start ∈ starts,
    BoundedPath indexGrid width height start.port node.current
      (Bool.xor start.parity node.parity)

theorem initialReachNode_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {start : WeightedStart}
    (hstart : start ∈ starts) (hbound : PortInBounds start.port width height) :
    BoundedSoundReachFromWeighted indexGrid width height starts
      (initialReachNode start) := by
  exact ⟨start, hstart, by
    simpa [initialReachNode] using
      (BoundedPath.refl (indexGrid := indexGrid) start.port hbound)⟩

theorem advanceReach_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {node next : ReachNode}
    {move : CertificateMove}
    (sound : BoundedSoundReachFromWeighted
      indexGrid width height starts node)
    (hadvance : advanceReach indexGrid width height node move = some next) :
    BoundedSoundReachFromWeighted indexGrid width height starts next := by
  rcases sound with ⟨start, hstart, path⟩
  unfold advanceReach at hadvance
  split at hadvance
  · rename_i hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    simp only [Option.some.injEq] at hadvance
    subst next
    refine ⟨start, hstart, ?_⟩
    have link := Move.link_of_valid move hvalid.1.2
    rw [hvalid.1.1] at link
    have nextBound : PortInBounds (Move.second move) width height := by
      simpa [PortInBounds, inBounds, Bool.and_eq_true] using hvalid.2
    simpa [Bool.xor_assoc] using BoundedPath.trans path
      (BoundedPath.ofLink link path.second_inBounds nextBound)
  · contradiction

theorem nextReachNodes_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {node next : ReachNode}
    (sound : BoundedSoundReachFromWeighted
      indexGrid width height starts node)
    (hnext : next ∈ nextReachNodes indexGrid width height node) :
    BoundedSoundReachFromWeighted indexGrid width height starts next := by
  rw [nextReachNodes, List.mem_filterMap] at hnext
  rcases hnext with ⟨move, _, hadvance⟩
  exact advanceReach_boundedSound sound hadvance

theorem foldl_markFreshReach_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} :
    ∀ (nodes : List ReachNode)
      (accumulator : List ReachNode × Array Bool),
      (∀ node ∈ nodes,
        BoundedSoundReachFromWeighted indexGrid width height starts node) →
      (∀ node ∈ accumulator.1,
        BoundedSoundReachFromWeighted indexGrid width height starts node) →
      ∀ node ∈ (nodes.foldl (markFreshReach width) accumulator).1,
        BoundedSoundReachFromWeighted indexGrid width height starts node := by
  intro nodes
  induction nodes with
  | nil =>
      intro accumulator _ haccumulator node hnode
      exact haccumulator node (by simpa using hnode)
  | cons first rest ih =>
      intro accumulator hnodes haccumulator node hnode
      have hfirst := hnodes first (by simp)
      have hrest : ∀ candidate ∈ rest,
          BoundedSoundReachFromWeighted
            indexGrid width height starts candidate := by
        intro candidate hcandidate
        exact hnodes candidate (by simp [hcandidate])
      simp only [List.foldl_cons] at hnode
      cases hlookup : accumulator.2[stateCode width first.state]? with
      | none =>
          apply ih (first :: accumulator.1,
            accumulator.2.setIfInBounds
              (stateCode width first.state) true) hrest
          · intro candidate hcandidate
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hcandidate
            · exact hfirst
            · exact haccumulator candidate hcandidate
          · simpa [markFreshReach, hlookup] using hnode
      | some present =>
          cases present with
          | false =>
              apply ih (first :: accumulator.1,
                accumulator.2.setIfInBounds
                  (stateCode width first.state) true) hrest
              · intro candidate hcandidate
                simp only [List.mem_cons] at hcandidate
                rcases hcandidate with rfl | hcandidate
                · exact hfirst
                · exact haccumulator candidate hcandidate
              · simpa [markFreshReach, hlookup] using hnode
          | true =>
              exact ih accumulator hrest haccumulator node
                (by simpa [markFreshReach, hlookup] using hnode)

theorem markFreshReachList_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {nodes : List ReachNode}
    {visited : Array Bool}
    (sound : ∀ node ∈ nodes,
      BoundedSoundReachFromWeighted indexGrid width height starts node) :
    ∀ node ∈ (markFreshReachList width visited nodes).1,
      BoundedSoundReachFromWeighted indexGrid width height starts node := by
  intro node hnode
  exact foldl_markFreshReach_boundedSound nodes ([], visited) sound
    (by simp) node (by simpa [markFreshReachList] using hnode)

theorem exploreWeightedReachAux_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} :
    ∀ (fuel : Nat) (stack : List ReachNode) (visited : Array Bool)
      (found : List ReachNode),
      (∀ node ∈ stack,
        BoundedSoundReachFromWeighted indexGrid width height starts node) →
      (∀ node ∈ found,
        BoundedSoundReachFromWeighted indexGrid width height starts node) →
      ∀ node ∈ exploreWeightedReachAux indexGrid width height fuel
        stack visited found,
        BoundedSoundReachFromWeighted indexGrid width height starts node := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack visited found _ hfound node hnode
      exact hfound node (by simpa [exploreWeightedReachAux] using hnode)
  | succ fuel ih =>
      intro stack visited found hstack hfound node hnode
      cases stack with
      | nil =>
          exact hfound node (by
            simpa [exploreWeightedReachAux] using hnode)
      | cons first rest =>
          rw [exploreWeightedReachAux] at hnode
          let marked := markFreshReachList width visited
            (nextReachNodes indexGrid width height first)
          apply ih (marked.1 ++ rest) marked.2 (first :: found)
          · intro candidate hcandidate
            rcases List.mem_append.1 hcandidate with hcandidate | hcandidate
            · exact markFreshReachList_boundedSound
                (nodes := nextReachNodes indexGrid width height first)
                (visited := visited)
                (fun next hnext => nextReachNodes_boundedSound
                  (hstack first (by simp)) hnext)
                candidate hcandidate
            · exact hstack candidate (by simp [hcandidate])
          · intro candidate hcandidate
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hcandidate
            · exact hstack candidate (by simp)
            · exact hfound candidate hcandidate
          · exact hnode

/-- Every lightweight weighted flood path remains in its declared box. -/
theorem exploreFastWeightedReach_bounded_sound
    {indexGrid : Nat → Nat → Index} {width height fuel : Nat}
    {starts : List WeightedStart} {node : ReachNode}
    (hstarts : ∀ start ∈ starts, PortInBounds start.port width height)
    (hnode : node ∈
      exploreFastWeightedReach indexGrid width height fuel starts) :
    BoundedSoundReachFromWeighted indexGrid width height starts node := by
  unfold exploreFastWeightedReach at hnode
  let nodes := starts.map initialReachNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshReachList width emptyVisited nodes
  apply exploreWeightedReachAux_boundedSound fuel marked.1 marked.2 []
  · exact markFreshReachList_boundedSound
      (nodes := nodes) (visited := emptyVisited) (by
        intro initial hinitial
        rcases List.mem_map.1 hinitial with ⟨start, hstart, rfl⟩
        exact initialReachNode_boundedSound hstart (hstarts start hstart))
  · simp
  · exact hnode

end RedShadeGraphWeightedReachBounded
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
