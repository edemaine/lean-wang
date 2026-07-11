/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphSearchSoundness

/-!
# Parity-weighted multi-source red-graph search

An old outer-cycle source has weight zero, while an old free-line source has
weight one. The weighted flood stores total parity from the outer cycle in the
ordinary node parity field. Its soundness theorem recovers the local path
parity by cancelling the source weight.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphWeightedSearch

open RedShadeGraph RedShadeGraphSearch RedShadeGraphSearchSoundness

structure WeightedStart where
  port : Port
  parity : Bool
deriving DecidableEq, Repr

def initialNode (start : WeightedStart) : Node where
  origin := start.port
  current := start.port
  parity := start.parity
  reverseMoves := []

def exploreFastWeighted (indexGrid : Nat → Nat → Index)
    (width height fuel : Nat) (starts : List WeightedStart) : List Node :=
  let nodes := starts.map initialNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshList width emptyVisited nodes
  exploreFastAux indexGrid width height fuel marked.1 marked.2 []

def SoundFromWeighted (indexGrid : Nat → Nat → Index)
    (starts : List WeightedStart) (node : Node) : Prop :=
  ∃ start ∈ starts, node.origin = start.port ∧
    Path indexGrid start.port node.current
      (Bool.xor start.parity node.parity)

theorem initialNode_sound
    {indexGrid : Nat → Nat → Index} {starts : List WeightedStart}
    {start : WeightedStart} (hstart : start ∈ starts) :
    SoundFromWeighted indexGrid starts (initialNode start) := by
  exact ⟨start, hstart, rfl, by
    simpa [initialNode] using (Path.refl (indexGrid := indexGrid) start.port)⟩

theorem advance_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {node next : Node}
    {move : CertificateMove}
    (sound : SoundFromWeighted indexGrid starts node)
    (hadvance : advance indexGrid width height node move = some next) :
    SoundFromWeighted indexGrid starts next := by
  rcases sound with ⟨start, hstart, horigin, path⟩
  unfold advance at hadvance
  split at hadvance
  · rename_i hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    simp only [Option.some.injEq] at hadvance
    subst next
    refine ⟨start, hstart, horigin, ?_⟩
    have link := RedShadeGraphCertificate.Move.link_of_valid move hvalid.1.2
    rw [hvalid.1.1] at link
    simpa [Bool.xor_assoc] using Path.trans path (Path.ofLink link)
  · contradiction

theorem nextNodes_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {node next : Node}
    (sound : SoundFromWeighted indexGrid starts node)
    (hnext : next ∈ nextNodes indexGrid width height node) :
    SoundFromWeighted indexGrid starts next := by
  rw [nextNodes, List.mem_filterMap] at hnext
  rcases hnext with ⟨move, _, hadvance⟩
  exact advance_sound sound hadvance

theorem foldl_markFresh_sound
    {indexGrid : Nat → Nat → Index} {width : Nat}
    {starts : List WeightedStart} :
    ∀ (nodes : List Node) (accumulator : List Node × Array Bool),
      (∀ node ∈ nodes, SoundFromWeighted indexGrid starts node) →
      (∀ node ∈ accumulator.1, SoundFromWeighted indexGrid starts node) →
      ∀ node ∈ (nodes.foldl (markFresh width) accumulator).1,
        SoundFromWeighted indexGrid starts node := by
  intro nodes
  induction nodes with
  | nil =>
      intro accumulator _ haccumulator node hnode
      exact haccumulator node (by simpa using hnode)
  | cons first rest ih =>
      intro accumulator hnodes haccumulator node hnode
      have hfirst := hnodes first (by simp)
      have hrest : ∀ candidate ∈ rest,
          SoundFromWeighted indexGrid starts candidate := by
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
          · simpa [markFresh, hlookup] using hnode
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
              · simpa [markFresh, hlookup] using hnode
          | true =>
              exact ih accumulator hrest haccumulator node
                (by simpa [markFresh, hlookup] using hnode)

theorem markFreshList_sound
    {indexGrid : Nat → Nat → Index} {width : Nat}
    {starts : List WeightedStart} {nodes : List Node} {visited : Array Bool}
    (sound : ∀ node ∈ nodes, SoundFromWeighted indexGrid starts node) :
    ∀ node ∈ (markFreshList width visited nodes).1,
      SoundFromWeighted indexGrid starts node := by
  intro node hnode
  exact foldl_markFresh_sound nodes ([], visited) sound (by simp)
    node (by simpa [markFreshList] using hnode)

theorem exploreFastAux_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} :
    ∀ (fuel : Nat) (stack : List Node) (visited : Array Bool)
      (found : List Node),
      (∀ node ∈ stack, SoundFromWeighted indexGrid starts node) →
      (∀ node ∈ found, SoundFromWeighted indexGrid starts node) →
      ∀ node ∈ exploreFastAux indexGrid width height fuel
        stack visited found, SoundFromWeighted indexGrid starts node := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack visited found _ hfound node hnode
      exact hfound node (by simpa [RedShadeGraphSearch.exploreFastAux] using hnode)
  | succ fuel ih =>
      intro stack visited found hstack hfound node hnode
      cases stack with
      | nil =>
          exact hfound node (by
            simpa [RedShadeGraphSearch.exploreFastAux] using hnode)
      | cons first rest =>
          rw [RedShadeGraphSearch.exploreFastAux] at hnode
          let marked := markFreshList width visited
            (nextNodes indexGrid width height first)
          apply ih (marked.1 ++ rest) marked.2 (first :: found)
          · intro candidate hcandidate
            rcases List.mem_append.1 hcandidate with hcandidate | hcandidate
            · exact markFreshList_sound
                (nodes := nextNodes indexGrid width height first)
                (visited := visited)
                (fun next hnext => nextNodes_sound
                  (hstack first (by simp)) hnext)
                candidate hcandidate
            · exact hstack candidate (by simp [hcandidate])
          · intro candidate hcandidate
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hcandidate
            · exact hstack candidate (by simp)
            · exact hfound candidate hcandidate
          · exact hnode

/-- Every weighted flood node has a genuine path with its source weight removed. -/
theorem exploreFastWeighted_sound
    {indexGrid : Nat → Nat → Index} {width height fuel : Nat}
    {starts : List WeightedStart} {node : Node}
    (hnode : node ∈ exploreFastWeighted indexGrid width height fuel starts) :
    SoundFromWeighted indexGrid starts node := by
  unfold exploreFastWeighted at hnode
  let nodes := starts.map initialNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshList width emptyVisited nodes
  apply exploreFastAux_sound fuel marked.1 marked.2 []
  · exact markFreshList_sound
      (nodes := nodes) (visited := emptyVisited) (by
        intro initial hinitial
        rcases List.mem_map.1 hinitial with ⟨start, hstart, rfl⟩
        exact initialNode_sound hstart)
  · simp
  · exact hnode

/-- Weighted search soundness retaining every intermediate search-box bound. -/
def BoundedSoundFromWeighted (indexGrid : Nat → Nat → Index)
    (width height : Nat) (starts : List WeightedStart) (node : Node) : Prop :=
  ∃ start ∈ starts,
    BoundedPath indexGrid width height start.port node.current
      (Bool.xor start.parity node.parity)

theorem initialNode_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {start : WeightedStart}
    (hstart : start ∈ starts) (hbound : PortInBounds start.port width height) :
    BoundedSoundFromWeighted indexGrid width height starts (initialNode start) := by
  exact ⟨start, hstart, by
    simpa [initialNode] using
      (BoundedPath.refl (indexGrid := indexGrid) start.port hbound)⟩

theorem advance_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {node next : Node} {move : CertificateMove}
    (sound : BoundedSoundFromWeighted indexGrid width height starts node)
    (hadvance : advance indexGrid width height node move = some next) :
    BoundedSoundFromWeighted indexGrid width height starts next := by
  rcases sound with ⟨start, hstart, path⟩
  unfold advance at hadvance
  split at hadvance
  · rename_i hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    simp only [Option.some.injEq] at hadvance
    subst next
    refine ⟨start, hstart, ?_⟩
    have link := RedShadeGraphCertificate.Move.link_of_valid move hvalid.1.2
    rw [hvalid.1.1] at link
    have nextBound : PortInBounds
        (RedShadeGraphCertificate.Move.second move) width height := by
      simpa [PortInBounds, inBounds, Bool.and_eq_true] using hvalid.2
    simpa [Bool.xor_assoc] using BoundedPath.trans path
      (BoundedPath.ofLink link path.second_inBounds nextBound)
  · contradiction

theorem nextNodes_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {node next : Node}
    (sound : BoundedSoundFromWeighted indexGrid width height starts node)
    (hnext : next ∈ nextNodes indexGrid width height node) :
    BoundedSoundFromWeighted indexGrid width height starts next := by
  rw [nextNodes, List.mem_filterMap] at hnext
  rcases hnext with ⟨move, _, hadvance⟩
  exact advance_boundedSound sound hadvance

theorem foldl_markFresh_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} :
    ∀ (nodes : List Node) (accumulator : List Node × Array Bool),
      (∀ node ∈ nodes,
        BoundedSoundFromWeighted indexGrid width height starts node) →
      (∀ node ∈ accumulator.1,
        BoundedSoundFromWeighted indexGrid width height starts node) →
      ∀ node ∈ (nodes.foldl (markFresh width) accumulator).1,
        BoundedSoundFromWeighted indexGrid width height starts node := by
  intro nodes
  induction nodes with
  | nil =>
      intro accumulator _ haccumulator node hnode
      exact haccumulator node (by simpa using hnode)
  | cons first rest ih =>
      intro accumulator hnodes haccumulator node hnode
      have hfirst := hnodes first (by simp)
      have hrest : ∀ candidate ∈ rest,
          BoundedSoundFromWeighted indexGrid width height starts candidate := by
        intro candidate hcandidate
        exact hnodes candidate (by simp [hcandidate])
      simp only [List.foldl_cons] at hnode
      cases hlookup : accumulator.2[stateCode width first.state]? with
      | none =>
          apply ih (first :: accumulator.1,
            accumulator.2.setIfInBounds (stateCode width first.state) true)
            hrest
          · intro candidate hcandidate
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hcandidate
            · exact hfirst
            · exact haccumulator candidate hcandidate
          · simpa [markFresh, hlookup] using hnode
      | some present =>
          cases present with
          | false =>
              apply ih (first :: accumulator.1,
                accumulator.2.setIfInBounds (stateCode width first.state) true)
                hrest
              · intro candidate hcandidate
                simp only [List.mem_cons] at hcandidate
                rcases hcandidate with rfl | hcandidate
                · exact hfirst
                · exact haccumulator candidate hcandidate
              · simpa [markFresh, hlookup] using hnode
          | true =>
              exact ih accumulator hrest haccumulator node
                (by simpa [markFresh, hlookup] using hnode)

theorem markFreshList_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {nodes : List Node} {visited : Array Bool}
    (sound : ∀ node ∈ nodes,
      BoundedSoundFromWeighted indexGrid width height starts node) :
    ∀ node ∈ (markFreshList width visited nodes).1,
      BoundedSoundFromWeighted indexGrid width height starts node := by
  intro node hnode
  exact foldl_markFresh_boundedSound nodes ([], visited) sound
    (by simp) node (by simpa [markFreshList] using hnode)

theorem exploreFastAux_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} :
    ∀ (fuel : Nat) (stack : List Node) (visited : Array Bool)
      (found : List Node),
      (∀ node ∈ stack,
        BoundedSoundFromWeighted indexGrid width height starts node) →
      (∀ node ∈ found,
        BoundedSoundFromWeighted indexGrid width height starts node) →
      ∀ node ∈ exploreFastAux indexGrid width height fuel
        stack visited found,
        BoundedSoundFromWeighted indexGrid width height starts node := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack visited found _ hfound node hnode
      exact hfound node (by simpa [RedShadeGraphSearch.exploreFastAux] using hnode)
  | succ fuel ih =>
      intro stack visited found hstack hfound node hnode
      cases stack with
      | nil =>
          exact hfound node (by
            simpa [RedShadeGraphSearch.exploreFastAux] using hnode)
      | cons first rest =>
          rw [RedShadeGraphSearch.exploreFastAux] at hnode
          let marked := markFreshList width visited
            (nextNodes indexGrid width height first)
          apply ih (marked.1 ++ rest) marked.2 (first :: found)
          · intro candidate hcandidate
            rcases List.mem_append.1 hcandidate with hcandidate | hcandidate
            · exact markFreshList_boundedSound
                (nodes := nextNodes indexGrid width height first)
                (visited := visited)
                (fun next hnext => nextNodes_boundedSound
                  (hstack first (by simp)) hnext)
                candidate hcandidate
            · exact hstack candidate (by simp [hcandidate])
          · intro candidate hcandidate
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hcandidate
            · exact hstack _ (by simp)
            · exact hfound candidate hcandidate
          · exact hnode

/-- Every weighted full-search path remains inside its declared search box. -/
theorem exploreFastWeighted_bounded_sound
    {indexGrid : Nat → Nat → Index} {width height fuel : Nat}
    {starts : List WeightedStart} {node : Node}
    (hstarts : ∀ start ∈ starts, PortInBounds start.port width height)
    (hnode : node ∈ exploreFastWeighted indexGrid width height fuel starts) :
    BoundedSoundFromWeighted indexGrid width height starts node := by
  unfold exploreFastWeighted at hnode
  let nodes := starts.map initialNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshList width emptyVisited nodes
  apply exploreFastAux_boundedSound fuel marked.1 marked.2 []
  · exact markFreshList_boundedSound
      (nodes := nodes) (visited := emptyVisited) (by
        intro initial hinitial
        rcases List.mem_map.1 hinitial with ⟨start, hstart, rfl⟩
        exact initialNode_boundedSound hstart (hstarts start hstart))
  · simp
  · exact hnode

def initialReachNode (start : WeightedStart) : ReachNode where
  current := start.port
  parity := start.parity

def exploreWeightedReachAux (indexGrid : Nat → Nat → Index)
    (width height : Nat) :
    Nat → List ReachNode → Array Bool → List ReachNode → List ReachNode
  | 0, _, _, found => found
  | _ + 1, [], _, found => found
  | fuel + 1, node :: stack, visited, found =>
      let marked := markFreshReachList width visited
        (nextReachNodes indexGrid width height node)
      exploreWeightedReachAux indexGrid width height fuel
        (marked.1 ++ stack) marked.2 (node :: found)

/-- Lightweight weighted flood used by exhaustive coverage audits. -/
def exploreFastWeightedReach (indexGrid : Nat → Nat → Index)
    (width height fuel : Nat) (starts : List WeightedStart) : List ReachNode :=
  let nodes := starts.map initialReachNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshReachList width emptyVisited nodes
  exploreWeightedReachAux indexGrid width height fuel marked.1 marked.2 []

def SoundReachFromWeighted (indexGrid : Nat → Nat → Index)
    (starts : List WeightedStart) (node : ReachNode) : Prop :=
  ∃ start ∈ starts, Path indexGrid start.port node.current
    (Bool.xor start.parity node.parity)

theorem initialReachNode_sound
    {indexGrid : Nat → Nat → Index} {starts : List WeightedStart}
    {start : WeightedStart} (hstart : start ∈ starts) :
    SoundReachFromWeighted indexGrid starts (initialReachNode start) := by
  exact ⟨start, hstart, by
    simpa [initialReachNode] using
      (Path.refl (indexGrid := indexGrid) start.port)⟩

theorem advanceReach_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {node next : ReachNode}
    {move : CertificateMove}
    (sound : SoundReachFromWeighted indexGrid starts node)
    (hadvance : advanceReach indexGrid width height node move = some next) :
    SoundReachFromWeighted indexGrid starts next := by
  rcases sound with ⟨start, hstart, path⟩
  unfold advanceReach at hadvance
  split at hadvance
  · rename_i hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    simp only [Option.some.injEq] at hadvance
    subst next
    refine ⟨start, hstart, ?_⟩
    have link := RedShadeGraphCertificate.Move.link_of_valid move hvalid.1.2
    rw [hvalid.1.1] at link
    simpa [Bool.xor_assoc] using Path.trans path (Path.ofLink link)
  · contradiction

theorem nextReachNodes_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} {node next : ReachNode}
    (sound : SoundReachFromWeighted indexGrid starts node)
    (hnext : next ∈ nextReachNodes indexGrid width height node) :
    SoundReachFromWeighted indexGrid starts next := by
  rw [nextReachNodes, List.mem_filterMap] at hnext
  rcases hnext with ⟨move, _, hadvance⟩
  exact advanceReach_sound sound hadvance

theorem foldl_markFreshReach_sound
    {indexGrid : Nat → Nat → Index} {width : Nat}
    {starts : List WeightedStart} :
    ∀ (nodes : List ReachNode)
      (accumulator : List ReachNode × Array Bool),
      (∀ node ∈ nodes, SoundReachFromWeighted indexGrid starts node) →
      (∀ node ∈ accumulator.1,
        SoundReachFromWeighted indexGrid starts node) →
      ∀ node ∈ (nodes.foldl (markFreshReach width) accumulator).1,
        SoundReachFromWeighted indexGrid starts node := by
  intro nodes
  induction nodes with
  | nil =>
      intro accumulator _ haccumulator node hnode
      exact haccumulator node (by simpa using hnode)
  | cons first rest ih =>
      intro accumulator hnodes haccumulator node hnode
      have hfirst := hnodes first (by simp)
      have hrest : ∀ candidate ∈ rest,
          SoundReachFromWeighted indexGrid starts candidate := by
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

theorem markFreshReachList_sound
    {indexGrid : Nat → Nat → Index} {width : Nat}
    {starts : List WeightedStart} {nodes : List ReachNode}
    {visited : Array Bool}
    (sound : ∀ node ∈ nodes,
      SoundReachFromWeighted indexGrid starts node) :
    ∀ node ∈ (markFreshReachList width visited nodes).1,
      SoundReachFromWeighted indexGrid starts node := by
  intro node hnode
  exact foldl_markFreshReach_sound nodes ([], visited) sound (by simp)
    node (by simpa [markFreshReachList] using hnode)

theorem exploreWeightedReachAux_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List WeightedStart} :
    ∀ (fuel : Nat) (stack : List ReachNode) (visited : Array Bool)
      (found : List ReachNode),
      (∀ node ∈ stack, SoundReachFromWeighted indexGrid starts node) →
      (∀ node ∈ found, SoundReachFromWeighted indexGrid starts node) →
      ∀ node ∈ exploreWeightedReachAux indexGrid width height fuel
        stack visited found,
        SoundReachFromWeighted indexGrid starts node := by
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
            · exact markFreshReachList_sound
                (nodes := nextReachNodes indexGrid width height first)
                (visited := visited)
                (fun next hnext => nextReachNodes_sound
                  (hstack first (by simp)) hnext)
                candidate hcandidate
            · exact hstack candidate (by simp [hcandidate])
          · intro candidate hcandidate
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hcandidate
            · exact hstack candidate (by simp)
            · exact hfound candidate hcandidate
          · exact hnode

/-- Every lightweight weighted flood node has a genuine parity-labelled path. -/
theorem exploreFastWeightedReach_sound
    {indexGrid : Nat → Nat → Index} {width height fuel : Nat}
    {starts : List WeightedStart} {node : ReachNode}
    (hnode : node ∈ exploreFastWeightedReach indexGrid width height fuel starts) :
    SoundReachFromWeighted indexGrid starts node := by
  unfold exploreFastWeightedReach at hnode
  let nodes := starts.map initialReachNode
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshReachList width emptyVisited nodes
  apply exploreWeightedReachAux_sound fuel marked.1 marked.2 []
  · exact markFreshReachList_sound
      (nodes := nodes) (visited := emptyVisited) (by
        intro initial hinitial
        rcases List.mem_map.1 hinitial with ⟨start, hstart, rfl⟩
        exact initialReachNode_sound hstart)
  · simp
  · exact hnode

end RedShadeGraphWeightedSearch
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
