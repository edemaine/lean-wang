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

end RedShadeGraphWeightedSearch
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
