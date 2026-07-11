/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphSearch

/-!
Soundness of bounded red-shade graph search.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphSearchSoundness

open RedShadeGraph RedShadeGraphCertificate RedShadeGraphSearch

def SoundFrom (indexGrid : Nat → Nat → Index)
    (start : Port) (node : Node) : Prop :=
  node.origin = start ∧ Path indexGrid start node.current node.parity

theorem advance_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {start : Port} {node next : Node} {move : CertificateMove}
    (sound : SoundFrom indexGrid start node)
    (hadvance : advance indexGrid width height node move = some next) :
    SoundFrom indexGrid start next := by
  unfold advance at hadvance
  split at hadvance
  · rename_i hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    simp only [Option.some.injEq] at hadvance
    subst next
    constructor
    · exact sound.1
    · have hlink := RedShadeGraphCertificate.Move.link_of_valid move
          hvalid.1.2
      rw [hvalid.1.1] at hlink
      exact Path.trans sound.2 (Path.ofLink hlink)
  · contradiction

theorem nextNodes_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {start : Port} {node next : Node}
    (sound : SoundFrom indexGrid start node)
    (hnext : next ∈ nextNodes indexGrid width height node) :
    SoundFrom indexGrid start next := by
  rw [nextNodes, List.mem_filterMap] at hnext
  rcases hnext with ⟨move, _, hadvance⟩
  exact advance_sound sound hadvance

theorem freshNodes_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {start : Port} {node next : Node} {visited : List (Port × Bool)}
    (sound : SoundFrom indexGrid start node)
    (hnext : next ∈ freshNodes visited
      (nextNodes indexGrid width height node)) :
    SoundFrom indexGrid start next := by
  exact nextNodes_sound sound (List.mem_of_mem_filter hnext)

theorem searchAux_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {accept : Port → Bool → Bool} {start : Port} :
    ∀ (fuel : Nat) {queue : List Node} {visited : List (Port × Bool)}
      {result : Node},
      (∀ node ∈ queue, SoundFrom indexGrid start node) →
      searchAux indexGrid width height accept fuel queue visited = some result →
      SoundFrom indexGrid start result := by
  intro fuel
  induction fuel with
  | zero =>
      intro queue visited result _ hsearch
      simp [searchAux] at hsearch
  | succ fuel ih =>
      intro queue visited result hqueue hsearch
      cases queue with
      | nil => simp [searchAux] at hsearch
      | cons node queue =>
          rw [searchAux] at hsearch
          split at hsearch
          · simp only [Option.some.injEq] at hsearch
            subst result
            exact hqueue node (by simp)
          · apply ih (queue := queue ++
                freshNodes visited (nextNodes indexGrid width height node))
              (visited := visited ++
                (freshNodes visited
                  (nextNodes indexGrid width height node)).map Node.state)
              ?_ hsearch
            intro candidate hcandidate
            rw [List.mem_append] at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · exact hqueue candidate (by simp [hcandidate])
            · exact freshNodes_sound
                (hqueue node (by simp)) hcandidate

/-- Every successful bounded search returns a genuine parity-labelled path. -/
theorem search_sound
    {indexGrid : Nat → Nat → Index} {width height fuel : Nat}
    {start finish : Port} {parity : Bool}
    {accept : Port → Bool → Bool} {moves : List CertificateMove}
    (hsearch : search indexGrid width height fuel start accept =
      some (finish, parity, moves)) :
    Path indexGrid start finish parity := by
  unfold search at hsearch
  split at hsearch
  · rename_i hbounds
    cases hresult : searchAux indexGrid width height accept fuel
        [⟨start, start, false, []⟩] [(start, false)] with
    | none => simp [hresult] at hsearch
    | some result =>
        rw [hresult] at hsearch
        simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at hsearch
        rcases hsearch with ⟨rfl, rfl, rfl⟩
        exact (searchAux_sound fuel (by
          intro node hnode
          simp only [List.mem_singleton] at hnode
          subst node
          exact ⟨rfl, Path.refl start⟩) hresult).2
  · contradiction

def SoundFromSome (indexGrid : Nat → Nat → Index)
    (starts : List Port) (node : Node) : Prop :=
  node.origin ∈ starts ∧ Path indexGrid node.origin node.current node.parity

theorem advance_soundFromSome
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List Port} {node next : Node} {move : CertificateMove}
    (sound : SoundFromSome indexGrid starts node)
    (hadvance : advance indexGrid width height node move = some next) :
    SoundFromSome indexGrid starts next := by
  have preserved := advance_sound
    (start := node.origin) ⟨rfl, sound.2⟩ hadvance
  constructor
  · rw [preserved.1]
    exact sound.1
  · rw [preserved.1]
    exact preserved.2

theorem nextNodes_soundFromSome
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List Port} {node next : Node}
    (sound : SoundFromSome indexGrid starts node)
    (hnext : next ∈ nextNodes indexGrid width height node) :
    SoundFromSome indexGrid starts next := by
  rw [nextNodes, List.mem_filterMap] at hnext
  rcases hnext with ⟨move, _, hadvance⟩
  exact advance_soundFromSome sound hadvance

theorem foldl_markFresh_soundFromSome
    {indexGrid : Nat → Nat → Index} {width : Nat}
    {starts : List Port} :
    ∀ (nodes : List Node) (accumulator : List Node × Array Bool),
      (∀ node ∈ nodes, SoundFromSome indexGrid starts node) →
      (∀ node ∈ accumulator.1, SoundFromSome indexGrid starts node) →
      ∀ node ∈ (nodes.foldl (markFresh width) accumulator).1,
        SoundFromSome indexGrid starts node := by
  intro nodes
  induction nodes with
  | nil =>
      intro accumulator _ haccumulator node hnode
      exact haccumulator node (by simpa using hnode)
  | cons first rest ih =>
      intro accumulator hnodes haccumulator node hnode
      have hfirst := hnodes first (by simp)
      have hrest : ∀ candidate ∈ rest,
          SoundFromSome indexGrid starts candidate := by
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
              apply ih accumulator hrest haccumulator
              simpa [markFresh, hlookup] using hnode

theorem markFreshList_soundFromSome
    {indexGrid : Nat → Nat → Index} {width : Nat}
    {starts : List Port} {nodes : List Node} {visited : Array Bool}
    (sound : ∀ node ∈ nodes, SoundFromSome indexGrid starts node) :
    ∀ node ∈ (markFreshList width visited nodes).1,
      SoundFromSome indexGrid starts node := by
  intro node hnode
  exact foldl_markFresh_soundFromSome nodes ([], visited) sound
    (by simp) node (by simpa [markFreshList] using hnode)

theorem exploreFastAux_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List Port} :
    ∀ (fuel : Nat) (stack : List Node) (visited : Array Bool)
      (found : List Node),
      (∀ node ∈ stack, SoundFromSome indexGrid starts node) →
      (∀ node ∈ found, SoundFromSome indexGrid starts node) →
      ∀ node ∈ exploreFastAux indexGrid width height fuel
        stack visited found, SoundFromSome indexGrid starts node := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack visited found _ hfound node hnode
      exact hfound node (by simpa [exploreFastAux] using hnode)
  | succ fuel ih =>
      intro stack visited found hstack hfound node hnode
      cases stack with
      | nil => exact hfound node (by simpa [exploreFastAux] using hnode)
      | cons first rest =>
          rw [exploreFastAux] at hnode
          let marked := markFreshList width visited
            (nextNodes indexGrid width height first)
          apply ih (marked.1 ++ rest) marked.2 (first :: found)
          · intro candidate hcandidate
            rw [List.mem_append] at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · exact markFreshList_soundFromSome
                (nodes := nextNodes indexGrid width height first)
                (visited := visited)
                (fun next hnext => nextNodes_soundFromSome
                  (hstack first (by simp)) hnext)
                candidate hcandidate
            · exact hstack candidate (by simp [hcandidate])
          · intro candidate hcandidate
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hcandidate
            · exact hstack _ (by simp)
            · exact hfound candidate hcandidate
          · exact hnode

/-- Every node retained by the fast multi-source flood has a genuine path. -/
theorem exploreFast_sound
    {indexGrid : Nat → Nat → Index} {width height fuel : Nat}
    {starts : List Port} {node : Node}
    (hnode : node ∈ exploreFast indexGrid width height fuel starts) :
    SoundFromSome indexGrid starts node := by
  unfold exploreFast at hnode
  let nodes : List Node := starts.map fun start =>
    { origin := start, current := start, parity := false, reverseMoves := [] }
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshList width emptyVisited nodes
  apply exploreFastAux_sound fuel marked.1 marked.2 []
  · exact markFreshList_soundFromSome
      (nodes := nodes) (visited := emptyVisited) (by
        intro initial hinitial
        rcases List.mem_map.1 hinitial with ⟨start, hstart, rfl⟩
        exact ⟨hstart, Path.refl start⟩)
  · simp
  · exact hnode

def PortInBounds (port : Port) (width height : Nat) : Prop :=
  port.x < width ∧ port.y < height

/-- A graph path retaining the search box bound at every intermediate port. -/
inductive BoundedPath (indexGrid : Nat → Nat → Index)
    (width height : Nat) : Port → Port → Bool → Prop where
  | refl (port : Port) (hport : PortInBounds port width height) :
      BoundedPath indexGrid width height port port false
  | ofLink {first second : Port} {parity : Bool}
      (link : Link indexGrid first second parity)
      (hfirst : PortInBounds first width height)
      (hsecond : PortInBounds second width height) :
      BoundedPath indexGrid width height first second parity
  | trans {first second third : Port} {firstParity secondParity : Bool}
      (firstPath : BoundedPath indexGrid width height
        first second firstParity)
      (secondPath : BoundedPath indexGrid width height
        second third secondParity) :
      BoundedPath indexGrid width height first third
        (Bool.xor firstParity secondParity)

theorem BoundedPath.path
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    Path indexGrid first second parity := by
  induction path with
  | refl port _ => exact Path.refl port
  | ofLink link _ _ => exact Path.ofLink link
  | trans _ _ firstIH secondIH => exact Path.trans firstIH secondIH

theorem BoundedPath.first_inBounds
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    PortInBounds first width height := by
  induction path with
  | refl _ hport => exact hport
  | ofLink _ hfirst _ => exact hfirst
  | trans _ _ firstIH _ => exact firstIH

theorem BoundedPath.second_inBounds
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    PortInBounds second width height := by
  induction path with
  | refl _ hport => exact hport
  | ofLink _ _ hsecond => exact hsecond
  | trans _ _ _ secondIH => exact secondIH

def BoundedSoundFromSome (indexGrid : Nat → Nat → Index)
    (width height : Nat) (starts : List Port) (node : Node) : Prop :=
  node.origin ∈ starts ∧
    BoundedPath indexGrid width height
      node.origin node.current node.parity

theorem advance_boundedSoundFromSome
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List Port} {node next : Node} {move : CertificateMove}
    (sound : BoundedSoundFromSome indexGrid width height starts node)
    (hadvance : advance indexGrid width height node move = some next) :
    BoundedSoundFromSome indexGrid width height starts next := by
  unfold advance at hadvance
  split at hadvance
  · rename_i hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    simp only [Option.some.injEq] at hadvance
    subst next
    constructor
    · exact sound.1
    · have hlink := RedShadeGraphCertificate.Move.link_of_valid move
          hvalid.1.2
      rw [hvalid.1.1] at hlink
      have hnextBound :
          PortInBounds (RedShadeGraphCertificate.Move.second move)
            width height := by
        simpa [PortInBounds, inBounds, Bool.and_eq_true] using hvalid.2
      exact BoundedPath.trans sound.2
        (BoundedPath.ofLink hlink sound.2.second_inBounds hnextBound)
  · contradiction

theorem nextNodes_boundedSoundFromSome
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List Port} {node next : Node}
    (sound : BoundedSoundFromSome indexGrid width height starts node)
    (hnext : next ∈ nextNodes indexGrid width height node) :
    BoundedSoundFromSome indexGrid width height starts next := by
  rw [nextNodes, List.mem_filterMap] at hnext
  rcases hnext with ⟨move, _, hadvance⟩
  exact advance_boundedSoundFromSome sound hadvance

theorem foldl_markFresh_boundedSoundFromSome
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List Port} :
    ∀ (nodes : List Node) (accumulator : List Node × Array Bool),
      (∀ node ∈ nodes,
        BoundedSoundFromSome indexGrid width height starts node) →
      (∀ node ∈ accumulator.1,
        BoundedSoundFromSome indexGrid width height starts node) →
      ∀ node ∈ (nodes.foldl (markFresh width) accumulator).1,
        BoundedSoundFromSome indexGrid width height starts node := by
  intro nodes
  induction nodes with
  | nil =>
      intro accumulator _ haccumulator node hnode
      exact haccumulator node (by simpa using hnode)
  | cons first rest ih =>
      intro accumulator hnodes haccumulator node hnode
      have hfirst := hnodes first (by simp)
      have hrest : ∀ candidate ∈ rest,
          BoundedSoundFromSome indexGrid width height starts candidate := by
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
              apply ih accumulator hrest haccumulator
              simpa [markFresh, hlookup] using hnode

theorem markFreshList_boundedSoundFromSome
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List Port} {nodes : List Node} {visited : Array Bool}
    (sound : ∀ node ∈ nodes,
      BoundedSoundFromSome indexGrid width height starts node) :
    ∀ node ∈ (markFreshList width visited nodes).1,
      BoundedSoundFromSome indexGrid width height starts node := by
  intro node hnode
  exact foldl_markFresh_boundedSoundFromSome nodes ([], visited) sound
    (by simp) node (by simpa [markFreshList] using hnode)

theorem exploreFastAux_boundedSound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {starts : List Port} :
    ∀ (fuel : Nat) (stack : List Node) (visited : Array Bool)
      (found : List Node),
      (∀ node ∈ stack,
        BoundedSoundFromSome indexGrid width height starts node) →
      (∀ node ∈ found,
        BoundedSoundFromSome indexGrid width height starts node) →
      ∀ node ∈ exploreFastAux indexGrid width height fuel
        stack visited found,
        BoundedSoundFromSome indexGrid width height starts node := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack visited found _ hfound node hnode
      exact hfound node (by simpa [exploreFastAux] using hnode)
  | succ fuel ih =>
      intro stack visited found hstack hfound node hnode
      cases stack with
      | nil => exact hfound node (by simpa [exploreFastAux] using hnode)
      | cons first rest =>
          rw [exploreFastAux] at hnode
          let marked := markFreshList width visited
            (nextNodes indexGrid width height first)
          apply ih (marked.1 ++ rest) marked.2 (first :: found)
          · intro candidate hcandidate
            rw [List.mem_append] at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · exact markFreshList_boundedSoundFromSome
                (nodes := nextNodes indexGrid width height first)
                (visited := visited)
                (fun next hnext => nextNodes_boundedSoundFromSome
                  (hstack first (by simp)) hnext)
                candidate hcandidate
            · exact hstack candidate (by simp [hcandidate])
          · intro candidate hcandidate
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hcandidate
            · exact hstack _ (by simp)
            · exact hfound candidate hcandidate
          · exact hnode

/-- Fast-search paths retain all intermediate search-box bounds. -/
theorem exploreFast_bounded_sound
    {indexGrid : Nat → Nat → Index} {width height fuel : Nat}
    {starts : List Port} {node : Node}
    (hstarts : ∀ port ∈ starts, PortInBounds port width height)
    (hnode : node ∈ exploreFast indexGrid width height fuel starts) :
    BoundedSoundFromSome indexGrid width height starts node := by
  unfold exploreFast at hnode
  let nodes : List Node := starts.map fun start =>
    { origin := start, current := start, parity := false, reverseMoves := [] }
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshList width emptyVisited nodes
  apply exploreFastAux_boundedSound fuel marked.1 marked.2 []
  · exact markFreshList_boundedSoundFromSome
      (nodes := nodes) (visited := emptyVisited) (by
        intro initial hinitial
        rcases List.mem_map.1 hinitial with ⟨start, hstart, rfl⟩
        exact ⟨hstart, BoundedPath.refl start (hstarts start hstart)⟩)
  · simp
  · exact hnode

end RedShadeGraphSearchSoundness
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
