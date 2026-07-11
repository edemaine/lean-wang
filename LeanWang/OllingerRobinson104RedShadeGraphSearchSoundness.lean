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

end RedShadeGraphSearchSoundness
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
