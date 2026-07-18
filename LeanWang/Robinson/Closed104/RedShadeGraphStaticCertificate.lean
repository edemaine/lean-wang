/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphBoundedPath
import LeanWang.Robinson.Closed104.RedShadeGraphCertificate

/-!
# Static red-graph path certificates

A certificate is a predecessor forest. Roots select one of the supplied
source ports; every other instruction names an earlier instruction and one
checked graph move. The evaluator therefore validates a complete bounded path
without running graph search.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphStaticCertificate

open RedShadeGraph RedShadeGraphBoundedPath RedShadeGraphCertificate

structure State where
  origin : Port
  current : Port
  parity : Bool
deriving DecidableEq, Repr

inductive Instruction where
  | root (source : Nat)
  | step (previous : Nat) (move : Move)
deriving DecidableEq, Repr

def inBounds (port : Port) (width height : Nat) : Bool :=
  port.x < width && port.y < height

def evaluate (indexGrid : Nat → Nat → Index) (width height : Nat)
    (sources : List Port) (instructions : List Instruction) :
    (index : Nat) → Option State
  | index =>
      match instructions[index]? with
      | none => none
      | some (.root sourceIndex) =>
          match sources[sourceIndex]? with
          | none => none
          | some source =>
              if inBounds source width height then
                some ⟨source, source, false⟩
              else none
      | some (.step previous move) =>
          if previous < index then
            match evaluate indexGrid width height sources instructions previous with
            | none => none
            | some state =>
                if move.first = state.current &&
                    move.valid indexGrid && inBounds move.second width height then
                  some ⟨state.origin, move.second,
                    Bool.xor state.parity move.parity⟩
                else none
          else none
termination_by index => index

theorem boundedPath_of_evaluate
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction}
    {index : Nat} {state : State}
    (evaluated : evaluate indexGrid width height sources instructions index =
      some state) :
    BoundedPath indexGrid width height
      state.origin state.current state.parity := by
  induction index using Nat.strong_induction_on generalizing state with
  | h index ih =>
      cases instructionEq : instructions[index]? with
      | none => simp [evaluate, instructionEq] at evaluated
      | some instruction =>
          cases instruction with
          | root sourceIndex =>
              cases sourceEq : sources[sourceIndex]? with
              | none => simp [evaluate, instructionEq, sourceEq] at evaluated
              | some source =>
                  by_cases bounded : inBounds source width height = true
                  · simp [evaluate, instructionEq, sourceEq, bounded] at evaluated
                    subst state
                    apply BoundedPath.refl
                    simpa [PortInBounds, inBounds, Bool.and_eq_true] using bounded
                  · simp [evaluate, instructionEq, sourceEq, bounded] at evaluated
          | step previous move =>
              by_cases previousLt : previous < index
              · cases previousEvaluated :
                    evaluate indexGrid width height sources instructions previous with
                | none =>
                    simp [evaluate, instructionEq, previousLt,
                      previousEvaluated] at evaluated
                | some previousState =>
                    by_cases valid :
                        (move.first = previousState.current &&
                          move.valid indexGrid &&
                          inBounds move.second width height) = true
                    · simp [evaluate, instructionEq, previousLt,
                        previousEvaluated, valid] at evaluated
                      subst state
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
                      have previousPath :=
                        ih previous previousLt previousEvaluated
                      have link := move.link_of_valid valid.1.2
                      rw [valid.1.1] at link
                      have nextBounds :
                          PortInBounds move.second width height := by
                        simpa [PortInBounds, inBounds, Bool.and_eq_true]
                          using valid.2
                      exact BoundedPath.trans previousPath
                        (BoundedPath.ofLink link previousPath.second_inBounds
                          nextBounds)
                    · simp [evaluate, instructionEq, previousLt,
                        previousEvaluated, valid] at evaluated
              · simp [evaluate, instructionEq, previousLt] at evaluated

theorem origin_mem_sources_of_evaluate
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction}
    {index : Nat} {state : State}
    (evaluated : evaluate indexGrid width height sources instructions index =
      some state) :
    state.origin ∈ sources := by
  induction index using Nat.strong_induction_on generalizing state with
  | h index ih =>
      cases instructionEq : instructions[index]? with
      | none => simp [evaluate, instructionEq] at evaluated
      | some instruction =>
          cases instruction with
          | root sourceIndex =>
              cases sourceEq : sources[sourceIndex]? with
              | none => simp [evaluate, instructionEq, sourceEq] at evaluated
              | some source =>
                  by_cases bounded : inBounds source width height = true
                  · simp [evaluate, instructionEq, sourceEq, bounded] at evaluated
                    subst state
                    exact List.mem_of_getElem? sourceEq
                  · simp [evaluate, instructionEq, sourceEq, bounded] at evaluated
          | step previous move =>
              by_cases previousLt : previous < index
              · cases previousEvaluated :
                    evaluate indexGrid width height sources instructions previous with
                | none =>
                    simp [evaluate, instructionEq, previousLt,
                      previousEvaluated] at evaluated
                | some previousState =>
                    by_cases valid :
                        (move.first = previousState.current &&
                          move.valid indexGrid &&
                          inBounds move.second width height) = true
                    · simp [evaluate, instructionEq, previousLt,
                        previousEvaluated, valid] at evaluated
                      subst state
                      exact ih previous previousLt
                        (state := previousState) previousEvaluated
                    · simp [evaluate, instructionEq, previousLt,
                        previousEvaluated, valid] at evaluated
              · simp [evaluate, instructionEq, previousLt] at evaluated

def evaluated (indexGrid : Nat → Nat → Index) (width height : Nat)
    (sources : List Port) (instructions : List Instruction) :
    List (Nat × State) :=
  (List.range instructions.length).filterMap fun index =>
    (evaluate indexGrid width height sources instructions index).map
      (fun state => (index, state))

theorem evaluate_of_mem_evaluated
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction}
    {index : Nat} {state : State}
    (member : (index, state) ∈
      evaluated indexGrid width height sources instructions) :
    evaluate indexGrid width height sources instructions index = some state := by
  unfold evaluated at member
  rw [List.mem_filterMap] at member
  rcases member with ⟨candidateIndex, _, candidate⟩
  cases candidateEq :
      evaluate indexGrid width height sources instructions candidateIndex with
  | none => simp [candidateEq] at candidate
  | some candidateState =>
      simp [candidateEq] at candidate
      rcases candidate with ⟨rfl, rfl⟩
      exact candidateEq

def route? (indexGrid : Nat → Nat → Index) (width height : Nat)
    (sources : List Port) (instructions : List Instruction)
    (accept : State → Bool) : Option (Nat × State) :=
  (List.range instructions.length).findSome? fun index =>
    (evaluate indexGrid width height sources instructions index).bind fun state =>
      if accept state then some (index, state) else none

theorem evaluate_eq_of_route?
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction}
    {accept : State → Bool} {index : Nat} {state : State}
    (found : route? indexGrid width height sources instructions accept =
      some (index, state)) :
    evaluate indexGrid width height sources instructions index = some state := by
  unfold route? at found
  rw [List.findSome?_eq_some_iff] at found
  rcases found with ⟨_, candidateIndex, _, _, candidateFound, _⟩
  cases candidateEq :
      evaluate indexGrid width height sources instructions candidateIndex with
  | none => simp [candidateEq] at candidateFound
  | some candidate =>
      by_cases accepted : accept candidate = true
      · simp [candidateEq, accepted] at candidateFound
        rcases candidateFound with ⟨rfl, rfl⟩
        exact candidateEq
      · simp [candidateEq, accepted] at candidateFound

theorem accept_of_route?
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction}
    {accept : State → Bool} {index : Nat} {state : State}
    (found : route? indexGrid width height sources instructions accept =
      some (index, state)) :
    accept state = true := by
  unfold route? at found
  rw [List.findSome?_eq_some_iff] at found
  rcases found with ⟨_, candidateIndex, _, _, candidateFound, _⟩
  cases candidateEq :
      evaluate indexGrid width height sources instructions candidateIndex with
  | none => simp [candidateEq] at candidateFound
  | some candidate =>
      by_cases accepted : accept candidate = true
      · simp [candidateEq, accepted] at candidateFound
        rcases candidateFound with ⟨rfl, rfl⟩
        exact accepted
      · simp [candidateEq, accepted] at candidateFound

theorem boundedPath_of_route?
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction}
    {accept : State → Bool} {index : Nat} {state : State}
    (found : route? indexGrid width height sources instructions accept =
      some (index, state)) :
    BoundedPath indexGrid width height
      state.origin state.current state.parity := by
  exact boundedPath_of_evaluate (evaluate_eq_of_route? found)

end RedShadeGraphStaticCertificate
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
