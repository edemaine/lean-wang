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

def evaluateInstruction (indexGrid : Nat → Nat → Index) (width height : Nat)
    (sources : List Port) (states : Array (Option State)) :
    Instruction → Option State
  | .root sourceIndex =>
      match sources[sourceIndex]? with
      | none => none
      | some source =>
          if inBounds source width height then
            some ⟨source, source, false⟩
          else none
  | .step previous move =>
      match states[previous]? with
      | some (some state) =>
          if move.first = state.current &&
              move.valid indexGrid && inBounds move.second width height then
            some ⟨state.origin, move.second,
              Bool.xor state.parity move.parity⟩
          else none
      | _ => none

def evaluateInto (indexGrid : Nat → Nat → Index) (width height : Nat)
    (sources : List Port) :
    Array (Option State) → List Instruction → Array (Option State)
  | states, [] => states
  | states, instruction :: instructions =>
      evaluateInto indexGrid width height sources
        (states.push (evaluateInstruction indexGrid width height sources states
          instruction)) instructions

def evaluateAll (indexGrid : Nat → Nat → Index) (width height : Nat)
    (sources : List Port) (instructions : List Instruction) :
    Array (Option State) :=
  evaluateInto indexGrid width height sources #[] instructions

abbrev StateSound (indexGrid : Nat → Nat → Index) (width height : Nat)
    (sources : List Port) (state : State) : Prop :=
  state.origin ∈ sources ∧
    BoundedPath indexGrid width height
      state.origin state.current state.parity

abbrev StatesSound (indexGrid : Nat → Nat → Index) (width height : Nat)
    (sources : List Port) (states : Array (Option State)) : Prop :=
  ∀ (index : Nat) (state : State), states[index]? = some (some state) →
    StateSound indexGrid width height sources state

theorem evaluateInstruction_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {states : Array (Option State)}
    (statesSound : StatesSound indexGrid width height sources states)
    {instruction : Instruction} {state : State}
    (evaluated : evaluateInstruction indexGrid width height sources states
      instruction = some state) :
    StateSound indexGrid width height sources state := by
  cases instruction with
  | root sourceIndex =>
      cases sourceEq : sources[sourceIndex]? with
      | none => simp [evaluateInstruction, sourceEq] at evaluated
      | some source =>
          by_cases bounded : inBounds source width height = true
          · simp only [evaluateInstruction, sourceEq, bounded, ↓reduceIte,
              Option.some.injEq] at evaluated
            subst state
            refine ⟨List.mem_of_getElem? sourceEq,
              BoundedPath.refl (indexGrid := indexGrid) (width := width)
                (height := height) source ?_⟩
            simpa [PortInBounds, inBounds, Bool.and_eq_true] using bounded
          · simp [evaluateInstruction, sourceEq, bounded] at evaluated
  | step previous move =>
      cases previousEq : states[previous]? with
      | none => simp [evaluateInstruction, previousEq] at evaluated
      | some previousOption =>
          cases previousOption with
          | none => simp [evaluateInstruction, previousEq] at evaluated
          | some previousState =>
              by_cases valid :
                  (move.first = previousState.current &&
                    move.valid indexGrid &&
                    inBounds move.second width height) = true
              · simp only [evaluateInstruction, previousEq, valid, ↓reduceIte,
                  Option.some.injEq] at evaluated
                subst state
                rcases statesSound previous previousState previousEq with
                  ⟨sourceMem, previousPath⟩
                simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
                have link := move.link_of_valid valid.1.2
                rw [valid.1.1] at link
                have nextBounds :
                    PortInBounds move.second width height := by
                  simpa [PortInBounds, inBounds, Bool.and_eq_true]
                    using valid.2
                exact ⟨sourceMem, BoundedPath.trans previousPath
                  (BoundedPath.ofLink link previousPath.second_inBounds
                    nextBounds)⟩
              · simp [evaluateInstruction, previousEq, valid] at evaluated

theorem statesSound_push
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {states : Array (Option State)}
    (statesSound : StatesSound indexGrid width height sources states)
    {next : Option State}
    (nextSound : ∀ state, next = some state →
      StateSound indexGrid width height sources state) :
    StatesSound indexGrid width height sources (states.push next) := by
  intro index state evaluated
  rw [Array.getElem?_push] at evaluated
  split at evaluated
  · rename_i indexEq
    subst index
    simp only [Option.some.injEq] at evaluated
    exact nextSound state evaluated
  · exact statesSound index state evaluated

theorem evaluateInto_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {states : Array (Option State)}
    (statesSound : StatesSound indexGrid width height sources states)
    (instructions : List Instruction) :
    StatesSound indexGrid width height sources
      (evaluateInto indexGrid width height sources states instructions) := by
  induction instructions generalizing states with
  | nil => simpa [evaluateInto] using statesSound
  | cons instruction instructions ih =>
      simp only [evaluateInto]
      apply ih
      apply statesSound_push statesSound
      intro state evaluated
      exact evaluateInstruction_sound statesSound evaluated

theorem evaluateAll_sound
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction} :
    StatesSound indexGrid width height sources
      (evaluateAll indexGrid width height sources instructions) := by
  apply evaluateInto_sound
  intro index state evaluated
  simp at evaluated

def evaluated (indexGrid : Nat → Nat → Index) (width height : Nat)
    (sources : List Port) (instructions : List Instruction) :
    List (Nat × State) :=
  let states := evaluateAll indexGrid width height sources instructions
  (List.range states.size).filterMap fun index =>
    states[index]?.join.map fun state => (index, state)

theorem sound_of_mem_evaluated
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction}
    {index : Nat} {state : State}
    (member : (index, state) ∈
      evaluated indexGrid width height sources instructions) :
    StateSound indexGrid width height sources state := by
  unfold evaluated at member
  rw [List.mem_filterMap] at member
  rcases member with ⟨candidateIndex, _, candidate⟩
  cases candidateEq :
      (evaluateAll indexGrid width height sources instructions)[candidateIndex]? with
  | none => simp [candidateEq] at candidate
  | some candidateOption =>
      cases candidateOption with
      | none => simp [candidateEq] at candidate
      | some candidateState =>
          simp only [candidateEq, Option.join, Option.map] at candidate
          rcases candidate with ⟨rfl, rfl⟩
          exact evaluateAll_sound index state candidateEq

def route? (indexGrid : Nat → Nat → Index) (width height : Nat)
    (sources : List Port) (instructions : List Instruction)
    (accept : State → Bool) : Option (Nat × State) :=
  (evaluated indexGrid width height sources instructions).find? fun entry =>
    accept entry.2

theorem mem_evaluated_of_route?
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction}
    {accept : State → Bool} {index : Nat} {state : State}
    (found : route? indexGrid width height sources instructions accept =
      some (index, state)) :
    (index, state) ∈ evaluated indexGrid width height sources instructions := by
  unfold route? at found
  exact List.mem_of_find?_eq_some found

theorem accept_of_route?
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction}
    {accept : State → Bool} {index : Nat} {state : State}
    (found : route? indexGrid width height sources instructions accept =
      some (index, state)) :
    accept state = true := by
  unfold route? at found
  simpa using List.find?_some found

theorem boundedPath_of_route?
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {sources : List Port} {instructions : List Instruction}
    {accept : State → Bool} {index : Nat} {state : State}
    (found : route? indexGrid width height sources instructions accept =
      some (index, state)) :
    BoundedPath indexGrid width height
      state.origin state.current state.parity := by
  exact (sound_of_mem_evaluated (mem_evaluated_of_route? found)).2

end RedShadeGraphStaticCertificate
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
