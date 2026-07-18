/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.AffineBeatty
import LeanWang.Kari.AffineSystem
import LeanWang.Kari.Hooper.FiniteTM0
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Rational affine branches for finite TM0 rules

This module is the local machine-to-affine compiler in Kari's construction.
A full-tape configuration is represented by three real coordinates:

* the stack strictly left of the head;
* the stack strictly right of the head;
* a discrete tag containing the control state and scanned symbol.

Tape symbols occupy disjoint unit intervals.  If `a` is a symbol, its stack
interval is `[2a, 2a+1]`; the gaps between these intervals exclude malformed
top symbols.  A stack pop is multiplication by a fixed base, and a push is
division by that base followed by addition of the new symbol code.  Therefore
each explicit TM0 rule, after choosing the two currently visible side-stack
symbols, is one rational affine map on three coordinates.

The output alphabet of a moving branch ranges over the still-hidden symbol
exposed by the pop.  This is finite but deliberately nondeterministic: the
real affine equation determines which output interval can actually occur.
-/

namespace LeanWang
namespace Kari
namespace AffineTM

open Hooper
open Hooper.FiniteTM0

variable {numSymbols : Nat}

/-! ## Discrete stack and center codes -/

/-- The radix used for side stacks.  It lies strictly beyond every symbol
interval `[2a, 2a+1]`. -/
def sideBase (numSymbols : Nat) : Nat :=
  2 * numSymbols + 2

theorem sideBase_pos (numSymbols : Nat) : 0 < sideBase numSymbols := by
  simp [sideBase]

/-- Even integer code of one tape symbol. -/
def symbolValue (a : Symbol numSymbols) : Int :=
  2 * (a.val : Int)

/-- Exact third-coordinate tag containing the state and scanned symbol. -/
def centerValue (q : State) (a : Symbol numSymbols) : Int :=
  Nat.pair q a.val

/-- The two possible Beatty digits of a real in one closed unit interval. -/
def intervalDigits (z : Int) : List Int :=
  [z, z + 1]

/-- All componentwise Beatty digits compatible with two visible side symbols
and one exact center tag. -/
def digitBox (leftTop rightTop : Symbol numSymbols)
    (center : Int) : List IntVector3 :=
  (intervalDigits (symbolValue leftTop)).flatMap fun x =>
    (intervalDigits (symbolValue rightTop)).map fun y =>
      ⟨x, y, center⟩

@[simp]
theorem mem_intervalDigits (z x : Int) :
    x ∈ intervalDigits z ↔ x = z ∨ x = z + 1 := by
  simp [intervalDigits]

theorem mem_digitBox_iff
    (leftTop rightTop : Symbol numSymbols) (center : Int)
    (v : IntVector3) :
    v ∈ digitBox leftTop rightTop center ↔
      (v.x = symbolValue leftTop ∨ v.x = symbolValue leftTop + 1) ∧
      (v.y = symbolValue rightTop ∨ v.y = symbolValue rightTop + 1) ∧
      v.z = center := by
  rcases v with ⟨x, y, z⟩
  simp [digitBox, intervalDigits]
  tauto

/-! ## The affine action of one explicit rule -/

/-- A finite TM0 rule together with the symbols currently visible on the two
side stacks. -/
structure LocalRule (numSymbols : Nat) where
  rule : Rule numSymbols
  leftTop : Symbol numSymbols
  rightTop : Symbol numSymbols

namespace LocalRule

/-- Source state of the underlying TM0 rule. -/
def source (spec : LocalRule numSymbols) : State :=
  spec.rule.1.1

/-- Symbol scanned by the underlying TM0 rule. -/
def read (spec : LocalRule numSymbols) : Symbol numSymbols :=
  spec.rule.1.2

/-- Target state of the underlying TM0 rule. -/
def target (spec : LocalRule numSymbols) : State :=
  spec.rule.2.1

/-- Explicit action of the underlying TM0 rule. -/
def action (spec : LocalRule numSymbols) : Action numSymbols :=
  spec.rule.2.2

/-- Injective tag for a fully specified local rule. -/
def tag (spec : LocalRule numSymbols) : Nat :=
  Nat.pair (Encodable.encode spec.rule)
    (Nat.pair spec.leftTop.val spec.rightTop.val)

/-- Common denominator of the affine branch. -/
def denominator (spec : LocalRule numSymbols) : Nat :=
  match spec.action with
  | .write _ => 1
  | .moveLeft | .moveRight => sideBase numSymbols

theorem denominator_pos (spec : LocalRule numSymbols) :
    0 < spec.denominator := by
  cases haction : spec.action <;>
    simp [denominator, haction, sideBase_pos]

/-- Integer numerator matrix of the stack update. -/
def linearNumerator (spec : LocalRule numSymbols) : IntMatrix3 :=
  let B : Int := sideBase numSymbols
  match spec.action with
  | .write _ =>
      ⟨1, 0, 0, 0, 1, 0, 0, 0, 0⟩
  | .moveLeft =>
      ⟨B * B, 0, 0, 0, 1, 0, 0, 0, 0⟩
  | .moveRight =>
      ⟨1, 0, 0, 0, B * B, 0, 0, 0, 0⟩

/-- Integer numerator offset of the stack update. -/
def offsetNumerator (spec : LocalRule numSymbols) : IntVector3 :=
  let B : Int := sideBase numSymbols
  match spec.action with
  | .write written =>
      ⟨0, 0, centerValue spec.target written⟩
  | .moveLeft =>
      ⟨-(B * B * symbolValue spec.leftTop),
        B * symbolValue spec.read,
        B * centerValue spec.target spec.leftTop⟩
  | .moveRight =>
      ⟨B * symbolValue spec.read,
        -(B * B * symbolValue spec.rightTop),
        B * centerValue spec.target spec.rightTop⟩

/-- The rational affine branch implementing this local machine rule. -/
def branch (spec : LocalRule numSymbols) : IntegerAffineBranch where
  tag := spec.tag
  denominator := spec.denominator
  denominator_pos := spec.denominator_pos
  linearNumerator := spec.linearNumerator
  offsetNumerator := spec.offsetNumerator

/-- Input digit alphabet selecting the source state, scanned symbol, and two
visible side-stack symbols. -/
def inputs (spec : LocalRule numSymbols) : List IntVector3 :=
  digitBox spec.leftTop spec.rightTop
    (centerValue spec.source spec.read)

/-- Output digit alphabet.  A write preserves both visible side symbols.  A
move exposes one previously hidden symbol, so that side ranges over the whole
finite tape alphabet. -/
def outputs (spec : LocalRule numSymbols) : List IntVector3 :=
  match spec.action with
  | .write written =>
      digitBox spec.leftTop spec.rightTop
        (centerValue spec.target written)
  | .moveLeft =>
      (List.finRange numSymbols).flatMap fun newLeftTop =>
        digitBox newLeftTop spec.read
          (centerValue spec.target spec.leftTop)
  | .moveRight =>
      (List.finRange numSymbols).flatMap fun newRightTop =>
        digitBox spec.read newRightTop
          (centerValue spec.target spec.rightTop)

/-- Fully compiled transducer branch, with the uniform Beatty carry bound. -/
def compiled (spec : LocalRule numSymbols) : CompiledAffineBranch where
  branch := spec.branch
  inputs := spec.inputs
  outputs := spec.outputs
  carryBound := AffineBeatty.carryBound spec.branch

/-! ## Exact real semantics -/

noncomputable section

/-- Push a symbol onto a real side-stack coordinate. -/
def push (a : Symbol numSymbols) (x : ℝ) : ℝ :=
  symbolValue a + x / sideBase numSymbols

/-- Pop a known visible symbol from a real side-stack coordinate. -/
def pop (a : Symbol numSymbols) (x : ℝ) : ℝ :=
  sideBase numSymbols * (x - symbolValue a)

/-- The real configuration obtained after applying the specified local rule.
The third input coordinate is intentionally ignored: the branch has already
selected its exact source center tag. -/
def realStep (spec : LocalRule numSymbols) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  match spec.action with
  | .write written => ![v 0, v 1, centerValue spec.target written]
  | .moveLeft =>
      ![pop spec.leftTop (v 0),
        push spec.read (v 1),
        centerValue spec.target spec.leftTop]
  | .moveRight =>
      ![push spec.read (v 0),
        pop spec.rightTop (v 1),
        centerValue spec.target spec.rightTop]

/-- The integer-coded rational branch is exactly the intended push/pop
operation on real stack coordinates. -/
theorem realizes_realStep (spec : LocalRule numSymbols) (v : Fin 3 → ℝ) :
    AffineBeatty.Realizes spec.branch v (spec.realStep v) := by
  intro j
  cases haction : spec.action with
  | write written =>
      fin_cases j <;>
        simp [branch, denominator, linearNumerator, offsetNumerator,
          realStep, haction, AffineBeatty.mulReal, AffineBeatty.toReal]
  | moveLeft =>
      fin_cases j <;>
        simp [branch, denominator, linearNumerator, offsetNumerator,
          realStep, pop, push, haction, AffineBeatty.mulReal,
          AffineBeatty.toReal, sideBase] <;>
        field_simp <;> ring
  | moveRight =>
      fin_cases j <;>
        simp [branch, denominator, linearNumerator, offsetNumerator,
          realStep, pop, push, haction, AffineBeatty.mulReal,
          AffineBeatty.toReal, sideBase] <;>
        field_simp <;> ring

/-- The affine equation has a unique output, so any orbit step using this
branch is the intended push/pop machine update. -/
theorem eq_realStep_of_realizes (spec : LocalRule numSymbols)
    (input output : Fin 3 → ℝ)
    (hrealizes : AffineBeatty.Realizes spec.branch input output) :
    output = spec.realStep input := by
  funext j
  have hgiven := hrealizes j
  have hintended := spec.realizes_realStep input j
  have hden : (0 : ℝ) < spec.branch.denominator := by
    exact_mod_cast spec.branch.denominator_pos
  nlinarith

end

end LocalRule

end AffineTM
end Kari
end LeanWang
