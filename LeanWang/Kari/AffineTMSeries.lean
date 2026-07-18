/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.AffineTMStacks
import Mathlib.Analysis.Real.OfDigits

/-!
# Canonical real encodings of arbitrary one-sided tapes

The converse to `AffineTMStacks` embeds an arbitrary infinite one-sided tape
as a real radix expansion.  Mathlib's `Real.ofDigits` supplies convergence and
the sharp `[0,1]` bound.  Multiplying that fractional expansion by the radix
places the visible even symbol in its separated unit interval and makes tail
removal exactly Kari's affine `pop` operation.
-/

namespace LeanWang
namespace Kari
namespace AffineTM

open Hooper.FiniteTM0

noncomputable section

variable {numSymbols : Nat}

/-- A tape symbol, viewed as its even digit in the side-stack radix. -/
def sideDigit (a : Symbol numSymbols) : Fin (sideBase numSymbols) :=
  ⟨2 * a.val, by simp [sideBase]; omega⟩

@[simp]
theorem sideDigit_val (a : Symbol numSymbols) :
    (sideDigit a).val = 2 * a.val :=
  rfl

/-- Drop the visible symbol of a one-sided word. -/
def wordTail (word : Nat → Symbol numSymbols) : Nat → Symbol numSymbols :=
  fun n => word (n + 1)

/-- Canonical radix value of an infinite one-sided tape, with its visible
symbol at weight one. -/
def stackValue (word : Nat → Symbol numSymbols) : ℝ :=
  sideBase numSymbols *
    Real.ofDigits (fun n => sideDigit (word n))

/-- Splitting the first digit writes the stack value as its visible even code
plus the fractional expansion of its tail. -/
theorem stackValue_eq_head_add_tail (word : Nat → Symbol numSymbols) :
    stackValue word =
      (symbolValue (word 0) : ℝ) +
        Real.ofDigits (fun n => sideDigit (word (n + 1))) := by
  have hbase : (sideBase numSymbols : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (sideBase_pos numSymbols))
  rw [stackValue, Real.ofDigits_eq_sum_add_ofDigits
    (fun n => sideDigit (word n)) 1]
  simp only [Finset.sum_range_one, Real.ofDigitsTerm, zero_add,
    pow_one, inv_eq_one_div]
  simp only [symbolValue, sideDigit_val]
  push_cast
  field_simp

/-- Canonical stack values lie in the separated unit interval of their
visible symbol. -/
theorem stackValue_inSymbolInterval (word : Nat → Symbol numSymbols) :
    InSymbolInterval (word 0) (stackValue word) := by
  rw [stackValue_eq_head_add_tail]
  constructor
  · linarith [Real.ofDigits_nonneg
      (fun n => sideDigit (word (n + 1)))]
  · linarith [Real.ofDigits_le_one
      (fun n => sideDigit (word (n + 1)))]

/-- The canonical radix encoding commutes exactly with prepending the visible
symbol. -/
theorem stackValue_eq_push_head_tail (word : Nat → Symbol numSymbols) :
    stackValue word =
      LocalRule.push (word 0) (stackValue (wordTail word)) := by
  rw [stackValue_eq_head_add_tail]
  have hbase : (sideBase numSymbols : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (sideBase_pos numSymbols))
  simp only [LocalRule.push, stackValue, wordTail]
  field_simp

/-- Popping the certified visible symbol gives the canonical value of the
tail word. -/
theorem pop_stackValue (word : Nat → Symbol numSymbols) :
    LocalRule.pop (word 0) (stackValue word) =
      stackValue (wordTail word) := by
  rw [stackValue_eq_push_head_tail]
  exact pop_push (word 0) (stackValue (wordTail word))

/-- Prepend one symbol to a one-sided word. -/
def wordCons (a : Symbol numSymbols) (word : Nat → Symbol numSymbols) :
    Nat → Symbol numSymbols
  | 0 => a
  | n + 1 => word n

@[simp]
theorem wordCons_zero (a : Symbol numSymbols)
    (word : Nat → Symbol numSymbols) :
    wordCons a word 0 = a :=
  rfl

@[simp]
theorem wordCons_succ (a : Symbol numSymbols)
    (word : Nat → Symbol numSymbols) (n : Nat) :
    wordCons a word (n + 1) = word n :=
  rfl

/-- Canonical encoding turns word prepending into the affine push map. -/
theorem stackValue_wordCons (a : Symbol numSymbols)
    (word : Nat → Symbol numSymbols) :
    stackValue (wordCons a word) =
      LocalRule.push a (stackValue word) := by
  rw [stackValue_eq_push_head_tail]
  congr 1

/-- Symbols strictly to the left of a head-relative full tape, nearest first. -/
def leftWord (tape : Hooper.FullTM0.Tape (Symbol numSymbols)) :
    Nat → Symbol numSymbols :=
  fun n => tape (Int.negSucc n)

/-- Symbols strictly to the right of a head-relative full tape, nearest first. -/
def rightWord (tape : Hooper.FullTM0.Tape (Symbol numSymbols)) :
    Nat → Symbol numSymbols :=
  fun n => tape (Int.ofNat (n + 1))

/-- Moving left drops the old left neighbor from the left word. -/
theorem leftWord_moveLeft (tape : Hooper.FullTM0.Tape (Symbol numSymbols)) :
    leftWord (tape.move .left) = wordTail (leftWord tape) := by
  funext n
  change tape (Int.negSucc n - 1) = tape (Int.negSucc (n + 1))
  apply congrArg tape
  omega

/-- Moving left prepends the old scanned symbol to the right word. -/
theorem rightWord_moveLeft (tape : Hooper.FullTM0.Tape (Symbol numSymbols)) :
    rightWord (tape.move .left) = wordCons (tape 0) (rightWord tape) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      change tape (Int.ofNat (n + 1 + 1) - 1) = tape (Int.ofNat (n + 1))
      apply congrArg tape
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, Nat.cast_one]
      ring

/-- Moving right prepends the old scanned symbol to the left word. -/
theorem leftWord_moveRight (tape : Hooper.FullTM0.Tape (Symbol numSymbols)) :
    leftWord (tape.move .right) = wordCons (tape 0) (leftWord tape) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      change tape (Int.negSucc (n + 1) + 1) = tape (Int.negSucc n)
      apply congrArg tape
      omega

/-- Moving right drops the old right neighbor from the right word. -/
theorem rightWord_moveRight (tape : Hooper.FullTM0.Tape (Symbol numSymbols)) :
    rightWord (tape.move .right) = wordTail (rightWord tape) := by
  funext n
  change tape (Int.ofNat (n + 1) + 1) = tape (Int.ofNat (n + 1 + 1))
  apply congrArg tape
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, Nat.cast_one]

/-- Writing at the head does not change the left word. -/
theorem leftWord_write (tape : Hooper.FullTM0.Tape (Symbol numSymbols))
    (a : Symbol numSymbols) :
    leftWord (tape.write a) = leftWord tape := by
  funext n
  simp [leftWord, Hooper.FullTM0.Tape.write]

/-- Writing at the head does not change the right word. -/
theorem rightWord_write (tape : Hooper.FullTM0.Tape (Symbol numSymbols))
    (a : Symbol numSymbols) :
    rightWord (tape.write a) = rightWord tape := by
  funext n
  simp [rightWord, Hooper.FullTM0.Tape.write]
  omega

/-! ## Canonical affine states of full configurations -/

/-- Canonical real triple of an arbitrary full-tape configuration. -/
def encodeCfg (cfg : Hooper.FullTM0.Cfg (Symbol numSymbols) State) :
    Fin 3 → ℝ :=
  ![stackValue (leftWord cfg.tape),
    stackValue (rightWord cfg.tape),
    centerValue cfg.q cfg.tape.read]

/-- The fully specified local affine rule selected by a concrete machine
configuration and transition result. -/
def specFor (cfg : Hooper.FullTM0.Cfg (Symbol numSymbols) State)
    (target : State) (action : Action numSymbols) : LocalRule numSymbols where
  rule := Rule.mk cfg.q cfg.tape.read target action
  leftTop := leftWord cfg.tape 0
  rightTop := rightWord cfg.tape 0

/-- Every canonical full configuration lies in the input region of its
selected local rule. -/
theorem specFor_inInputRegion
    (cfg : Hooper.FullTM0.Cfg (Symbol numSymbols) State)
    (target : State) (action : Action numSymbols) :
    (specFor cfg target action).InInputRegion (encodeCfg cfg) := by
  refine ⟨?_, ?_, rfl⟩
  · exact stackValue_inSymbolInterval (leftWord cfg.tape)
  · exact stackValue_inSymbolInterval (rightWord cfg.tape)

/-- Canonical real triples commute exactly with every explicit finite-TM0
action. -/
theorem encodeCfg_action
    (cfg : Hooper.FullTM0.Cfg (Symbol numSymbols) State)
    (target : State) (action : Action numSymbols) :
    let nextTape := match action with
      | .write a => cfg.tape.write a
      | .moveLeft => cfg.tape.move .left
      | .moveRight => cfg.tape.move .right
    encodeCfg ⟨target, nextTape⟩ =
      (specFor cfg target action).realStep (encodeCfg cfg) := by
  dsimp only
  cases action with
  | write written =>
      funext j
      fin_cases j
      · change stackValue (leftWord (cfg.tape.write written)) =
          stackValue (leftWord cfg.tape)
        rw [leftWord_write]
      · change stackValue (rightWord (cfg.tape.write written)) =
          stackValue (rightWord cfg.tape)
        rw [rightWord_write]
      · rfl
  | moveLeft =>
      funext j
      fin_cases j
      · change stackValue (leftWord (cfg.tape.move .left)) =
          LocalRule.pop (leftWord cfg.tape 0)
            (stackValue (leftWord cfg.tape))
        rw [leftWord_moveLeft]
        exact (pop_stackValue (leftWord cfg.tape)).symm
      · change stackValue (rightWord (cfg.tape.move .left)) =
          LocalRule.push (cfg.tape 0)
            (stackValue (rightWord cfg.tape))
        rw [rightWord_moveLeft, stackValue_wordCons]
      · rfl
  | moveRight =>
      funext j
      fin_cases j
      · change stackValue (leftWord (cfg.tape.move .right)) =
          LocalRule.push (cfg.tape 0)
            (stackValue (leftWord cfg.tape))
        rw [leftWord_moveRight, stackValue_wordCons]
      · change stackValue (rightWord (cfg.tape.move .right)) =
          LocalRule.pop (rightWord cfg.tape 0)
            (stackValue (rightWord cfg.tape))
        rw [rightWord_moveRight]
        exact (pop_stackValue (rightWord cfg.tape)).symm
      · rfl

/-- The canonical target configuration lies in the finite output region
advertised by its selected local branch. -/
theorem specFor_action_inOutputRegion
    (cfg : Hooper.FullTM0.Cfg (Symbol numSymbols) State)
    (target : State) (action : Action numSymbols) :
    let nextTape := match action with
      | .write a => cfg.tape.write a
      | .moveLeft => cfg.tape.move .left
      | .moveRight => cfg.tape.move .right
    (specFor cfg target action).InOutputRegion
      (encodeCfg ⟨target, nextTape⟩) := by
  dsimp only
  cases action with
  | write written =>
      simp only [LocalRule.InOutputRegion, specFor, LocalRule.action,
        encodeCfg, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]
      refine ⟨?_, ?_, rfl⟩
      · rw [leftWord_write]
        exact stackValue_inSymbolInterval (leftWord cfg.tape)
      · rw [rightWord_write]
        exact stackValue_inSymbolInterval (rightWord cfg.tape)
  | moveLeft =>
      simp only [LocalRule.InOutputRegion, specFor, LocalRule.action,
        encodeCfg, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]
      let exposed := leftWord (cfg.tape.move .left) 0
      refine ⟨exposed, ?_, ?_, rfl⟩
      · exact stackValue_inSymbolInterval
          (leftWord (cfg.tape.move .left))
      · rw [rightWord_moveLeft]
        exact stackValue_inSymbolInterval
          (wordCons (cfg.tape 0) (rightWord cfg.tape))
  | moveRight =>
      simp only [LocalRule.InOutputRegion, specFor, LocalRule.action,
        encodeCfg, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]
      let exposed := rightWord (cfg.tape.move .right) 0
      refine ⟨exposed, ?_, ?_, rfl⟩
      · rw [leftWord_moveRight]
        exact stackValue_inSymbolInterval
          (wordCons (cfg.tape 0) (leftWord cfg.tape))
      · exact stackValue_inSymbolInterval
          (rightWord (cfg.tape.move .right))
end

end AffineTM
end Kari
end LeanWang
