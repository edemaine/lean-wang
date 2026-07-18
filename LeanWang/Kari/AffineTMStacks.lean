/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.AffineTMEncoding
import LeanWang.Kari.Hooper.FullTM0

/-!
# Decoding affine side stacks

An immortal affine itinerary need not start at a Cantor-series encoding of a
pre-existing tape.  Nevertheless it determines an actual full tape.  At every
valid stack coordinate the separated input intervals identify the visible
symbol uniquely; recursively popping that symbol decodes the rest of the
one-sided tape.  The exact push/pop formulas then make this decoder commute
with both head moves.

This observation supplies the soundness direction missing from a bare
piecewise-affine simulation: even noncanonical real points cannot create a
spurious immortal machine itinerary.
-/

namespace LeanWang
namespace Kari
namespace AffineTM

open Hooper
open Hooper.FiniteTM0

noncomputable section

variable {numSymbols : Nat}

/-- Select the unique visible symbol when `x` lies in one of the separated
symbol intervals, and use `fallback` only for an invalid coordinate. -/
def topSymbol (fallback : Symbol numSymbols) (x : ℝ) : Symbol numSymbols :=
  by
    classical
    exact if h : ∃ a : Symbol numSymbols, InSymbolInterval a x then
      Classical.choose h
    else fallback

/-- On a valid coordinate, `topSymbol` returns the interval's symbol. -/
theorem topSymbol_eq_of_interval (fallback a : Symbol numSymbols) (x : ℝ)
    (hx : InSymbolInterval a x) :
    topSymbol fallback x = a := by
  classical
  unfold topSymbol
  split
  · rename_i h
    exact eq_of_inSymbolInterval (Classical.choose_spec h) hx
  · rename_i h
    exact False.elim (h ⟨a, hx⟩)

/-- Remove the selected visible symbol from a real side-stack coordinate. -/
def tailValue (fallback : Symbol numSymbols) (x : ℝ) : ℝ :=
  LocalRule.pop (topSymbol fallback x) x

/-- Recursively decode a real side stack from its visible end. -/
def decodeStack (fallback : Symbol numSymbols) (x : ℝ) : Nat → Symbol numSymbols
  | 0 => topSymbol fallback x
  | n + 1 => decodeStack fallback (tailValue fallback x) n

@[simp]
theorem decodeStack_zero (fallback : Symbol numSymbols) (x : ℝ) :
    decodeStack fallback x 0 = topSymbol fallback x :=
  rfl

@[simp]
theorem decodeStack_succ (fallback : Symbol numSymbols) (x : ℝ) (n : Nat) :
    decodeStack fallback x (n + 1) =
      decodeStack fallback (tailValue fallback x) n :=
  rfl

/-- Pop cancels a push exactly. -/
@[simp]
theorem pop_push (a : Symbol numSymbols) (x : ℝ) :
    LocalRule.pop a (LocalRule.push a x) = x := by
  have hbase : (sideBase numSymbols : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (sideBase_pos numSymbols))
  simp only [LocalRule.pop, LocalRule.push]
  field_simp
  ring

/-- The decoder exposes the certified top symbol. -/
theorem decodeStack_zero_eq_of_interval
    (fallback a : Symbol numSymbols) (x : ℝ)
    (hx : InSymbolInterval a x) :
    decodeStack fallback x 0 = a := by
  simp [topSymbol_eq_of_interval fallback a x hx]

/-- Decoding after the visible symbol is the same as decoding the popped
coordinate. -/
theorem decodeStack_succ_eq_pop
    (fallback a : Symbol numSymbols) (x : ℝ)
    (hx : InSymbolInterval a x) (n : Nat) :
    decodeStack fallback x (n + 1) =
      decodeStack fallback (LocalRule.pop a x) n := by
  simp [tailValue, topSymbol_eq_of_interval fallback a x hx]

/-- Pushing onto a valid stack prepends precisely that symbol to its decoded
one-sided word. -/
theorem decodeStack_push
    (fallback a b : Symbol numSymbols) (x : ℝ)
    (hx : InSymbolInterval b x) :
    decodeStack fallback (LocalRule.push a x) =
      fun
      | 0 => a
      | n + 1 => decodeStack fallback x n := by
  funext n
  cases n with
  | zero =>
      exact decodeStack_zero_eq_of_interval fallback a _
        (inSymbolInterval_push a b x hx)
  | succ n =>
      rw [decodeStack_succ_eq_pop fallback a _
        (inSymbolInterval_push a b x hx)]
      simp

/-- Interpret the two decoded real stacks as an unrestricted head-relative
tape.  Negative coordinates read the left stack and positive coordinates read
the right stack. -/
def realTape (fallback : Symbol numSymbols) (spec : LocalRule numSymbols)
    (v : Fin 3 → ℝ) : FullTM0.Tape (Symbol numSymbols)
  | .ofNat 0 => spec.read
  | .ofNat (n + 1) => decodeStack fallback (v 1) n
  | .negSucc n => decodeStack fallback (v 0) n

@[simp]
theorem realTape_zero (fallback : Symbol numSymbols)
    (spec : LocalRule numSymbols) (v : Fin 3 → ℝ) :
    realTape fallback spec v 0 = spec.read :=
  rfl

@[simp]
theorem realTape_pos (fallback : Symbol numSymbols)
    (spec : LocalRule numSymbols) (v : Fin 3 → ℝ) (n : Nat) :
    realTape fallback spec v (Int.ofNat (n + 1)) =
      decodeStack fallback (v 1) n :=
  rfl

@[simp]
theorem realTape_neg (fallback : Symbol numSymbols)
    (spec : LocalRule numSymbols) (v : Fin 3 → ℝ) (n : Nat) :
    realTape fallback spec v (Int.negSucc n) =
      decodeStack fallback (v 0) n :=
  rfl

/-- Full machine configuration decoded from one local affine state. -/
def realCfg (fallback : Symbol numSymbols) (spec : LocalRule numSymbols)
    (v : Fin 3 → ℝ) : FullTM0.Cfg (Symbol numSymbols) State :=
  ⟨spec.source, realTape fallback spec v⟩

@[simp]
theorem realCfg_state (fallback : Symbol numSymbols)
    (spec : LocalRule numSymbols) (v : Fin 3 → ℝ) :
    (realCfg fallback spec v).q = spec.source :=
  rfl

@[simp]
theorem realCfg_read (fallback : Symbol numSymbols)
    (spec : LocalRule numSymbols) (v : Fin 3 → ℝ) :
    (realCfg fallback spec v).tape.read = spec.read :=
  rfl

/-! ## Commutation with machine actions -/

/-- Decoding commutes with a write action. -/
theorem realTape_write (fallback : Symbol numSymbols)
    (spec next : LocalRule numSymbols) (input output : Fin 3 → ℝ)
    (written : Symbol numSymbols) (haction : spec.action = .write written)
    (hinput : spec.InInputRegion input)
    (houtput : next.InInputRegion output)
    (hstep : output = spec.realStep input) :
    (realTape fallback spec input).write written =
      realTape fallback next output := by
  have hfollows := spec.follows_of_regions_realStep next input output
    hinput houtput hstep
  simp only [LocalRule.Follows, haction] at hfollows
  rcases hfollows with ⟨_hstate, hread, hleft, hright⟩
  have houtLeft : output 0 = input 0 := by
    simpa [LocalRule.realStep, haction] using congrFun hstep (0 : Fin 3)
  have houtRight : output 1 = input 1 := by
    simpa [LocalRule.realStep, haction] using congrFun hstep (1 : Fin 3)
  funext i
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          simp [FullTM0.Tape.write, realTape, hread]
      | succ n =>
          simp [FullTM0.Tape.write, realTape, houtRight]
          omega
  | negSucc n =>
      simp [FullTM0.Tape.write, realTape, houtLeft]

/-- Decoding commutes with a left head move. -/
theorem realTape_moveLeft (fallback : Symbol numSymbols)
    (spec next : LocalRule numSymbols) (input output : Fin 3 → ℝ)
    (haction : spec.action = .moveLeft)
    (hinput : spec.InInputRegion input)
    (houtput : next.InInputRegion output)
    (hstep : output = spec.realStep input) :
    (realTape fallback spec input).move .left =
      realTape fallback next output := by
  have hfollows := spec.follows_of_regions_realStep next input output
    hinput houtput hstep
  simp only [LocalRule.Follows, haction] at hfollows
  rcases hfollows with ⟨_hstate, hread, hright⟩
  have houtLeft : output 0 = LocalRule.pop spec.leftTop (input 0) := by
    simpa [LocalRule.realStep, haction] using congrFun hstep (0 : Fin 3)
  have houtRight : output 1 = LocalRule.push spec.read (input 1) := by
    simpa [LocalRule.realStep, haction] using congrFun hstep (1 : Fin 3)
  have hpush := decodeStack_push fallback spec.read spec.rightTop (input 1)
    hinput.2.1
  funext i
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          change decodeStack fallback (input 0) 0 = next.read
          rw [decodeStack_zero_eq_of_interval fallback spec.leftTop
            (input 0) hinput.1, hread]
      | succ n =>
          cases n with
          | zero =>
              change spec.read = decodeStack fallback (output 1) 0
              rw [houtRight]
              exact (congrFun hpush 0).symm
          | succ n =>
              rw [FullTM0.Tape.move_left_apply]
              have hindex : (Int.ofNat (n + 1 + 1) - 1) =
                  Int.ofNat (n + 1) := by
                simp only [Int.ofNat_eq_natCast, Int.natCast_add,
                  Nat.cast_one]
                ring
              rw [hindex, realTape_pos, realTape_pos]
              rw [houtRight]
              exact (congrFun hpush (n + 1)).symm
  | negSucc n =>
      change decodeStack fallback (input 0) (n + 1) =
        decodeStack fallback (output 0) n
      rw [houtLeft]
      exact decodeStack_succ_eq_pop fallback spec.leftTop (input 0)
        hinput.1 n

/-- Decoding commutes with a right head move. -/
theorem realTape_moveRight (fallback : Symbol numSymbols)
    (spec next : LocalRule numSymbols) (input output : Fin 3 → ℝ)
    (haction : spec.action = .moveRight)
    (hinput : spec.InInputRegion input)
    (houtput : next.InInputRegion output)
    (hstep : output = spec.realStep input) :
    (realTape fallback spec input).move .right =
      realTape fallback next output := by
  have hfollows := spec.follows_of_regions_realStep next input output
    hinput houtput hstep
  simp only [LocalRule.Follows, haction] at hfollows
  rcases hfollows with ⟨_hstate, hread, hleft⟩
  have houtLeft : output 0 = LocalRule.push spec.read (input 0) := by
    simpa [LocalRule.realStep, haction] using congrFun hstep (0 : Fin 3)
  have houtRight : output 1 = LocalRule.pop spec.rightTop (input 1) := by
    simpa [LocalRule.realStep, haction] using congrFun hstep (1 : Fin 3)
  have hpush := decodeStack_push fallback spec.read spec.leftTop (input 0)
    hinput.1
  funext i
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          change decodeStack fallback (input 1) 0 = next.read
          rw [decodeStack_zero_eq_of_interval fallback spec.rightTop
            (input 1) hinput.2.1, hread]
      | succ n =>
          change decodeStack fallback (input 1) (n + 1) =
            decodeStack fallback (output 1) n
          rw [houtRight]
          exact decodeStack_succ_eq_pop fallback spec.rightTop (input 1)
            hinput.2.1 n
  | negSucc n =>
      cases n with
      | zero =>
          change spec.read = decodeStack fallback (output 0) 0
          rw [houtLeft]
          exact (congrFun hpush 0).symm
      | succ n =>
          rw [FullTM0.Tape.move_right_apply]
          have hindex : Int.negSucc (n + 1) + 1 = Int.negSucc n := by
            omega
          rw [hindex, realTape_neg, realTape_neg]
          rw [houtLeft]
          exact (congrFun hpush (n + 1)).symm

/-! ## Exact full-machine semantics -/

/-- One admissible affine local step decodes to exactly one step of the
finite-table machine on an unrestricted tape. -/
theorem step_realCfg {table : Table numSymbols}
    (hdeterministic : Deterministic table)
    (fallback : Symbol numSymbols)
    (spec next : LocalRule numSymbols) (hrule : spec.rule ∈ table)
    (input output : Fin 3 → ℝ)
    (hinput : spec.InInputRegion input)
    (houtput : next.InInputRegion output)
    (hrealizes : AffineBeatty.Realizes spec.branch input output) :
    FullTM0.step (FiniteTM0.machine table) (realCfg fallback spec input) =
      some (realCfg fallback next output) := by
  have hmachine : FiniteTM0.machine table spec.source spec.read =
      some (spec.target, spec.action.toStmt) := by
    apply (machine_eq_some_iff_of_deterministic hdeterministic).2
    change spec.rule ∈ table
    exact hrule
  have hstep : output = spec.realStep input :=
    spec.eq_realStep_of_realizes input output hrealizes
  have hfollows := spec.follows_of_regions_realStep next input output
    hinput houtput hstep
  have hstate : spec.target = next.source :=
    LocalRule.target_eq_source_of_follows hfollows
  cases haction : spec.action with
  | write written =>
      have htape := realTape_write fallback spec next input output written
        haction hinput houtput hstep
      rw [haction] at hmachine
      unfold FullTM0.step
      rw [realCfg_state, realCfg_read, hmachine]
      simp only [Option.map_some, Action.toStmt_write]
      simp only [realCfg]
      rw [hstate, htape]
  | moveLeft =>
      have htape := realTape_moveLeft fallback spec next input output
        haction hinput houtput hstep
      rw [haction] at hmachine
      unfold FullTM0.step
      rw [realCfg_state, realCfg_read, hmachine]
      simp only [Option.map_some, Action.toStmt_moveLeft]
      simp only [realCfg]
      rw [hstate, htape]
  | moveRight =>
      have htape := realTape_moveRight fallback spec next input output
        haction hinput houtput hstep
      rw [haction] at hmachine
      unfold FullTM0.step
      rw [realCfg_state, realCfg_read, hmachine]
      simp only [Option.map_some, Action.toStmt_moveRight]
      simp only [realCfg]
      rw [hstate, htape]

end

end AffineTM
end Kari
end LeanWang
