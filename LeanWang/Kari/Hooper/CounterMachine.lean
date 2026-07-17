/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec

/-!
# A finite four-register counter machine

This file isolates the counter-program layer used by the sparse simulation in
Hooper's construction.  There are four named registers and two instructions:
increment-and-jump, and conditional-decrement-and-jump.  Control states are
natural numbers, but a program is an explicit finite association list.  Thus
states absent from the program's source list halt immediately, an important
fact when reasoning about arbitrary starting configurations.

Lookup selects the first instruction with the requested source state.  The
instruction and configuration types have primitive-recursive encodings, and
program lookup is primitive recursive (hence computable).
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterMachine

/-- The four registers used by the sparse simulator. -/
inductive Register where
  | left
  | right
  | temp
  | clock
  deriving DecidableEq

namespace Register

/-- Encode the four register names by two bits. -/
def equivCode : Register ≃ Bool × Bool where
  toFun
    | .left => (false, false)
    | .right => (false, true)
    | .temp => (true, false)
    | .clock => (true, true)
  invFun
    | (false, false) => .left
    | (false, true) => .right
    | (true, false) => .temp
    | (true, true) => .clock
  left_inv := by
    intro r
    cases r <;> rfl
  right_inv := by
    intro code
    rcases code with ⟨a, b⟩
    cases a <;> cases b <;> rfl

/-- The register index type is genuinely finite. -/
instance : Fintype Register where
  elems := {.left, .right, .temp, .clock}
  complete r := by
    cases r <;> simp

instance : Primcodable Register :=
  Primcodable.ofEquiv (Bool × Bool) equivCode

end Register

/-- Values of the four registers.  Using a structure rather than an
unbounded register file makes the finite storage interface explicit. -/
structure Registers where
  left : Nat
  right : Nat
  temp : Nat
  clock : Nat
  deriving DecidableEq

namespace Registers

/-- Primitive-recursive tuple code for register values. -/
def equivCode : Registers ≃ Nat × Nat × Nat × Nat where
  toFun r := (r.left, r.right, r.temp, r.clock)
  invFun r := ⟨r.1, r.2.1, r.2.2.1, r.2.2.2⟩
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro r
    rcases r with ⟨left, right, temp, clock⟩
    rfl

instance : Primcodable Registers :=
  Primcodable.ofEquiv (Nat × Nat × Nat × Nat) equivCode

/-- Read a named register. -/
def get (v : Registers) : Register → Nat
  | .left => v.left
  | .right => v.right
  | .temp => v.temp
  | .clock => v.clock

/-- Replace one named register. -/
def set (v : Registers) : Register → Nat → Registers
  | .left, n => { v with left := n }
  | .right, n => { v with right := n }
  | .temp, n => { v with temp := n }
  | .clock, n => { v with clock := n }

/-- Increment one named register. -/
def increment (v : Registers) (r : Register) : Registers :=
  v.set r (v.get r + 1)

/-- Decrement one named register, saturating at zero.  The machine invokes
this operation only on the nonzero branch of a conditional decrement. -/
def decrement (v : Registers) (r : Register) : Registers :=
  v.set r (v.get r - 1)

/-- Sum of the four registers. -/
def total (v : Registers) : Nat :=
  v.left + v.right + v.temp + v.clock

@[simp]
theorem get_set_same (v : Registers) (r : Register) (n : Nat) :
    (v.set r n).get r = n := by
  cases r <;> rfl

@[simp]
theorem get_set_other (v : Registers) {r s : Register} (h : s ≠ r) (n : Nat) :
    (v.set r n).get s = v.get s := by
  cases r <;> cases s <;> simp_all [set, get]

@[simp]
theorem get_increment_same (v : Registers) (r : Register) :
    (v.increment r).get r = v.get r + 1 := by
  simp [increment]

theorem get_increment_other (v : Registers) {r s : Register} (h : s ≠ r) :
    (v.increment r).get s = v.get s := by
  simp [increment, get_set_other v h]

@[simp]
theorem get_decrement_same (v : Registers) (r : Register) :
    (v.decrement r).get r = v.get r - 1 := by
  simp [decrement]

theorem get_decrement_other (v : Registers) {r s : Register} (h : s ≠ r) :
    (v.decrement r).get s = v.get s := by
  simp [decrement, get_set_other v h]

/-- Incrementing any register increases their total by exactly one. -/
@[simp]
theorem total_increment (v : Registers) (r : Register) :
    (v.increment r).total = v.total + 1 := by
  cases r <;> simp [increment, set, get, total, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm]

/-- A successful decrement decreases the register total by exactly one. -/
theorem total_decrement_add_one (v : Registers) (r : Register)
    (h : 0 < v.get r) :
    (v.decrement r).total + 1 = v.total := by
  cases r <;> simp_all [decrement, set, get, total] <;> omega

/-- Saturating decrement never increases the total. -/
theorem total_decrement_le (v : Registers) (r : Register) :
    (v.decrement r).total ≤ v.total := by
  cases r <;> simp [decrement, set, get, total]

/-- On a zero register, saturating decrement does nothing. -/
theorem decrement_eq_self_of_get_eq_zero (v : Registers) (r : Register)
    (h : v.get r = 0) :
    v.decrement r = v := by
  cases r <;> cases v <;> simp_all [decrement, set, get]

end Registers

/-- Control states are natural numbers.  Only the finitely many states that
occur as sources in a program can take a step. -/
abbrev State := Nat

/-- Instructions for a deterministic register program. -/
inductive Instruction where
  /-- Increment `register` and continue at `next`. -/
  | increment (register : Register) (next : State)
  /-- If `register` is zero, continue at `ifZero`; otherwise decrement it and
  continue at `ifPositive`. -/
  | decrement (register : Register) (ifZero ifPositive : State)
  deriving DecidableEq

namespace Instruction

/-- Sum code distinguishing increment from conditional decrement. -/
def equivCode : Instruction ≃ Register × (State ⊕ State × State) where
  toFun
    | .increment r next => (r, Sum.inl next)
    | .decrement r ifZero ifPositive => (r, Sum.inr (ifZero, ifPositive))
  invFun
    | (r, Sum.inl next) => .increment r next
    | (r, Sum.inr (ifZero, ifPositive)) => .decrement r ifZero ifPositive
  left_inv := by
    intro instruction
    cases instruction <;> rfl
  right_inv := by
    intro code
    rcases code with ⟨r, next | targets⟩
    · rfl
    · rcases targets with ⟨ifZero, ifPositive⟩
      rfl

instance : Primcodable Instruction :=
  Primcodable.ofEquiv (Register × (State ⊕ State × State)) equivCode

end Instruction

/-- A rule pairs its source control state with its instruction. -/
abbrev Rule := State × Instruction

/-- A finite counter program.  If source states are duplicated, lookup uses
the first matching rule. -/
abbrev Program := List Rule

/-- Source states occurring in the explicit program. -/
def sourceStates (program : Program) : List State :=
  program.map Prod.fst

/-- Look up the first instruction for a control state. -/
def lookupInstruction : Program → State → Option Instruction
  | [], _ => none
  | (source, instruction) :: program, state =>
      if state = source then some instruction
      else lookupInstruction program state

@[simp]
theorem lookupInstruction_nil (state : State) :
    lookupInstruction [] state = none :=
  rfl

@[simp]
theorem lookupInstruction_cons_eq (state : State) (instruction : Instruction)
    (program : Program) :
    lookupInstruction ((state, instruction) :: program) state = some instruction := by
  simp [lookupInstruction]

theorem lookupInstruction_cons_ne {state source : State} (h : state ≠ source)
    (instruction : Instruction) (program : Program) :
    lookupInstruction ((source, instruction) :: program) state =
      lookupInstruction program state := by
  simp [lookupInstruction, h]

/-- Recursive lookup agrees with Mathlib's executable association-list
lookup. -/
theorem lookupInstruction_eq_listLookup (program : Program) (state : State) :
    lookupInstruction program state =
      @List.lookup State Instruction instBEqOfDecidableEq state program := by
  induction program with
  | nil => rfl
  | cons rule program ih =>
      rcases rule with ⟨source, instruction⟩
      by_cases h : state = source
      · subst source
        simp [lookupInstruction, List.lookup]
      · have hb :
            @BEq.beq State instBEqOfDecidableEq state source = false := by
          change decide (state = source) = false
          simp [h]
        simp only [lookupInstruction, if_neg h, List.lookup, hb, ih]

/-- A source state absent from the finite list has no instruction. -/
theorem lookupInstruction_eq_none_of_not_mem
    {program : Program} {state : State}
    (h : state ∉ sourceStates program) :
    lookupInstruction program state = none := by
  induction program with
  | nil => rfl
  | cons rule program ih =>
      rcases rule with ⟨source, instruction⟩
      have hne : state ≠ source := by
        intro heq
        apply h
        simp [sourceStates, heq]
      have htail : state ∉ sourceStates program := by
        intro hmem
        apply h
        exact List.mem_cons_of_mem source hmem
      simp [lookupInstruction, hne, ih htail]

/-- Program lookup is primitive recursive in the program and source state. -/
theorem lookupInstruction_primrec :
    Primrec fun input : Program × State =>
      lookupInstruction input.1 input.2 := by
  have hlookup : Primrec fun input : Program × State =>
      @List.lookup State Instruction instBEqOfDecidableEq input.2 input.1 :=
    Primrec.listLookup.comp Primrec.snd Primrec.fst
  exact hlookup.of_eq fun input => by
    symm
    exact lookupInstruction_eq_listLookup input.1 input.2

/-- Computability corollary for explicit program lookup. -/
theorem lookupInstruction_computable :
    Computable fun input : Program × State =>
      lookupInstruction input.1 input.2 :=
  lookupInstruction_primrec.to_comp

/-- Counter-machine configurations. -/
structure Cfg where
  state : State
  registers : Registers
  deriving DecidableEq

namespace Cfg

/-- Product code for counter-machine configurations. -/
def equivCode : Cfg ≃ State × Registers where
  toFun c := (c.state, c.registers)
  invFun c := ⟨c.1, c.2⟩
  left_inv := by
    intro c
    cases c
    rfl
  right_inv := by
    intro c
    rcases c with ⟨state, registers⟩
    rfl

instance : Primcodable Cfg :=
  Primcodable.ofEquiv (State × Registers) equivCode

end Cfg

/-- One partial step of an explicit counter program. -/
def step (program : Program) (cfg : Cfg) : Option Cfg :=
  match lookupInstruction program cfg.state with
  | none => none
  | some (.increment register next) =>
      some ⟨next, cfg.registers.increment register⟩
  | some (.decrement register ifZero ifPositive) =>
      if cfg.registers.get register = 0 then
        some ⟨ifZero, cfg.registers⟩
      else
        some ⟨ifPositive, cfg.registers.decrement register⟩

/-- Missing lookup is exactly immediate halting. -/
theorem step_eq_none_iff (program : Program) (cfg : Cfg) :
    step program cfg = none ↔
      lookupInstruction program cfg.state = none := by
  cases hlookup : lookupInstruction program cfg.state with
  | none => simp [step, hlookup]
  | some instruction =>
    cases instruction with
    | increment => simp [step, hlookup]
    | decrement register ifZero ifPositive =>
        by_cases hzero : cfg.registers.get register = 0 <;>
          simp [step, hlookup, hzero]

/-- An increment instruction has exactly its advertised effect. -/
theorem step_of_lookup_increment
    {program : Program} {cfg : Cfg} {register : Register} {next : State}
    (h : lookupInstruction program cfg.state =
      some (.increment register next)) :
    step program cfg = some ⟨next, cfg.registers.increment register⟩ := by
  simp [step, h]

/-- The zero branch of a conditional decrement preserves all registers. -/
theorem step_of_lookup_decrement_zero
    {program : Program} {cfg : Cfg} {register : Register}
    {ifZero ifPositive : State}
    (hlookup : lookupInstruction program cfg.state =
      some (.decrement register ifZero ifPositive))
    (hzero : cfg.registers.get register = 0) :
    step program cfg = some ⟨ifZero, cfg.registers⟩ := by
  simp [step, hlookup, hzero]

/-- The positive branch decrements exactly the tested register. -/
theorem step_of_lookup_decrement_positive
    {program : Program} {cfg : Cfg} {register : Register}
    {ifZero ifPositive : State}
    (hlookup : lookupInstruction program cfg.state =
      some (.decrement register ifZero ifPositive))
    (hpositive : 0 < cfg.registers.get register) :
    step program cfg =
      some ⟨ifPositive, cfg.registers.decrement register⟩ := by
  have hne : cfg.registers.get register ≠ 0 := Nat.ne_of_gt hpositive
  simp [step, hlookup, hne]

/-- Every state absent from the finite source-state list halts immediately,
for every possible register valuation. -/
theorem step_eq_none_of_state_not_mem
    {program : Program} {cfg : Cfg}
    (h : cfg.state ∉ sourceStates program) :
    step program cfg = none := by
  rw [step_eq_none_iff]
  exact lookupInstruction_eq_none_of_not_mem h

/-- An increment step increases the register total by one. -/
theorem total_of_step_increment
    {program : Program} {cfg nextCfg : Cfg}
    {register : Register} {next : State}
    (hlookup : lookupInstruction program cfg.state =
      some (.increment register next))
    (hstep : step program cfg = some nextCfg) :
    nextCfg.registers.total = cfg.registers.total + 1 := by
  rw [step_of_lookup_increment hlookup] at hstep
  cases Option.some.inj hstep
  exact Registers.total_increment cfg.registers register

/-- A positive decrement step decreases the register total by one. -/
theorem total_of_step_decrement_positive
    {program : Program} {cfg nextCfg : Cfg}
    {register : Register} {ifZero ifPositive : State}
    (hlookup : lookupInstruction program cfg.state =
      some (.decrement register ifZero ifPositive))
    (hpositive : 0 < cfg.registers.get register)
    (hstep : step program cfg = some nextCfg) :
    nextCfg.registers.total + 1 = cfg.registers.total := by
  rw [step_of_lookup_decrement_positive hlookup hpositive] at hstep
  cases Option.some.inj hstep
  exact Registers.total_decrement_add_one cfg.registers register hpositive

end CounterMachine
end Hooper
end Kari
end LeanWang
