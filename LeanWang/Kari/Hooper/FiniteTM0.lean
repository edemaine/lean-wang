/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Explicit finite rule tables for Post-Turing machines

`Turing.TM0.Machine` is a transition *function*.  This is convenient for
semantics, but Hooper's construction eventually has to inspect and compile a
finite transition table.  This file supplies such a representation.

Tape symbols are bounded natural numbers, while control states are `Nat` so a
compiler can allocate fresh states without changing its result type.  A rule
table is an association list from `(state, scanned symbol)` to `(next state, action)`;
lookup therefore selects the first matching rule.  `Deterministic` says that
the keys have no duplicates, and under that hypothesis table membership is
equivalent to a machine transition.

The action type has its own primitive-recursive code.  This lets us prove that
table lookup is primitive recursive without requiring a `Primcodable` instance
for Mathlib's semantic `Turing.TM0.Stmt` type.  The final `machine` merely maps
the explicitly coded action to the corresponding statement.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace FiniteTM0

open Turing

/-! ## Finite syntax and encodings -/

/-- A tape symbol is a natural number below the declared alphabet size. -/
abbrev Symbol (numSymbols : Nat) := Fin numSymbols

/-- Control states are natural numbers.  Only finitely many can occur as source
states in a finite rule table; every other state has no transition and halts.

Using `Nat` rather than `Fin numStates` is important for compilation: a
compiler may generate arbitrarily many fresh states while retaining the fixed,
nondependent codomain `Table numSymbols`.
-/
abbrev State := Nat

/-- Explicitly coded actions for a finite-alphabet Post-Turing machine. -/
inductive Action (numSymbols : Nat) where
  | moveLeft
  | moveRight
  | write (symbol : Symbol numSymbols)
  deriving DecidableEq

namespace Action

variable {numSymbols : Nat}

/-- A simple sum code for finite-machine actions. -/
def equivCode : Action numSymbols ≃ Bool ⊕ Symbol numSymbols where
  toFun
    | .moveLeft => Sum.inl false
    | .moveRight => Sum.inl true
    | .write a => Sum.inr a
  invFun
    | Sum.inl false => .moveLeft
    | Sum.inl true => .moveRight
    | Sum.inr a => .write a
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    intro code
    rcases code with b | a
    · cases b <;> rfl
    · rfl

instance : Primcodable (Action numSymbols) :=
  Primcodable.ofEquiv (Bool ⊕ Symbol numSymbols) equivCode

/-- Interpret an explicitly coded action as a Mathlib `TM0` statement. -/
def toStmt : Action numSymbols → Turing.TM0.Stmt (Symbol numSymbols)
  | .moveLeft => .move .left
  | .moveRight => .move .right
  | .write a => .write a

@[simp] theorem toStmt_moveLeft :
    (moveLeft : Action numSymbols).toStmt = .move .left := rfl

@[simp] theorem toStmt_moveRight :
    (moveRight : Action numSymbols).toStmt = .move .right := rfl

@[simp] theorem toStmt_write (a : Symbol numSymbols) :
    (write a).toStmt = .write a := rfl

theorem toStmt_injective :
    Function.Injective (toStmt : Action numSymbols → Turing.TM0.Stmt (Symbol numSymbols)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [toStmt]

end Action

/-- The input key of a finite transition rule. -/
abbrev Key (numSymbols : Nat) :=
  State × Symbol numSymbols

/-- The explicitly coded result of a finite transition rule. -/
abbrev Result (numSymbols : Nat) :=
  State × Action numSymbols

/-- A transition rule is represented directly as a key-result pair.

The tuple representation gives rule lists a canonical primitive-recursive
encoding and makes the executable lookup exactly `List.lookup`.
-/
abbrev Rule (numSymbols : Nat) :=
  Key numSymbols × Result numSymbols

/-- A finite Post-Turing program is a list of explicitly coded rules. -/
abbrev Table (numSymbols : Nat) :=
  List (Rule numSymbols)

namespace Rule

variable {numSymbols : Nat}

/-- Construct a rule from its four semantic fields. -/
def mk (source : State) (read : Symbol numSymbols)
    (target : State) (action : Action numSymbols) :
    Rule numSymbols :=
  ((source, read), (target, action))

@[simp] theorem mk_fst (source : State) (read : Symbol numSymbols)
    (target : State) (action : Action numSymbols) :
    (mk source read target action).1 = (source, read) := rfl

@[simp] theorem mk_snd (source : State) (read : Symbol numSymbols)
    (target : State) (action : Action numSymbols) :
    (mk source read target action).2 = (target, action) := rfl

end Rule

variable {numSymbols : Nat}

/-- Lookup in the explicit action table.  In a malformed table with duplicate
keys, the first matching rule wins. -/
def lookupAction : Table numSymbols →
    State → Symbol numSymbols →
    Option (Result numSymbols)
  | [], _, _ => none
  | (key, result) :: rules, q, a =>
      if (q, a) = key then some result else lookupAction rules q a

/-- The propositional recursive definition agrees with the executable
association-list lookup used by Mathlib's primitive-recursion library. -/
theorem lookupAction_eq_listLookup
    (rules : Table numSymbols)
    (q : State) (a : Symbol numSymbols) :
    lookupAction rules q a =
      @List.lookup (Key numSymbols)
        (Result numSymbols) instBEqOfDecidableEq (q, a) rules := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
      rcases rule with ⟨key, result⟩
      by_cases h : (q, a) = key
      · subst key
        simp [lookupAction, List.lookup]
      · have hb :
            @BEq.beq (Key numSymbols) instBEqOfDecidableEq
              (q, a) key = false := by
          change decide ((q, a) = key) = false
          simp [h]
        simp only [lookupAction, if_neg h, List.lookup, hb, ih]

/-! ## Determinism and machine semantics -/

/-- A table is deterministic when no two rules have the same source state and
scanned symbol. -/
def Deterministic (rules : Table numSymbols) : Prop :=
  (rules.map Prod.fst).Nodup

/-- The finite list of states from which the table has at least one rule. -/
def sourceStates (rules : Table numSymbols) : List State :=
  rules.map fun rule => rule.1.1

/-- Interpret an explicit rule table as Mathlib's semantic `TM0` machine. -/
def machine {numSymbols : Nat}
    (rules : Table numSymbols) :
    Turing.TM0.Machine (Symbol numSymbols) State :=
  fun q a => (lookupAction rules q a).map fun result =>
    (result.1, result.2.toStmt)

@[simp] theorem machine_apply {numSymbols : Nat}
    (rules : Table numSymbols) (q : State)
    (a : Symbol numSymbols) :
    machine rules q a =
      (lookupAction rules q a).map fun result =>
        (result.1, result.2.toStmt) :=
  rfl

@[simp] theorem lookupAction_nil (q : State) (a : Symbol numSymbols) :
    lookupAction ([] : Table numSymbols) q a = none :=
  rfl

@[simp] theorem lookupAction_cons_eq
    (q : State) (a : Symbol numSymbols)
    (target : State) (action : Action numSymbols)
    (rules : Table numSymbols) :
    lookupAction (Rule.mk q a target action :: rules) q a =
      some (target, action) := by
  simp [lookupAction, Rule.mk]

theorem lookupAction_cons_ne
    {q source : State} {a read : Symbol numSymbols}
    (h : (q, a) ≠ (source, read))
    (target : State) (action : Action numSymbols)
    (rules : Table numSymbols) :
    lookupAction (Rule.mk source read target action :: rules) q a =
      lookupAction rules q a := by
  simp [lookupAction, Rule.mk, h]

/-- A key absent from the finite table has no explicitly coded transition. -/
theorem lookupAction_eq_none_of_key_not_mem
    {rules : Table numSymbols} {q : State} {a : Symbol numSymbols}
    (h : (q, a) ∉ rules.map Prod.fst) :
    lookupAction rules q a = none := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
      rcases rule with ⟨key, result⟩
      have hne : (q, a) ≠ key := by
        intro heq
        apply h
        simp [heq]
      have htail : (q, a) ∉ rules.map Prod.fst := by
        intro hmem
        apply h
        exact List.mem_cons_of_mem key hmem
      simp [lookupAction, hne, ih htail]

/-- Every state absent from the finite source-state list halts immediately,
regardless of the scanned symbol.  This is the key arbitrary-configuration
property of the `Nat`-state representation. -/
theorem machine_eq_none_of_state_not_mem
    {rules : Table numSymbols} {q : State}
    (h : q ∉ sourceStates rules) (a : Symbol numSymbols) :
    machine rules q a = none := by
  have hkey : (q, a) ∉ rules.map Prod.fst := by
    intro hmem
    apply h
    rcases List.mem_map.mp hmem with ⟨rule, hrule, hkey⟩
    apply List.mem_map.mpr
    refine ⟨rule, hrule, ?_⟩
    exact congrArg Prod.fst hkey
  simp [machine, lookupAction_eq_none_of_key_not_mem hkey]

/-- A successful lookup always comes from a rule in the table, even without
the no-duplicate-keys hypothesis. -/
theorem rule_mem_of_lookupAction_eq_some
    {rules : Table numSymbols}
    {q : State} {a : Symbol numSymbols}
    {target : State} {action : Action numSymbols}
    (h : lookupAction rules q a = some (target, action)) :
    Rule.mk q a target action ∈ rules := by
  induction rules with
  | nil => simp at h
  | cons rule rules ih =>
      rcases rule with ⟨⟨source, read⟩, ⟨target', action'⟩⟩
      by_cases hkey : (q, a) = (source, read)
      · cases hkey
        change lookupAction (Rule.mk q a target' action' :: rules) q a =
          some (target, action) at h
        rw [lookupAction_cons_eq] at h
        have hresult : (target', action') = (target, action) := Option.some.inj h
        cases hresult
        simp [Rule.mk]
      · have htail : lookupAction rules q a = some (target, action) := by
          simpa [lookupAction, hkey] using h
        exact List.mem_cons_of_mem _ (ih htail)

/-- Successful lookup is exactly table membership when keys are unique. -/
theorem lookupAction_eq_some_iff_of_deterministic
    {rules : Table numSymbols}
    (hdet : Deterministic rules)
    {q : State} {a : Symbol numSymbols}
    {target : State} {action : Action numSymbols} :
    lookupAction rules q a = some (target, action) ↔
      Rule.mk q a target action ∈ rules := by
  constructor
  · exact rule_mem_of_lookupAction_eq_some
  · intro hmem
    induction rules with
    | nil => simp at hmem
    | cons rule rules ih =>
        rcases rule with ⟨⟨source, read⟩, ⟨target', action'⟩⟩
        simp only [Deterministic, List.map_cons, List.nodup_cons] at hdet
        rcases hdet with ⟨hkeyFresh, htailDet⟩
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htail
        · cases hhead
          exact lookupAction_cons_eq _ _ _ _ _
        · have hkey : (q, a) ≠ (source, read) := by
            intro heq
            apply hkeyFresh
            rw [← heq]
            exact List.mem_map.mpr ⟨Rule.mk q a target action, htail, rfl⟩
          change lookupAction (Rule.mk source read target' action' :: rules) q a =
            some (target, action)
          rw [lookupAction_cons_ne hkey]
          exact ih htailDet htail

/-- Under deterministic keys, the semantic `TM0` transition is exactly the
corresponding explicit rule. -/
theorem machine_eq_some_iff_of_deterministic
    {numSymbols : Nat}
    {rules : Table numSymbols}
    (hdet : Deterministic rules)
    {q : State} {a : Symbol numSymbols}
    {target : State} {action : Action numSymbols} :
    machine rules q a = some (target, action.toStmt) ↔
      Rule.mk q a target action ∈ rules := by
  rw [machine_apply]
  constructor
  · intro h
    cases hlookup : lookupAction rules q a with
    | none => simp [hlookup] at h
    | some result =>
        rcases result with ⟨target', action'⟩
        simp only [hlookup, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, haction⟩
        have : action' = action := Action.toStmt_injective haction
        cases this
        exact (lookupAction_eq_some_iff_of_deterministic hdet).1 hlookup
  · intro h
    have hlookup :=
      (lookupAction_eq_some_iff_of_deterministic hdet).2 h
    simp [hlookup]

/-! ## Computability of table lookup -/

/-- Explicit table lookup is primitive recursive in the table, state, and
scanned symbol. -/
theorem lookupAction_primrec :
    Primrec fun input :
        Table numSymbols × Key numSymbols =>
      lookupAction input.1 input.2.1 input.2.2 := by
  have hlookup : Primrec fun input :
      Table numSymbols × Key numSymbols =>
      @List.lookup (Key numSymbols)
        (Result numSymbols) instBEqOfDecidableEq input.2 input.1 :=
    Primrec.listLookup.comp Primrec.snd Primrec.fst
  exact hlookup.of_eq fun input => by
    symm
    exact lookupAction_eq_listLookup input.1 input.2.1 input.2.2

/-- Computability corollary for explicit table lookup. -/
theorem lookupAction_computable :
    Computable fun input :
        Table numSymbols × Key numSymbols =>
      lookupAction input.1 input.2.1 input.2.2 :=
  lookupAction_primrec.to_comp

end FiniteTM0
end Hooper
end Kari
end LeanWang
