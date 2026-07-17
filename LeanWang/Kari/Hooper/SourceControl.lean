/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FiniteTM0
import LeanWang.Kari.Hooper.StackEncoding

/-!
# Effective finite control for the fixed Hooper source machine

`SourceMachine.machine` has finite control and a finite alphabet, but those
facts alone are not quite enough for the later counter-machine compiler.  In
particular, the generic coding in `StackEncoding` starts from a
noncomputably-chosen `Fintype.equivFin`.  Here we give the *particular* source
alphabet a canonical, executable code.

The translated alphabet consists of a Boolean bottom marker and four optional
four-valued stack symbols.  We code the four stack symbols by `Fin 4`, an
optional symbol by `Fin 5` (with `none` at zero), and the complete alphabet by
`Fin 1250 = Fin (2 * 5^4)`.  Consequently the blank symbol has code zero by
construction.

The translated control labels contain higher-order syntax, so their fixed
finite support is enumerated once and for all.  This choice is a constant of
the compiler, not part of its input.  We enumerate every coded state/symbol
pair, retain precisely the nonhalting transitions, and obtain an explicit
`FiniteTM0.Table`.  The main correctness theorem says that lookup in this
table is exactly the encoded transition of `SourceMachine.machine`.
-/

noncomputable section

namespace LeanWang
namespace Kari
namespace Hooper
namespace SourceControl

open Turing

/-! ## A canonical pointed code for the source alphabet -/

abbrev Stack := UniversalTM0Semantic.Stack
abbrev StackSymbol := Turing.PartrecToTM2.Γ'
abbrev StackCell := Option StackSymbol
abbrev StackVector := ∀ _ : Stack, StackCell

/-- The four stack-symbol constructors, in their declaration order. -/
def stackSymbolEquivBits : StackSymbol ≃ Bool × Bool where
  toFun
    | .consₗ => (false, false)
    | .cons => (false, true)
    | .bit0 => (true, false)
    | .bit1 => (true, true)
  invFun
    | (false, false) => .consₗ
    | (false, true) => .cons
    | (true, false) => .bit0
    | (true, true) => .bit1
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;> rfl

/-- Canonical stack-symbol code `consₗ, cons, bit0, bit1 ↦ 0,1,2,3`. -/
def stackSymbolEquivFin : StackSymbol ≃ Fin 4 :=
  stackSymbolEquivBits |>.trans
    (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm) |>.trans
      finProdFinEquiv

/-- Canonical optional-symbol code, with `none ↦ 0`. -/
def stackCellEquivFin : StackCell ≃ Fin 5 :=
  (Equiv.optionCongr stackSymbolEquivFin).trans (finSuccEquiv 4).symm

/-- Make the four named stacks into an ordinary four-tuple. -/
def stackVectorEquivTuple :
    StackVector ≃ StackCell × StackCell × StackCell × StackCell where
  toFun f := (f .main, f .rev, f .aux, f .stack)
  invFun p
    | .main => p.1
    | .rev => p.2.1
    | .aux => p.2.2.1
    | .stack => p.2.2.2
  left_inv := by
    intro f
    funext k
    cases k <;> rfl
  right_inv := by
    rintro ⟨a, b, c, d⟩
    rfl

/-- Four base-five digits as one number below `5^4 = 625`. -/
def stackVectorEquivFin : StackVector ≃ Fin 625 :=
  stackVectorEquivTuple |>.trans
    (Equiv.prodCongr stackCellEquivFin
      (Equiv.prodCongr stackCellEquivFin
        (Equiv.prodCongr stackCellEquivFin stackCellEquivFin))) |>.trans
    (Equiv.prodCongr (Equiv.refl (Fin 5))
      (Equiv.prodCongr (Equiv.refl (Fin 5)) finProdFinEquiv)) |>.trans
    (Equiv.prodCongr (Equiv.refl (Fin 5)) finProdFinEquiv) |>.trans
    finProdFinEquiv

@[simp]
theorem stackVectorEquivFin_default :
    stackVectorEquivFin (default : StackVector) = 0 := by
  apply Fin.ext
  rfl

/-- The source alphabet has exactly `2 * 5^4 = 1250` canonical symbols. -/
abbrev numSymbols : Nat := 1250

/-- Explicit alphabet enumeration.  Its order is mixed radix: the marker bit
is the most significant component and each optional stack cell is base five. -/
def alphabetEquivFin : SourceMachine.Alphabet ≃ Fin numSymbols :=
  (Equiv.prodCongr finTwoEquiv.symm stackVectorEquivFin).trans
    finProdFinEquiv

/-- The finite symbol consumed by explicit source transition tables. -/
def encodeSymbol : SourceMachine.Alphabet → FiniteTM0.Symbol numSymbols :=
  alphabetEquivFin

/-- Decode an explicit source symbol. -/
def decodeSymbol : FiniteTM0.Symbol numSymbols → SourceMachine.Alphabet :=
  alphabetEquivFin.symm

@[simp]
theorem decodeSymbol_encodeSymbol (a : SourceMachine.Alphabet) :
    decodeSymbol (encodeSymbol a) = a :=
  alphabetEquivFin.symm_apply_apply a

@[simp]
theorem encodeSymbol_decodeSymbol (a : FiniteTM0.Symbol numSymbols) :
    encodeSymbol (decodeSymbol a) = a :=
  alphabetEquivFin.apply_symm_apply a

/-- Natural-number digit of a source symbol. -/
def symbolDigit (a : SourceMachine.Alphabet) : Nat :=
  (encodeSymbol a).val

@[simp]
theorem encodeSymbol_default :
    encodeSymbol (default : SourceMachine.Alphabet) = 0 := by
  change alphabetEquivFin (false, fun _ => none) = 0
  change finProdFinEquiv
    (finTwoEquiv.symm false, stackVectorEquivFin (fun _ => none)) = 0
  have hv : stackVectorEquivFin (fun _ : Stack => none) = 0 := by
    apply Fin.ext
    rfl
  rw [hv]
  rfl

@[simp]
theorem symbolDigit_default :
    symbolDigit (default : SourceMachine.Alphabet) = 0 := by
  simp [symbolDigit]

theorem symbolDigit_lt (a : SourceMachine.Alphabet) :
    symbolDigit a < numSymbols :=
  (encodeSymbol a).isLt

theorem encodeSymbol_injective : Function.Injective encodeSymbol :=
  alphabetEquivFin.injective

theorem symbolDigit_injective : Function.Injective symbolDigit := by
  intro a b h
  apply encodeSymbol_injective
  exact Fin.ext h

instance instPrimcodableAlphabet : Primcodable SourceMachine.Alphabet :=
  Primcodable.ofEquiv (Fin numSymbols) alphabetEquivFin

theorem encodeSymbol_primrec : Primrec encodeSymbol :=
  Primrec.of_equiv

theorem encodeSymbol_computable : Computable encodeSymbol :=
  encodeSymbol_primrec.to_comp

theorem decodeSymbol_primrec : Primrec decodeSymbol :=
  Primrec.of_equiv_symm

theorem decodeSymbol_computable : Computable decodeSymbol :=
  decodeSymbol_primrec.to_comp

theorem symbolDigit_primrec : Primrec symbolDigit :=
  Primrec.fin_val.comp encodeSymbol_primrec

theorem symbolDigit_computable : Computable symbolDigit :=
  symbolDigit_primrec.to_comp

/-! ## A fixed finite code for source control states -/

/-- Number of states in the fixed transition-closed support. -/
def numStates : Nat := Fintype.card SourceMachine.State

/-- A once-and-for-all enumeration of the fixed source control.  Unlike the
alphabet enumeration, its concrete order is immaterial to all later proofs. -/
def stateEquivFin : SourceMachine.State ≃ Fin numStates :=
  Fintype.equivFin SourceMachine.State

instance instPrimcodableState : Primcodable SourceMachine.State :=
  Primcodable.ofEquiv (Fin numStates) stateEquivFin

/-- Bounded code of a source state. -/
def encodeStateFin : SourceMachine.State → Fin numStates :=
  stateEquivFin

/-- Natural-number control tag allocated to a source state. -/
def encodeState (q : SourceMachine.State) : Nat :=
  (encodeStateFin q).val

/-- Decode a bounded source-state code. -/
def decodeStateFin : Fin numStates → SourceMachine.State :=
  stateEquivFin.symm

@[simp]
theorem decodeStateFin_encodeStateFin (q : SourceMachine.State) :
    decodeStateFin (encodeStateFin q) = q :=
  stateEquivFin.symm_apply_apply q

@[simp]
theorem encodeStateFin_decodeStateFin (q : Fin numStates) :
    encodeStateFin (decodeStateFin q) = q :=
  stateEquivFin.apply_symm_apply q

theorem encodeState_lt (q : SourceMachine.State) :
    encodeState q < numStates :=
  (encodeStateFin q).isLt

theorem encodeStateFin_injective : Function.Injective encodeStateFin :=
  stateEquivFin.injective

theorem encodeState_injective : Function.Injective encodeState := by
  intro q r h
  apply encodeStateFin_injective
  exact Fin.ext h

theorem encodeStateFin_primrec : Primrec encodeStateFin :=
  Primrec.of_equiv

theorem encodeStateFin_computable : Computable encodeStateFin :=
  encodeStateFin_primrec.to_comp

theorem decodeStateFin_primrec : Primrec decodeStateFin :=
  Primrec.of_equiv_symm

theorem decodeStateFin_computable : Computable decodeStateFin :=
  decodeStateFin_primrec.to_comp

theorem encodeState_primrec : Primrec encodeState :=
  Primrec.fin_val.comp encodeStateFin_primrec

theorem encodeState_computable : Computable encodeState :=
  encodeState_primrec.to_comp

/-! ## Encoding source actions -/

/-- Encode a semantic source action in the executable finite-table format. -/
def encodeAction : Turing.TM0.Stmt SourceMachine.Alphabet →
    FiniteTM0.Action numSymbols
  | .move .left => .moveLeft
  | .move .right => .moveRight
  | .write a => .write (encodeSymbol a)

/-- Decode an executable finite-table action. -/
def decodeAction : FiniteTM0.Action numSymbols →
    Turing.TM0.Stmt SourceMachine.Alphabet
  | .moveLeft => .move .left
  | .moveRight => .move .right
  | .write a => .write (decodeSymbol a)

@[simp]
theorem decodeAction_encodeAction
    (action : Turing.TM0.Stmt SourceMachine.Alphabet) :
    decodeAction (encodeAction action) = action := by
  cases action with
  | move d => cases d <;> rfl
  | write a => simp [encodeAction, decodeAction]

@[simp]
theorem encodeAction_decodeAction
    (action : FiniteTM0.Action numSymbols) :
    encodeAction (decodeAction action) = action := by
  cases action <;> simp [encodeAction, decodeAction]

/-- Semantic source actions and finite-table actions are equivalent. -/
def actionEquiv : Turing.TM0.Stmt SourceMachine.Alphabet ≃
    FiniteTM0.Action numSymbols where
  toFun := encodeAction
  invFun := decodeAction
  left_inv := decodeAction_encodeAction
  right_inv := encodeAction_decodeAction

instance instPrimcodableStmt :
    Primcodable (Turing.TM0.Stmt SourceMachine.Alphabet) :=
  Primcodable.ofEquiv (FiniteTM0.Action numSymbols) actionEquiv

theorem encodeAction_primrec : Primrec encodeAction :=
  Primrec.of_equiv

theorem encodeAction_computable : Computable encodeAction :=
  encodeAction_primrec.to_comp

theorem decodeAction_primrec : Primrec decodeAction :=
  Primrec.of_equiv_symm

theorem decodeAction_computable : Computable decodeAction :=
  decodeAction_primrec.to_comp

/-! ## The complete finite source transition table -/

abbrev SourceKey := Fin numStates × FiniteTM0.Symbol numSymbols

/-- Every bounded state/symbol input, in a fixed order. -/
def sourceKeys : List SourceKey :=
  (List.finRange numStates).product (List.finRange numSymbols)

@[simp]
theorem mem_sourceKeys (q : Fin numStates)
    (a : FiniteTM0.Symbol numSymbols) :
    (q, a) ∈ sourceKeys := by
  simp [sourceKeys]

theorem sourceKeys_nodup : sourceKeys.Nodup := by
  exact (List.nodup_finRange numStates).product
    (List.nodup_finRange numSymbols)

/-- Compile one bounded source input.  Halting entries are omitted. -/
def compileKey (key : SourceKey) : Option (FiniteTM0.Rule numSymbols) :=
  match SourceMachine.machine (decodeStateFin key.1) (decodeSymbol key.2) with
  | none => none
  | some (q', action) =>
      some (FiniteTM0.Rule.mk key.1.val key.2 (encodeState q')
        (encodeAction action))

/-- Explicit finite transition table of `SourceMachine.machine`. -/
def transitionTable : FiniteTM0.Table numSymbols :=
  sourceKeys.filterMap compileKey

theorem compileKey_result_key {key : SourceKey}
    {rule : FiniteTM0.Rule numSymbols}
    (h : rule ∈ compileKey key) :
    rule.1 = (key.1.val, key.2) := by
  unfold compileKey at h
  split at h
  · simp at h
  · next q' action heq =>
      simp only [Option.mem_def, Option.some.injEq] at h
      subst rule
      rfl

private theorem transitionKeys_eq :
    transitionTable.map Prod.fst =
      sourceKeys.filterMap fun key => (compileKey key).map Prod.fst := by
  simp [transitionTable, List.map_filterMap]

/-- The generated table has at most one rule for each state/symbol key. -/
theorem transitionTable_deterministic :
    FiniteTM0.Deterministic transitionTable := by
  rw [FiniteTM0.Deterministic, transitionKeys_eq]
  apply sourceKeys_nodup.filterMap
  intro key key' result h h'
  rcases Option.mem_map.mp h with ⟨rule, hrule, heq⟩
  rcases Option.mem_map.mp h' with ⟨rule', hrule', heq'⟩
  have hkeys : (key.1.val, key.2) = (key'.1.val, key'.2) := by
    calc
      (key.1.val, key.2) = rule.1 := (compileKey_result_key hrule).symm
      _ = result := heq
      _ = rule'.1 := heq'.symm
      _ = (key'.1.val, key'.2) := compileKey_result_key hrule'
  rcases key with ⟨q, a⟩
  rcases key' with ⟨q', a'⟩
  have hq : q = q' := Fin.ext (congrArg Prod.fst hkeys)
  have ha : a = a' := congrArg Prod.snd hkeys
  exact Prod.ext hq ha

private theorem compiled_rule_mem {key : SourceKey}
    {rule : FiniteTM0.Rule numSymbols}
    (h : compileKey key = some rule) :
    rule ∈ transitionTable := by
  exact List.mem_filterMap.mpr ⟨key, mem_sourceKeys _ _, h⟩

private theorem source_key_of_table_rule
    {q : SourceMachine.State} {a : SourceMachine.Alphabet}
    {rule : FiniteTM0.Rule numSymbols}
    (hrule : rule ∈ transitionTable)
    (hkey : rule.1 = (encodeState q, encodeSymbol a)) :
    ∃ key : SourceKey,
      key = (encodeStateFin q, encodeSymbol a) ∧
        compileKey key = some rule := by
  rcases List.mem_filterMap.mp hrule with ⟨key, _, hcompile⟩
  have hcompiledKey : rule.1 = (key.1.val, key.2) :=
    compileKey_result_key (by simp [hcompile])
  have hpairs : (key.1.val, key.2) =
      ((encodeStateFin q).val, encodeSymbol a) := by
    exact hcompiledKey.symm.trans hkey
  have hstate : key.1 = encodeStateFin q :=
    Fin.ext (congrArg Prod.fst hpairs)
  have hsymbol : key.2 = encodeSymbol a :=
    congrArg Prod.snd hpairs
  exact ⟨key, Prod.ext hstate hsymbol, hcompile⟩

/-- Lookup in the explicit table is exactly the encoded source transition. -/
theorem lookup_transitionTable (q : SourceMachine.State)
    (a : SourceMachine.Alphabet) :
    FiniteTM0.lookupAction transitionTable (encodeState q) (encodeSymbol a) =
      (SourceMachine.machine q a).map fun result =>
        (encodeState result.1, encodeAction result.2) := by
  cases hmachine : SourceMachine.machine q a with
  | none =>
      apply FiniteTM0.lookupAction_eq_none_of_key_not_mem
      intro hmem
      rcases List.mem_map.mp hmem with ⟨rule, hrule, hkey⟩
      rcases source_key_of_table_rule hrule hkey with
        ⟨key, rfl, hcompile⟩
      simp [compileKey, hmachine] at hcompile
  | some result =>
      rcases result with ⟨q', action⟩
      simp only [Option.map_some]
      apply (FiniteTM0.lookupAction_eq_some_iff_of_deterministic
        transitionTable_deterministic).2
      apply compiled_rule_mem
        (key := (encodeStateFin q, encodeSymbol a))
      simp [compileKey, hmachine, encodeState]

/-- Successful table lookup decodes to precisely the semantic source rule. -/
theorem lookup_transitionTable_eq_some_iff
    {q : SourceMachine.State} {a : SourceMachine.Alphabet}
    {target : Nat} {action : FiniteTM0.Action numSymbols} :
    FiniteTM0.lookupAction transitionTable (encodeState q) (encodeSymbol a) =
        some (target, action) ↔
      ∃ q' sourceAction,
        SourceMachine.machine q a = some (q', sourceAction) ∧
        target = encodeState q' ∧ action = encodeAction sourceAction := by
  rw [lookup_transitionTable]
  constructor
  · intro hlookup
    rcases Option.map_eq_some_iff.mp hlookup with
      ⟨⟨q', sourceAction⟩, hmachine, hresult⟩
    have htarget : encodeState q' = target := congrArg Prod.fst hresult
    have haction : encodeAction sourceAction = action :=
      congrArg Prod.snd hresult
    exact ⟨q', sourceAction, hmachine, htarget.symm, haction.symm⟩
  · rintro ⟨q', sourceAction, hmachine, htarget, haction⟩
    apply Option.map_eq_some_iff.mpr
    exact ⟨(q', sourceAction), hmachine,
      Prod.ext htarget.symm haction.symm⟩

/-- The source transition function is primitive recursive after applying the
fixed finite state and action codes. -/
theorem encoded_source_transition_primrec :
    Primrec fun input : SourceMachine.State × SourceMachine.Alphabet =>
      (SourceMachine.machine input.1 input.2).map fun result =>
        (encodeState result.1, encodeAction result.2) := by
  exact Primrec.dom_finite _

theorem encoded_source_transition_computable :
    Computable fun input : SourceMachine.State × SourceMachine.Alphabet =>
      (SourceMachine.machine input.1 input.2).map fun result =>
        (encodeState result.1, encodeAction result.2) :=
  encoded_source_transition_primrec.to_comp

/-- Executable lookup in the fixed transition table. -/
def lookup (input : FiniteTM0.Key numSymbols) :
    Option (FiniteTM0.Result numSymbols) :=
  FiniteTM0.lookupAction transitionTable input.1 input.2

theorem lookup_primrec : Primrec lookup := by
  exact FiniteTM0.lookupAction_primrec.comp
    (Primrec.pair (Primrec.const transitionTable) Primrec.id)

theorem lookup_computable : Computable lookup :=
  lookup_primrec.to_comp

/-- The fixed transition table itself is a primitive-recursive compiler
constant. -/
theorem transitionTable_primrec :
    Primrec fun _ : Unit => transitionTable :=
  Primrec.const transitionTable

theorem transitionTable_computable :
    Computable fun _ : Unit => transitionTable :=
  transitionTable_primrec.to_comp

/-! ## High-level counter-register step specification -/

/-- A source control state together with the three logical tape registers.
This is the specification that arithmetic counter macros must implement. -/
structure RegisterCfg where
  state : SourceMachine.State
  tape : StackEncoding.TapeRegisters SourceMachine.Alphabet

/-- Interpret the three logical tape registers as a finite-support Mathlib
source configuration. -/
def RegisterCfg.decode (c : RegisterCfg) :
    Turing.TM0.Cfg SourceMachine.Alphabet SourceMachine.State :=
  ⟨c.state, StackEncoding.TapeRegisters.decodeTape c.tape⟩

/-- One source step at the level of logical stack operations. -/
def registerStep (c : RegisterCfg) : Option RegisterCfg :=
  (SourceMachine.machine c.state c.tape.head).map fun result =>
    ⟨result.1,
      match result.2 with
      | .move .left => c.tape.moveLeft
      | .move .right => c.tape.moveRight
      | .write a => c.tape.write a⟩

/-- Decoding commutes with the high-level register specification. -/
theorem decode_registerStep (c : RegisterCfg) :
    (registerStep c).map RegisterCfg.decode =
      Turing.TM0.step SourceMachine.machine c.decode := by
  rcases c with ⟨q, tape⟩
  simp only [registerStep, RegisterCfg.decode, Turing.TM0.step]
  rw [show (StackEncoding.TapeRegisters.decodeTape tape).head = tape.head by rfl]
  cases h : SourceMachine.machine q tape.head with
  | none => simp
  | some result =>
      rcases result with ⟨q', action⟩
      cases action with
      | move d => cases d <;> simp [RegisterCfg.decode]
      | write a => simp [RegisterCfg.decode]

end SourceControl
end Hooper
end Kari
end LeanWang
