/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BoundedMarkerProgram

/-!
# Uniform effectiveness of tagged bounded-search controllers

The bounded controller is an explicit finite list for every fixed set of
commands.  For the final many-one reduction we additionally need uniformity:
its table must be computable when the radius, command continuations, and
appended core table vary with the input program code.

This file supplies primitive-recursive codes for the small command language
and proves primitive recursiveness of the generated controller.  The public
interface is deliberately compositional: a later compiler only has to prove
that its numeric parameters, command list, and core table are primitive
recursive; `table_primrec_of` then compiles all of them uniformly.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace BoundedMarkerProgram

open Turing

noncomputable section

/-! ## Primitive-recursive codes for the command language -/

/-- Two-valued code for tape directions. -/
def dirEquivBool : Turing.Dir ≃ Bool where
  toFun
    | .left => false
    | .right => true
  invFun
    | false => .left
    | true => .right
  left_inv := by intro direction; cases direction <;> rfl
  right_inv := by intro bit; cases bit <;> rfl

instance instPrimcodableDir : Primcodable Turing.Dir :=
  Primcodable.ofEquiv Bool dirEquivBool

instance instFintypeDir : Fintype Turing.Dir :=
  Fintype.ofEquiv Bool dirEquivBool.symm

/-- Tuple code for an independent marker move. -/
def MarkerProgram.Move.equivCode :
    MarkerProgram.Move ≃ Fin 5 × Turing.Dir × Turing.Dir where
  toFun move := (move.expected, move.searchDirection, move.shiftDirection)
  invFun code := ⟨code.1, code.2.1, code.2.2⟩
  left_inv := by intro move; cases move; rfl
  right_inv := by intro code; rcases code with ⟨expected, search, shift⟩; rfl

instance MarkerProgram.Move.instPrimcodable :
    Primcodable MarkerProgram.Move :=
  Primcodable.ofEquiv (Fin 5 × Turing.Dir × Turing.Dir)
    MarkerProgram.Move.equivCode

/-- `none` codes preservation; `some departure` codes erasure. -/
def NavigationAction.equivCode : NavigationAction ≃ Option (Option Turing.Dir) where
  toFun
    | .preserve => none
    | .erase departure => some departure
  invFun
    | none => .preserve
    | some departure => .erase departure
  left_inv := by intro action; cases action <;> rfl
  right_inv := by intro code; cases code <;> rfl

instance NavigationAction.instPrimcodable : Primcodable NavigationAction :=
  Primcodable.ofEquiv (Option (Option Turing.Dir)) NavigationAction.equivCode

/-- `none` codes an arbitrary physical tag; `some label` codes a boundary. -/
def Target.equivCode {numTags : Nat} : Target numTags ≃ Option (Fin 5) where
  toFun
    | .boundary label => some label
    | .anyTag => none
  invFun
    | some label => .boundary label
    | none => .anyTag
  left_inv := by intro target; cases target <;> rfl
  right_inv := by intro code; cases code <;> rfl

instance Target.instPrimcodable {numTags : Nat} : Primcodable (Target numTags) :=
  Primcodable.ofEquiv (Option (Fin 5)) Target.equivCode

/-- Product payload of a boundary-navigation command. -/
abbrev BoundaryNavigationCode (numTags : Nat) :=
  Fin 5 × Turing.Dir × FiniteTM0.State × Fin numTags × NavigationAction

/-- Product payload of a tag-navigation command. -/
abbrev TagNavigationCode (numTags : Nat) :=
  Turing.Dir × FiniteTM0.State × Fin numTags

/-- Product payload of a marker-shift command. -/
abbrev MarkerShiftCode (numTags : Nat) :=
  MarkerProgram.Move × FiniteTM0.State × Fin numTags ×
    Option Turing.Dir × Option FiniteTM0.State

/-- Disjoint-sum code exposing the three command constructors. -/
abbrev CommandCode (numTags : Nat) :=
  BoundaryNavigationCode numTags ⊕
    (TagNavigationCode numTags ⊕ MarkerShiftCode numTags)

/-- Primitive-recursive structural code for bounded commands. -/
def Command.equivCode {numTags : Nat} : Command numTags ≃ CommandCode numTags where
  toFun
    | .boundaryNavigation expected direction success tag action =>
        .inl (expected, direction, success, tag, action)
    | .tagNavigation direction success tag => .inr (.inl (direction, success, tag))
    | .markerShift move success tag departure collision =>
        .inr (.inr (move, success, tag, departure, collision))
  invFun
    | .inl (expected, direction, success, tag, action) =>
        .boundaryNavigation expected direction success tag action
    | .inr (.inl (direction, success, tag)) =>
        .tagNavigation direction success tag
    | .inr (.inr (move, success, tag, departure, collision)) =>
        .markerShift move success tag departure collision
  left_inv := by intro command; cases command <;> rfl
  right_inv := by
    intro code
    rcases code with code | code
    · rcases code with ⟨expected, direction, success, tag, action⟩
      rfl
    · rcases code with code | code
      · rcases code with ⟨direction, success, tag⟩
        rfl
      · rcases code with ⟨move, success, tag, departure, collision⟩
        rfl

instance Command.instPrimcodable {numTags : Nat} :
    Primcodable (Command numTags) :=
  Primcodable.ofEquiv (CommandCode numTags) Command.equivCode

/-- Encoding a marker move by its tuple is primitive recursive. -/
theorem move_equivCode_primrec : Primrec MarkerProgram.Move.equivCode :=
  Primrec.of_equiv

/-- Decoding the tuple representation of a marker move is primitive
recursive. -/
theorem move_ofCode_primrec : Primrec MarkerProgram.Move.equivCode.symm :=
  Primrec.of_equiv_symm

/-- Encoding navigation actions by their nested option code is primitive
recursive. -/
theorem navigationAction_equivCode_primrec :
    Primrec NavigationAction.equivCode :=
  Primrec.of_equiv

/-- Decoding a navigation-action code is primitive recursive. -/
theorem navigationAction_ofCode_primrec :
    Primrec NavigationAction.equivCode.symm :=
  Primrec.of_equiv_symm

/-- Encoding a bounded command by its constructor sum is primitive recursive. -/
theorem command_equivCode_primrec {numTags : Nat} :
    Primrec (@Command.equivCode numTags) :=
  Primrec.of_equiv

/-- Decoding the public constructor-sum representation of a bounded command
is primitive recursive.  Later compilers can construct `CommandCode` values
with the standard sum/product combinators and finish with this map. -/
theorem command_ofCode_primrec {numTags : Nat} :
    Primrec (@Command.equivCode numTags).symm :=
  Primrec.of_equiv_symm

/-! ## Primitive-recursive finite-machine building blocks -/

private theorem singleton_primrec {alpha beta : Type*}
    [Primcodable alpha] [Primcodable beta] {f : alpha → beta}
    (hf : Primrec f) : Primrec fun a => [f a] :=
  Primrec.list_cons.comp hf (Primrec.const [])

private theorem rule_primrec {alpha : Type*} [Primcodable alpha]
    {numSymbols : Nat}
    {source target : alpha → FiniteTM0.State}
    {read : alpha → FiniteTM0.Symbol numSymbols}
    {action : alpha → FiniteTM0.Action numSymbols}
    (hsource : Primrec source) (hread : Primrec read)
    (htarget : Primrec target) (haction : Primrec action) :
    Primrec fun a => FiniteTM0.Rule.mk (source a) (read a)
      (target a) (action a) :=
  Primrec.pair (Primrec.pair hsource hread) (Primrec.pair htarget haction)

private theorem writeAction_primrec {alpha : Type*} [Primcodable alpha]
    {numSymbols : Nat} {symbol : alpha → FiniteTM0.Symbol numSymbols}
    (hsymbol : Primrec symbol) :
    Primrec fun a =>
      (FiniteTM0.Action.write (symbol a) : FiniteTM0.Action numSymbols) := by
  have hcode : Primrec fun a =>
      (Sum.inr (symbol a) : Bool ⊕ FiniteTM0.Symbol numSymbols) :=
    Primrec.sumInr.comp hsymbol
  exact (Primrec.of_equiv_symm
    (e := FiniteTM0.Action.equivCode (numSymbols := numSymbols))).comp hcode

/-- Embedding a marker-alphabet symbol into the tagged alphabet is primitive
recursive. -/
theorem baseSymbol_primrec {numTags : Nat} :
    Primrec (@baseSymbol numTags) := by
  apply Primrec.fin_val_iff.mp
  exact Primrec.fin_val

/-- The physical-symbol embedding of return tags is primitive recursive. -/
theorem tagSymbol_primrec {numTags : Nat} :
    Primrec (@tagSymbol numTags) := by
  apply Primrec.fin_val_iff.mp
  exact Primrec.nat_add.comp (Primrec.const MarkerMachine.AlphabetSize)
    Primrec.fin_val

/-- The physical-symbol embedding of boundary labels is primitive recursive. -/
theorem boundarySymbol_primrec {numTags : Nat} :
    Primrec (@boundarySymbol numTags) := by
  exact Primrec.dom_finite _

/-- Turning a direction into the corresponding explicit move action is
primitive recursive. -/
theorem moveAction_primrec : Primrec MarkerMachine.moveAction :=
  Primrec.dom_finite _

/-- Lifting an explicit action to the tagged alphabet is primitive recursive. -/
theorem liftAction_primrec {numTags : Nat} :
    Primrec (@liftAction numTags) := by
  have hcode : Primrec
      (FiniteTM0.Action.equivCode
        (numSymbols := MarkerMachine.AlphabetSize)) :=
    Primrec.of_equiv
  have hleft : Primrec fun _ : Bool =>
      (FiniteTM0.Action.moveLeft :
        FiniteTM0.Action (AlphabetSize numTags)) :=
    Primrec.const _
  have hright : Primrec fun _ : Bool =>
      (FiniteTM0.Action.moveRight :
        FiniteTM0.Action (AlphabetSize numTags)) :=
    Primrec.const _
  have hmove : Primrec fun bit : Bool =>
      (bif bit then FiniteTM0.Action.moveRight
        else FiniteTM0.Action.moveLeft :
          FiniteTM0.Action (AlphabetSize numTags)) :=
    Primrec.cond Primrec.id hright hleft
  have hwrite : Primrec fun symbol : MarkerMachine.Symbol =>
      (FiniteTM0.Action.write (baseSymbol symbol) :
        FiniteTM0.Action (AlphabetSize numTags)) := by
    have hcodewrite : Primrec fun symbol : MarkerMachine.Symbol =>
        (Sum.inr (baseSymbol symbol) : Bool ⊕ Symbol numTags) :=
      Primrec.sumInr.comp baseSymbol_primrec
    exact (Primrec.of_equiv_symm
      (e := FiniteTM0.Action.equivCode
        (numSymbols := AlphabetSize numTags))).comp hcodewrite
  have hcases : Primrec fun code : (Bool ⊕ MarkerMachine.Symbol) =>
      match code with
      | .inl bit => bif bit then FiniteTM0.Action.moveRight
          else FiniteTM0.Action.moveLeft
      | .inr symbol =>
          (FiniteTM0.Action.write (baseSymbol symbol) :
            FiniteTM0.Action (AlphabetSize numTags)) := by
    exact (Primrec.sumCasesOn (Primrec.id :
      Primrec fun code : (Bool ⊕ MarkerMachine.Symbol) => code)
      (hmove.comp Primrec.snd).to₂
      (hwrite.comp Primrec.snd).to₂).of_eq fun code => by
        cases code <;> rfl
  exact (hcases.comp hcode).of_eq fun action => by
    cases action <;> rfl

/-- Lifting one rule from the marker alphabet is primitive recursive. -/
theorem liftRule_primrec {numTags : Nat} :
    Primrec (@liftRule numTags) := by
  apply rule_primrec
  · exact Primrec.fst.comp Primrec.fst
  · exact baseSymbol_primrec.comp (Primrec.snd.comp Primrec.fst)
  · exact Primrec.fst.comp Primrec.snd
  · exact liftAction_primrec.comp (Primrec.snd.comp Primrec.snd)

/-- Lifting a whole finite table from the marker alphabet is primitive
recursive. -/
theorem liftTable_primrec {numTags : Nat} :
    Primrec (@liftTable numTags) :=
  Primrec.list_map Primrec.id
    (liftRule_primrec.comp Primrec.snd).to₂

/-! ## Primitive-recursive target-rule families -/

private theorem anyTagRules_primrec {numTags : Nat} :
    Primrec fun input : FiniteTM0.State × FiniteTM0.State =>
      (List.finRange numTags).map fun tag =>
        FiniteTM0.Rule.mk input.1 (tagSymbol tag) input.2
          (.write (tagSymbol tag)) := by
  have hrule : Primrec₂ fun input :
      FiniteTM0.State × FiniteTM0.State => fun tag : Fin numTags =>
      FiniteTM0.Rule.mk input.1 (tagSymbol tag) input.2
        (.write (tagSymbol tag)) := by
    apply Primrec₂.mk
    apply rule_primrec
    · exact Primrec.fst.comp Primrec.fst
    · exact tagSymbol_primrec.comp Primrec.snd
    · exact Primrec.snd.comp Primrec.fst
    · exact writeAction_primrec (tagSymbol_primrec.comp Primrec.snd)
  exact Primrec.list_map (Primrec.const (List.finRange numTags)) hrule

/-- The finite family recognizing a variable target is primitive recursive
in both of its states and the target descriptor. -/
theorem targetRules_primrec {numTags : Nat} :
    Primrec fun input :
      FiniteTM0.State × FiniteTM0.State × Target numTags =>
      targetRules input.1 input.2.1 input.2.2 := by
  have htargetCode : Primrec fun input :
      FiniteTM0.State × FiniteTM0.State × Target numTags =>
      Target.equivCode input.2.2 :=
    (Primrec.of_equiv (e := @Target.equivCode numTags)).comp
      (Primrec.snd.comp Primrec.snd)
  have hany : Primrec fun input :
      FiniteTM0.State × FiniteTM0.State × Target numTags =>
      (List.finRange numTags).map fun tag =>
        FiniteTM0.Rule.mk input.1 (tagSymbol tag) input.2.1
          (.write (tagSymbol tag)) :=
    anyTagRules_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have hboundary : Primrec₂ fun input :
      FiniteTM0.State × FiniteTM0.State × Target numTags =>
      fun label : Fin 5 =>
        [FiniteTM0.Rule.mk input.1
          (boundarySymbol (numTags := numTags) label) input.2.1
          (.write (boundarySymbol (numTags := numTags) label))] := by
    apply Primrec₂.mk
    apply singleton_primrec
    apply rule_primrec
    · exact Primrec.fst.comp Primrec.fst
    · exact boundarySymbol_primrec.comp Primrec.snd
    · exact Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    · exact writeAction_primrec (boundarySymbol_primrec.comp Primrec.snd)
  exact (Primrec.option_casesOn htargetCode hany hboundary).of_eq fun input => by
    cases input.2.2 <;> rfl

/-! ## Uniformly unrolled native scans and unwinds -/

private def nativeScanStepTable {numTags : Nat} (target : Target numTags)
    (direction : Turing.Dir) (success state : FiniteTM0.State) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  targetRules state success target ++
    [FiniteTM0.Rule.mk state blankSymbol (state + 1)
      (liftAction (MarkerMachine.moveAction direction))]

private def nativeScanFinalTable {numTags : Nat} (target : Target numTags)
    (success launch state : FiniteTM0.State) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  targetRules state success target ++
    [FiniteTM0.Rule.mk state blankSymbol launch (.write blankSymbol)]

private def nativeScanTableClosed {numTags : Nat} (target : Target numTags)
    (direction : Turing.Dir) (success launch : FiniteTM0.State)
    (remaining state : Nat) : FiniteTM0.Table (AlphabetSize numTags) :=
  ((List.range remaining).flatMap fun index =>
      nativeScanStepTable target direction success (state + index)) ++
    nativeScanFinalTable target success launch (state + remaining)

private theorem nativeScanStepTable_primrec {numTags : Nat} :
    Primrec fun input :
      Target numTags × Turing.Dir × FiniteTM0.State × FiniteTM0.State =>
      nativeScanStepTable input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have htargets : Primrec fun input :
      Target numTags × Turing.Dir × FiniteTM0.State × FiniteTM0.State =>
      targetRules input.2.2.2 input.2.2.1 input.1 :=
    targetRules_primrec.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          Primrec.fst))
  have hmoveRule : Primrec fun input :
      Target numTags × Turing.Dir × FiniteTM0.State × FiniteTM0.State =>
      FiniteTM0.Rule.mk input.2.2.2 (blankSymbol (numTags := numTags))
        (input.2.2.2 + 1)
        (liftAction (numTags := numTags)
          (MarkerMachine.moveAction input.2.1)) := by
    apply rule_primrec
    · exact Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    · exact Primrec.const (blankSymbol (numTags := numTags))
    · exact Primrec.succ.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    · exact liftAction_primrec.comp
        (moveAction_primrec.comp (Primrec.fst.comp Primrec.snd))
  exact (Primrec.list_append.comp htargets
    (singleton_primrec hmoveRule)).of_eq fun _ => rfl

private theorem nativeScanFinalTable_primrec {numTags : Nat} :
    Primrec fun input :
      Target numTags × FiniteTM0.State × FiniteTM0.State × FiniteTM0.State =>
      nativeScanFinalTable input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have htargets : Primrec fun input :
      Target numTags × FiniteTM0.State × FiniteTM0.State × FiniteTM0.State =>
      targetRules input.2.2.2 input.2.1 input.1 :=
    targetRules_primrec.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair (Primrec.fst.comp Primrec.snd) Primrec.fst))
  have hlaunchRule : Primrec fun input :
      Target numTags × FiniteTM0.State × FiniteTM0.State × FiniteTM0.State =>
      FiniteTM0.Rule.mk input.2.2.2 (blankSymbol (numTags := numTags))
        input.2.2.1 (.write (blankSymbol (numTags := numTags))) := by
    apply rule_primrec
    · exact Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    · exact Primrec.const (blankSymbol (numTags := numTags))
    · exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    · exact Primrec.const
        (FiniteTM0.Action.write (blankSymbol (numTags := numTags)))
  exact (Primrec.list_append.comp htargets
    (singleton_primrec hlaunchRule)).of_eq fun _ => rfl

private theorem nativeScanTableClosed_primrec {numTags : Nat} :
    Primrec fun input :
      (Target numTags × Turing.Dir × FiniteTM0.State ×
        FiniteTM0.State) × Nat × Nat =>
      nativeScanTableClosed input.1.1 input.1.2.1 input.1.2.2.1
        input.1.2.2.2 input.2.1 input.2.2 := by
  have hsteps : Primrec fun input :
      (Target numTags × Turing.Dir × FiniteTM0.State ×
        FiniteTM0.State) × Nat × Nat =>
      (List.range input.2.1).flatMap fun index =>
        nativeScanStepTable input.1.1 input.1.2.1 input.1.2.2.1
          (input.2.2 + index) := by
    apply Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd))
    apply Primrec₂.mk
    exact nativeScanStepTable_primrec.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.fst.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
            (Primrec.nat_add.comp
              (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))))
  have hfinal : Primrec fun input :
      (Target numTags × Turing.Dir × FiniteTM0.State ×
        FiniteTM0.State) × Nat × Nat =>
      nativeScanFinalTable input.1.1 input.1.2.2.1 input.1.2.2.2
        (input.2.2 + input.2.1) :=
    nativeScanFinalTable_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
            (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
              (Primrec.fst.comp Primrec.snd)))))
  exact Primrec.list_append.comp hsteps hfinal

private theorem nativeScanTableAux_eq_closed {numTags : Nat}
    (target : Target numTags) (direction : Turing.Dir)
    (success launch remaining state : Nat) :
    nativeScanTableAux target direction success launch remaining state =
      nativeScanTableClosed target direction success launch remaining state := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
      simp [nativeScanTableAux, nativeScanTableClosed,
        List.range_succ_eq_map, List.flatMap_map, ih,
        nativeScanStepTable, Nat.add_assoc]
      apply congrArg₂ (fun first second => first ++ second)
      · apply List.flatMap_congr
        intro index _
        simp [Nat.add_comm, Nat.add_left_comm]
      · simp [Nat.add_comm, Nat.add_left_comm]

/-- The native bounded scan is primitive recursive in its target, direction,
states, radius counter, and starting state. -/
theorem nativeScanTableAux_primrec {numTags : Nat} :
    Primrec fun input :
      (Target numTags × Turing.Dir × FiniteTM0.State ×
        FiniteTM0.State) × Nat × Nat =>
      nativeScanTableAux input.1.1 input.1.2.1 input.1.2.2.1
        input.1.2.2.2 input.2.1 input.2.2 :=
  nativeScanTableClosed_primrec.of_eq fun input =>
    (nativeScanTableAux_eq_closed input.1.1 input.1.2.1 input.1.2.2.1
      input.1.2.2.2 input.2.1 input.2.2).symm

private def unwindStepTable (direction : Turing.Dir)
    (state : FiniteTM0.State) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  [FiniteTM0.Rule.mk state MarkerMachine.blankSymbol (state + 1)
    (MarkerMachine.moveAction (NestingMachine.opposite direction))]

private def unwindFinalTable (search state : FiniteTM0.State) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  [FiniteTM0.Rule.mk state MarkerMachine.blankSymbol search
    (.write MarkerMachine.blankSymbol)]

private def unwindTableClosed (direction : Turing.Dir)
    (search remaining state : Nat) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  ((List.range remaining).flatMap fun index =>
      unwindStepTable direction (state + index)) ++
    unwindFinalTable search (state + remaining)

private theorem opposite_primrec : Primrec NestingMachine.opposite :=
  Primrec.dom_finite _

private theorem unwindStepTable_primrec :
    Primrec fun input : Turing.Dir × FiniteTM0.State =>
      unwindStepTable input.1 input.2 := by
  apply singleton_primrec
  apply rule_primrec
  · exact Primrec.snd
  · exact Primrec.const MarkerMachine.blankSymbol
  · exact Primrec.succ.comp Primrec.snd
  · exact moveAction_primrec.comp
      (opposite_primrec.comp Primrec.fst)

private theorem unwindFinalTable_primrec :
    Primrec fun input : FiniteTM0.State × FiniteTM0.State =>
      unwindFinalTable input.1 input.2 := by
  apply singleton_primrec
  apply rule_primrec
  · exact Primrec.snd
  · exact Primrec.const MarkerMachine.blankSymbol
  · exact Primrec.fst
  · exact Primrec.const
      (FiniteTM0.Action.write MarkerMachine.blankSymbol)

private theorem unwindTableClosed_primrec :
    Primrec fun input :
      (Turing.Dir × FiniteTM0.State) × Nat × Nat =>
      unwindTableClosed input.1.1 input.1.2 input.2.1 input.2.2 := by
  have hsteps : Primrec fun input :
      (Turing.Dir × FiniteTM0.State) × Nat × Nat =>
      (List.range input.2.1).flatMap fun index =>
        unwindStepTable input.1.1 (input.2.2 + index) := by
    apply Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd))
    apply Primrec₂.mk
    exact unwindStepTable_primrec.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.nat_add.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  have hfinal : Primrec fun input :
      (Turing.Dir × FiniteTM0.State) × Nat × Nat =>
      unwindFinalTable input.1.2 (input.2.2 + input.2.1) :=
    unwindFinalTable_primrec.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.fst.comp Primrec.snd)))
  exact Primrec.list_append.comp hsteps hfinal

private theorem unwindTableAux_eq_closed (direction : Turing.Dir)
    (search remaining state : Nat) :
    NestingMachine.unwindTableAux direction search remaining state =
      unwindTableClosed direction search remaining state := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
      simp [NestingMachine.unwindTableAux, unwindTableClosed,
        List.range_succ_eq_map, List.flatMap_map, ih, unwindStepTable,
        Nat.add_assoc]
      apply congrArg₂ (fun first second => first ++ second)
      · apply List.flatMap_congr
        intro index _
        simp [Nat.add_comm, Nat.add_left_comm]
      · simp [Nat.add_comm, Nat.add_left_comm]

/-- The finite unwind generator is primitive recursive in all of its numeric
parameters and its direction. -/
theorem unwindTableAux_primrec :
    Primrec fun input :
      (Turing.Dir × FiniteTM0.State) × Nat × Nat =>
      NestingMachine.unwindTableAux input.1.1 input.1.2
        input.2.1 input.2.2 :=
  unwindTableClosed_primrec.of_eq fun input =>
    (unwindTableAux_eq_closed input.1.1 input.1.2
      input.2.1 input.2.2).symm

/-- One local native bounded scan is primitive recursive in its radius,
target, and direction. -/
theorem nativeScanTable_primrec {numTags : Nat} :
    Primrec fun input : Nat × Target numTags × Turing.Dir =>
      nativeScanTable input.1 input.2.1 input.2.2 := by
  have hsuccess : Primrec fun input :
      Nat × Target numTags × Turing.Dir =>
      NestingMachine.localSuccessState input.1 :=
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 2)).of_eq fun _ => rfl
  have hlaunch : Primrec fun input :
      Nat × Target numTags × Turing.Dir =>
      NestingMachine.localLaunchState input.1 :=
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 3)).of_eq fun _ => rfl
  have hbound : Primrec fun input :
      Nat × Target numTags × Turing.Dir =>
      NestingMachine.bound input.1 :=
    Primrec.succ.comp Primrec.fst
  exact nativeScanTableAux_primrec.comp
    (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.snd.comp Primrec.snd)
          (Primrec.pair hsuccess hlaunch)))
      (Primrec.pair hbound (Primrec.const 0)))

/-- The local finite unwind is primitive recursive in radius and direction. -/
theorem unwindTable_primrec :
    Primrec fun input : Nat × Turing.Dir =>
      NestingMachine.unwindTable input.1 input.2 := by
  have hunwindState : Primrec fun input : Nat × Turing.Dir =>
      NestingMachine.localUnwindState input.1 :=
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 4)).of_eq fun _ => rfl
  exact unwindTableAux_primrec.comp
    (Primrec.pair (Primrec.pair Primrec.snd (Primrec.const 0))
      (Primrec.pair Primrec.fst hunwindState))

/-- One complete tagged local controller is primitive recursive in its
radius, target, and direction. -/
theorem nativeLocalTable_primrec {numTags : Nat} :
    Primrec fun input : Nat × Target numTags × Turing.Dir =>
      nativeLocalTable input.1 input.2.1 input.2.2 := by
  exact Primrec.list_append.comp nativeScanTable_primrec
    (liftTable_primrec.comp
      (unwindTable_primrec.comp
        (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))))

/-! ## Primitive-recursive command projections -/

theorem move_expected_primrec : Primrec MarkerProgram.Move.expected :=
  Primrec.fst.comp move_equivCode_primrec

theorem move_searchDirection_primrec :
    Primrec MarkerProgram.Move.searchDirection :=
  (Primrec.fst.comp Primrec.snd).comp move_equivCode_primrec

theorem move_shiftDirection_primrec :
    Primrec MarkerProgram.Move.shiftDirection :=
  (Primrec.snd.comp Primrec.snd).comp move_equivCode_primrec

private theorem targetBoundary_primrec {numTags : Nat} :
    Primrec (Target.boundary : Fin 5 → Target numTags) := by
  have hcode : Primrec fun label : Fin 5 => some label :=
    Primrec.option_some
  exact (Primrec.of_equiv_symm (e := @Target.equivCode numTags)).comp hcode

/-- The target recognized by a varying command is primitive recursive. -/
theorem Command.target_primrec {numTags : Nat} :
    Primrec (@Command.target numTags) := by
  have hboundary : Primrec fun code : BoundaryNavigationCode numTags =>
      (Target.boundary code.1 : Target numTags) :=
    targetBoundary_primrec.comp Primrec.fst
  have htag : Primrec fun _code : TagNavigationCode numTags =>
      (Target.anyTag : Target numTags) :=
    Primrec.const _
  have hshift : Primrec fun code : MarkerShiftCode numTags =>
      (Target.boundary code.1.expected : Target numTags) :=
    targetBoundary_primrec.comp
      (move_expected_primrec.comp Primrec.fst)
  have hright : Primrec fun code :
      (TagNavigationCode numTags ⊕ MarkerShiftCode numTags) =>
      match code with
      | .inl _ => (Target.anyTag : Target numTags)
      | .inr shift =>
          (Target.boundary shift.1.expected : Target numTags) := by
    exact (Primrec.sumCasesOn Primrec.id
      (htag.comp Primrec.snd).to₂
      (hshift.comp Primrec.snd).to₂).of_eq fun code => by
        cases code <;> rfl
  have hall : Primrec fun code : CommandCode numTags =>
      match code with
      | .inl boundary =>
          (Target.boundary boundary.1 : Target numTags)
      | .inr rest =>
          match rest with
          | .inl _ => (Target.anyTag : Target numTags)
          | .inr shift =>
              (Target.boundary shift.1.expected : Target numTags) := by
    exact (Primrec.sumCasesOn Primrec.id
      (hboundary.comp Primrec.snd).to₂
      (hright.comp Primrec.snd).to₂).of_eq fun code => by
        cases code <;> rfl
  exact (hall.comp command_equivCode_primrec).of_eq fun command => by
    cases command <;> rfl

/-- The search direction selected by a varying command is primitive
recursive. -/
theorem Command.searchDirection_primrec {numTags : Nat} :
    Primrec (@Command.searchDirection numTags) := by
  have hboundary : Primrec fun code : BoundaryNavigationCode numTags =>
      code.2.1 := Primrec.fst.comp Primrec.snd
  have htag : Primrec fun code : TagNavigationCode numTags =>
      code.1 := Primrec.fst
  have hshift : Primrec fun code : MarkerShiftCode numTags =>
      code.1.searchDirection :=
    move_searchDirection_primrec.comp Primrec.fst
  have hright : Primrec fun code :
      (TagNavigationCode numTags ⊕ MarkerShiftCode numTags) =>
      match code with
      | .inl tag => tag.1
      | .inr shift => shift.1.searchDirection := by
    exact (Primrec.sumCasesOn Primrec.id
      (htag.comp Primrec.snd).to₂
      (hshift.comp Primrec.snd).to₂).of_eq fun code => by
        cases code <;> rfl
  have hall : Primrec fun code : CommandCode numTags =>
      match code with
      | .inl boundary => boundary.2.1
      | .inr rest =>
          match rest with
          | .inl tag => tag.1
          | .inr shift => shift.1.searchDirection := by
    exact (Primrec.sumCasesOn Primrec.id
      (hboundary.comp Primrec.snd).to₂
      (hright.comp Primrec.snd).to₂).of_eq fun code => by
        cases code <;> rfl
  exact (hall.comp command_equivCode_primrec).of_eq fun command => by
    cases command <;> rfl

/-- The external success state selected by a varying command is primitive
recursive. -/
theorem Command.successState_primrec {numTags : Nat} :
    Primrec (@Command.successState numTags) := by
  have hboundary : Primrec fun code : BoundaryNavigationCode numTags =>
      code.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have htag : Primrec fun code : TagNavigationCode numTags =>
      code.2.1 := Primrec.fst.comp Primrec.snd
  have hshift : Primrec fun code : MarkerShiftCode numTags =>
      code.2.1 := Primrec.fst.comp Primrec.snd
  have hright : Primrec fun code :
      (TagNavigationCode numTags ⊕ MarkerShiftCode numTags) =>
      match code with
      | .inl tag => tag.2.1
      | .inr shift => shift.2.1 := by
    exact (Primrec.sumCasesOn Primrec.id
      (htag.comp Primrec.snd).to₂
      (hshift.comp Primrec.snd).to₂).of_eq fun code => by
        cases code <;> rfl
  have hall : Primrec fun code : CommandCode numTags =>
      match code with
      | .inl boundary => boundary.2.2.1
      | .inr rest =>
          match rest with
          | .inl tag => tag.2.1
          | .inr shift => shift.2.1 := by
    exact (Primrec.sumCasesOn Primrec.id
      (hboundary.comp Primrec.snd).to₂
      (hright.comp Primrec.snd).to₂).of_eq fun code => by
        cases code <;> rfl
  exact (hall.comp command_equivCode_primrec).of_eq fun command => by
    cases command <;> rfl

/-- The physical return tag selected by a varying command is primitive
recursive. -/
theorem Command.returnTag_primrec {numTags : Nat} :
    Primrec (@Command.returnTag numTags) := by
  have hboundary : Primrec fun code : BoundaryNavigationCode numTags =>
      code.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have htag : Primrec fun code : TagNavigationCode numTags =>
      code.2.2 := Primrec.snd.comp Primrec.snd
  have hshift : Primrec fun code : MarkerShiftCode numTags =>
      code.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hright : Primrec fun code :
      (TagNavigationCode numTags ⊕ MarkerShiftCode numTags) =>
      match code with
      | .inl tag => tag.2.2
      | .inr shift => shift.2.2.1 := by
    exact (Primrec.sumCasesOn Primrec.id
      (htag.comp Primrec.snd).to₂
      (hshift.comp Primrec.snd).to₂).of_eq fun code => by
        cases code <;> rfl
  have hall : Primrec fun code : CommandCode numTags =>
      match code with
      | .inl boundary => boundary.2.2.2.1
      | .inr rest =>
          match rest with
          | .inl tag => tag.2.2
          | .inr shift => shift.2.2.1 := by
    exact (Primrec.sumCasesOn Primrec.id
      (hboundary.comp Primrec.snd).to₂
      (hright.comp Primrec.snd).to₂).of_eq fun code => by
        cases code <;> rfl
  exact (hall.comp command_equivCode_primrec).of_eq fun command => by
    cases command <;> rfl

/-! ## Uniform command continuations -/

private theorem launchState_primrec :
    Primrec fun input : Nat × Nat => launchState input.1 input.2 := by
  exact (Primrec.nat_add.comp Primrec.snd
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 3))).of_eq fun _ => rfl

private theorem foundState_primrec :
    Primrec fun input : Nat × Nat => foundState input.1 input.2 := by
  exact (Primrec.nat_add.comp Primrec.snd
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))).of_eq fun _ => rfl

private theorem clearState_primrec :
    Primrec fun input : Nat × Nat => clearState input.1 input.2 := by
  exact (Primrec.nat_add.comp Primrec.snd
    ((Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)))
      (Primrec.const 3)))).of_eq fun _ => rfl

private theorem verifyState_primrec :
    Primrec fun input : Nat × Nat => verifyState input.1 input.2 :=
  Primrec.succ.comp clearState_primrec

private theorem departState_primrec :
    Primrec fun input : Nat × Nat => departState input.1 input.2 := by
  exact (Primrec.nat_add.comp clearState_primrec (Primrec.const 2)).of_eq
    fun _ => rfl

private theorem resumeState_primrec :
    Primrec fun input : Nat × Nat => resumeState input.1 input.2 := by
  exact (Primrec.nat_add.comp clearState_primrec (Primrec.const 3)).of_eq
    fun _ => rfl

/-- The collision-preserving rule family is primitive recursive in its two
control states. -/
theorem collisionRules_primrec {numTags : Nat} :
    Primrec fun input : FiniteTM0.State × FiniteTM0.State =>
      collisionRules (numTags := numTags) input.1 input.2 := by
  have hrule : Primrec₂ fun input :
      FiniteTM0.State × FiniteTM0.State => fun symbol : Symbol numTags =>
      FiniteTM0.Rule.mk input.1 symbol input.2 (.write symbol) := by
    apply Primrec₂.mk
    apply rule_primrec
    · exact Primrec.fst.comp Primrec.fst
    · exact Primrec.snd
    · exact Primrec.snd.comp Primrec.fst
    · exact writeAction_primrec Primrec.snd
  exact Primrec.list_map (Primrec.const (nonblankSymbols numTags)) hrule

private theorem optionalCollisionRules_primrec {numTags : Nat} :
    Primrec fun input : FiniteTM0.State × Option FiniteTM0.State =>
      match input.2 with
      | none => []
      | some collision =>
          collisionRules (numTags := numTags) input.1 collision := by
  have hsome : Primrec₂
      (fun input : FiniteTM0.State × Option FiniteTM0.State =>
        fun collision : FiniteTM0.State =>
          collisionRules (numTags := numTags) input.1 collision) := by
    apply Primrec₂.mk
    exact collisionRules_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact (Primrec.option_casesOn Primrec.snd (Primrec.const []) hsome).of_eq
    fun input => by cases input.2 <;> rfl

private def launchRule {numTags : Nat} (radius offset sharedCore : Nat)
    (command : Command numTags) : FiniteTM0.Rule (AlphabetSize numTags) :=
  FiniteTM0.Rule.mk (launchState radius offset) blankSymbol sharedCore
    (.write (tagSymbol command.returnTag))

private def resumeRule {numTags : Nat} (radius offset : Nat)
    (command : Command numTags) : FiniteTM0.Rule (AlphabetSize numTags) :=
  FiniteTM0.Rule.mk (resumeState radius offset) blankSymbol
    (entryState radius offset)
    (liftAction (MarkerMachine.moveAction command.searchDirection))

private def continuationMiddle {numTags : Nat} (radius offset : Nat) :
    Command numTags → FiniteTM0.Table (AlphabetSize numTags)
  | .boundaryNavigation expected _ successState _ .preserve =>
      targetRules (foundState radius offset) successState (.boundary expected)
  | .boundaryNavigation expected _ successState _ (.erase none) =>
      [FiniteTM0.Rule.mk (foundState radius offset)
        (boundarySymbol expected) successState (.write blankSymbol)]
  | .boundaryNavigation expected _ successState _ (.erase (some departure)) =>
      [ FiniteTM0.Rule.mk (foundState radius offset)
          (boundarySymbol expected) (departState radius offset)
          (.write blankSymbol)
      , FiniteTM0.Rule.mk (departState radius offset) blankSymbol successState
          (liftAction (MarkerMachine.moveAction departure))
      ]
  | .tagNavigation _ successState _ =>
      targetRules (foundState radius offset) successState .anyTag
  | .markerShift move successState _ departure collisionState =>
      let verifyTarget := match departure with
        | none => successState
        | some _ => departState radius offset
      let collisions := match collisionState with
        | none => []
        | some collision => collisionRules (verifyState radius offset) collision
      let departureRules := match departure with
        | none => []
        | some direction =>
            [FiniteTM0.Rule.mk (departState radius offset)
              (boundarySymbol move.expected) successState
              (liftAction (MarkerMachine.moveAction direction))]
      [ FiniteTM0.Rule.mk (foundState radius offset)
          (boundarySymbol move.expected) (clearState radius offset)
          (.write blankSymbol)
      , FiniteTM0.Rule.mk (clearState radius offset) blankSymbol
          (verifyState radius offset)
          (liftAction (MarkerMachine.moveAction move.shiftDirection))
      , FiniteTM0.Rule.mk (verifyState radius offset) blankSymbol
          verifyTarget (.write (boundarySymbol move.expected))
      ] ++ collisions ++ departureRules

private theorem continuationTable_eq {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags) :
    continuationTable radius offset sharedCore command =
      [launchRule radius offset sharedCore command] ++
        continuationMiddle radius offset command ++
          [resumeRule radius offset command] := by
  cases command with
  | boundaryNavigation expected direction success tag action =>
      cases action with
      | preserve => rfl
      | erase departure => cases departure <;> rfl
  | tagNavigation => rfl
  | markerShift move success tag departure collision =>
      cases departure <;> cases collision <;> rfl

private abbrev ContinuationInput (numTags : Nat) :=
  Nat × Nat × Nat × Command numTags

private theorem launchRule_primrec {numTags : Nat} :
    Primrec fun input : ContinuationInput numTags =>
      launchRule input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  apply rule_primrec
  · exact launchState_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  · exact Primrec.const (blankSymbol (numTags := numTags))
  · exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  · exact writeAction_primrec
      (tagSymbol_primrec.comp
        (Command.returnTag_primrec.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

private theorem resumeRule_primrec {numTags : Nat} :
    Primrec fun input : ContinuationInput numTags =>
      resumeRule input.1 input.2.1 input.2.2.2 := by
  apply rule_primrec
  · exact resumeState_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  · exact Primrec.const (blankSymbol (numTags := numTags))
  · exact Primrec.fst.comp Primrec.snd
  · exact liftAction_primrec.comp
      (moveAction_primrec.comp
        (Command.searchDirection_primrec.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

private abbrev BoundaryMiddleInput (numTags : Nat) :=
  Nat × Nat × BoundaryNavigationCode numTags

set_option maxHeartbeats 800000 in
private theorem boundaryMiddle_primrec {numTags : Nat} :
    Primrec fun input : BoundaryMiddleInput numTags =>
      continuationMiddle input.1 input.2.1
        (.boundaryNavigation input.2.2.1 input.2.2.2.1
          input.2.2.2.2.1 input.2.2.2.2.2.1 input.2.2.2.2.2.2) := by
  have hradiusOffset : Primrec fun input : BoundaryMiddleInput numTags =>
      (input.1, input.2.1) :=
    Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hfound : Primrec fun input : BoundaryMiddleInput numTags =>
      foundState input.1 input.2.1 :=
    foundState_primrec.comp hradiusOffset
  have hdepart : Primrec fun input : BoundaryMiddleInput numTags =>
      departState input.1 input.2.1 :=
    departState_primrec.comp hradiusOffset
  have hexpected : Primrec fun input : BoundaryMiddleInput numTags =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hsuccess : Primrec fun input : BoundaryMiddleInput numTags =>
      input.2.2.2.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hactionCode : Primrec fun input : BoundaryMiddleInput numTags =>
      NavigationAction.equivCode input.2.2.2.2.2.2 :=
    (Primrec.of_equiv (e := NavigationAction.equivCode)).comp
      (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hpreserve : Primrec fun input : BoundaryMiddleInput numTags =>
      targetRules (numTags := numTags) (foundState input.1 input.2.1)
        input.2.2.2.2.1
        (Target.boundary input.2.2.1 : Target numTags) :=
    targetRules_primrec.comp
      (Primrec.pair hfound
        (Primrec.pair hsuccess
          (targetBoundary_primrec (numTags := numTags) |>.comp hexpected)))
  have heraseNone : Primrec fun input : BoundaryMiddleInput numTags =>
      [FiniteTM0.Rule.mk (foundState input.1 input.2.1)
        (boundarySymbol (numTags := numTags) input.2.2.1)
        input.2.2.2.2.1
        (.write (blankSymbol (numTags := numTags)))] := by
    apply singleton_primrec
    apply rule_primrec
    · exact hfound
    · exact boundarySymbol_primrec.comp hexpected
    · exact hsuccess
    · exact Primrec.const
        (FiniteTM0.Action.write (blankSymbol (numTags := numTags)))
  have heraseSome : Primrec₂ fun input : BoundaryMiddleInput numTags =>
      fun departure : Turing.Dir =>
      [ FiniteTM0.Rule.mk (foundState input.1 input.2.1)
          (boundarySymbol (numTags := numTags) input.2.2.1)
          (departState input.1 input.2.1)
          (.write (blankSymbol (numTags := numTags)))
      , FiniteTM0.Rule.mk (departState input.1 input.2.1)
          (blankSymbol (numTags := numTags))
          input.2.2.2.2.1
          (liftAction (numTags := numTags)
            (MarkerMachine.moveAction departure))
      ] := by
    apply Primrec₂.mk
    have hfirst : Primrec fun pair :
        BoundaryMiddleInput numTags × Turing.Dir =>
        FiniteTM0.Rule.mk (foundState pair.1.1 pair.1.2.1)
          (boundarySymbol (numTags := numTags) pair.1.2.2.1)
          (departState pair.1.1 pair.1.2.1)
          (.write (blankSymbol (numTags := numTags))) := by
      apply rule_primrec
      · exact hfound.comp Primrec.fst
      · exact (boundarySymbol_primrec.comp hexpected).comp Primrec.fst
      · exact hdepart.comp Primrec.fst
      · exact Primrec.const
          (FiniteTM0.Action.write (blankSymbol (numTags := numTags)))
    have hsecond : Primrec fun pair :
        BoundaryMiddleInput numTags × Turing.Dir =>
        FiniteTM0.Rule.mk (departState pair.1.1 pair.1.2.1)
          (blankSymbol (numTags := numTags))
          pair.1.2.2.2.2.1
          (liftAction (numTags := numTags)
            (MarkerMachine.moveAction pair.2)) := by
      apply rule_primrec
      · exact hdepart.comp Primrec.fst
      · exact Primrec.const (blankSymbol (numTags := numTags))
      · exact hsuccess.comp Primrec.fst
      · exact liftAction_primrec.comp
          (moveAction_primrec.comp Primrec.snd)
    exact Primrec.list_cons.comp hfirst
      (Primrec.list_cons.comp hsecond (Primrec.const []))
  have herase : Primrec₂ fun input : BoundaryMiddleInput numTags =>
      fun departure : Option Turing.Dir =>
      match departure with
      | none =>
          [FiniteTM0.Rule.mk (foundState input.1 input.2.1)
            (boundarySymbol (numTags := numTags) input.2.2.1)
            input.2.2.2.2.1
            (.write (blankSymbol (numTags := numTags)))]
      | some direction =>
          [ FiniteTM0.Rule.mk (foundState input.1 input.2.1)
              (boundarySymbol (numTags := numTags) input.2.2.1)
              (departState input.1 input.2.1)
              (.write (blankSymbol (numTags := numTags)))
          , FiniteTM0.Rule.mk (departState input.1 input.2.1)
              (blankSymbol (numTags := numTags))
              input.2.2.2.2.1
              (liftAction (numTags := numTags)
                (MarkerMachine.moveAction direction))
          ] := by
    apply Primrec₂.mk
    exact (Primrec.option_casesOn Primrec.snd
      (heraseNone.comp Primrec.fst)
      (heraseSome.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)).of_eq fun pair => by
          cases pair.2 <;> rfl
  exact (Primrec.option_casesOn hactionCode hpreserve herase).of_eq
    fun input => by
      cases input.2.2.2.2.2.2 with
      | preserve => rfl
      | erase departure => cases departure <;> rfl

private abbrev TagMiddleInput (numTags : Nat) :=
  Nat × Nat × TagNavigationCode numTags

private theorem tagMiddle_primrec {numTags : Nat} :
    Primrec fun input : TagMiddleInput numTags =>
      continuationMiddle input.1 input.2.1
        (.tagNavigation input.2.2.1 input.2.2.2.1 input.2.2.2.2) := by
  exact targetRules_primrec.comp
    (Primrec.pair
      (foundState_primrec.comp
        (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.const (Target.anyTag : Target numTags))))

private abbrev ShiftMiddleInput (numTags : Nat) :=
  Nat × Nat × MarkerShiftCode numTags

private def shiftBase {numTags : Nat} (radius offset : Nat)
    (code : MarkerShiftCode numTags) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  let verifyTarget := match code.2.2.2.1 with
    | none => code.2.1
    | some _ => departState radius offset
  [ FiniteTM0.Rule.mk (foundState radius offset)
      (boundarySymbol code.1.expected) (clearState radius offset)
      (.write blankSymbol)
  , FiniteTM0.Rule.mk (clearState radius offset) blankSymbol
      (verifyState radius offset)
      (liftAction (MarkerMachine.moveAction code.1.shiftDirection))
  , FiniteTM0.Rule.mk (verifyState radius offset) blankSymbol
      verifyTarget (.write (boundarySymbol code.1.expected))
  ]

private def shiftCollisions {numTags : Nat} (radius offset : Nat)
    (code : MarkerShiftCode numTags) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  match code.2.2.2.2 with
  | none => []
  | some collision => collisionRules (verifyState radius offset) collision

private def shiftDepartureRules {numTags : Nat} (radius offset : Nat)
    (code : MarkerShiftCode numTags) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  match code.2.2.2.1 with
  | none => []
  | some direction =>
      [FiniteTM0.Rule.mk (departState radius offset)
        (boundarySymbol code.1.expected) code.2.1
        (liftAction (MarkerMachine.moveAction direction))]

set_option maxHeartbeats 2000000 in
private theorem shiftFirstRule_primrec {numTags : Nat} :
    Primrec fun input : ShiftMiddleInput numTags =>
      FiniteTM0.Rule.mk (foundState input.1 input.2.1)
        (boundarySymbol (numTags := numTags) input.2.2.1.expected)
        (clearState input.1 input.2.1)
        (.write (blankSymbol (numTags := numTags))) := by
  have hradiusOffset : Primrec fun input : ShiftMiddleInput numTags =>
      (input.1, input.2.1) :=
    Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hfound : Primrec fun input : ShiftMiddleInput numTags =>
      foundState input.1 input.2.1 :=
    foundState_primrec.comp hradiusOffset
  have hclear : Primrec fun input : ShiftMiddleInput numTags =>
      clearState input.1 input.2.1 :=
    clearState_primrec.comp hradiusOffset
  have hmove : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hexpected : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.1.expected :=
    move_expected_primrec.comp hmove
  apply rule_primrec
  · exact hfound
  · exact boundarySymbol_primrec.comp hexpected
  · exact hclear
  · exact Primrec.const
      (FiniteTM0.Action.write (blankSymbol (numTags := numTags)))

set_option maxHeartbeats 2000000 in
private theorem shiftSecondRule_primrec {numTags : Nat} :
    Primrec fun input : ShiftMiddleInput numTags =>
      FiniteTM0.Rule.mk (clearState input.1 input.2.1)
        (blankSymbol (numTags := numTags))
        (verifyState input.1 input.2.1)
        (liftAction (numTags := numTags)
          (MarkerMachine.moveAction input.2.2.1.shiftDirection)) := by
  have hradiusOffset : Primrec fun input : ShiftMiddleInput numTags =>
      (input.1, input.2.1) :=
    Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hclear : Primrec fun input : ShiftMiddleInput numTags =>
      clearState input.1 input.2.1 :=
    clearState_primrec.comp hradiusOffset
  have hverify : Primrec fun input : ShiftMiddleInput numTags =>
      verifyState input.1 input.2.1 :=
    verifyState_primrec.comp hradiusOffset
  have hmove : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hshiftDirection : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.1.shiftDirection :=
    move_shiftDirection_primrec.comp hmove
  apply rule_primrec
  · exact hclear
  · exact Primrec.const (blankSymbol (numTags := numTags))
  · exact hverify
  · exact liftAction_primrec.comp
      (moveAction_primrec.comp hshiftDirection)

set_option maxHeartbeats 3000000 in
private theorem shiftThirdRule_primrec {numTags : Nat} :
    Primrec fun input : ShiftMiddleInput numTags =>
      FiniteTM0.Rule.mk (verifyState input.1 input.2.1)
        (blankSymbol (numTags := numTags))
        (match input.2.2.2.2.2.1 with
          | none => input.2.2.2.1
          | some _ => departState input.1 input.2.1)
        (.write (boundarySymbol (numTags := numTags)
          input.2.2.1.expected)) := by
  have hradiusOffset : Primrec fun input : ShiftMiddleInput numTags =>
      (input.1, input.2.1) :=
    Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hverify : Primrec fun input : ShiftMiddleInput numTags =>
      verifyState input.1 input.2.1 :=
    verifyState_primrec.comp hradiusOffset
  have hdepart : Primrec fun input : ShiftMiddleInput numTags =>
      departState input.1 input.2.1 :=
    departState_primrec.comp hradiusOffset
  have hmove : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hexpected : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.1.expected :=
    move_expected_primrec.comp hmove
  have hsuccess : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hdeparture : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.2.2.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hverifyTarget : Primrec fun input : ShiftMiddleInput numTags =>
      match input.2.2.2.2.2.1 with
      | none => input.2.2.2.1
      | some _ => departState input.1 input.2.1 := by
    exact (Primrec.option_casesOn hdeparture hsuccess
      (hdepart.comp Primrec.fst).to₂).of_eq fun input => by
        cases input.2.2.2.2.2.1 <;> rfl
  apply rule_primrec
  · exact hverify
  · exact Primrec.const (blankSymbol (numTags := numTags))
  · exact hverifyTarget
  · exact writeAction_primrec
      (boundarySymbol_primrec.comp hexpected)

set_option maxHeartbeats 1000000 in
private theorem shiftBase_primrec {numTags : Nat} :
    Primrec fun input : ShiftMiddleInput numTags =>
      shiftBase input.1 input.2.1 input.2.2 := by
  have hnil : Primrec fun _ : ShiftMiddleInput numTags =>
      ([] : FiniteTM0.Table (AlphabetSize numTags)) :=
    Primrec.const []
  have hthird := Primrec.list_cons.comp
    (@shiftThirdRule_primrec numTags) hnil
  have hsecond := Primrec.list_cons.comp
    (@shiftSecondRule_primrec numTags) hthird
  have hbase := Primrec.list_cons.comp
    (@shiftFirstRule_primrec numTags) hsecond
  exact hbase.of_eq fun input => by
    rcases input with ⟨radius, offset, move, success, tag, departure, collision⟩
    cases departure <;> rfl

set_option maxHeartbeats 2000000 in
private theorem shiftCollisions_primrec {numTags : Nat} :
    Primrec fun input : ShiftMiddleInput numTags =>
      shiftCollisions input.1 input.2.1 input.2.2 := by
  have hradiusOffset : Primrec fun input : ShiftMiddleInput numTags =>
      (input.1, input.2.1) :=
    Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hverify : Primrec fun input : ShiftMiddleInput numTags =>
      verifyState input.1 input.2.1 :=
    verifyState_primrec.comp hradiusOffset
  have hcollision : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.2.2.2.2 :=
    Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (optionalCollisionRules_primrec.comp
    (Primrec.pair hverify hcollision)).of_eq fun input => by
    rcases input with ⟨radius, offset, move, success, tag, departure, collision⟩
    cases collision <;> rfl

set_option maxHeartbeats 2000000 in
private theorem shiftDepartureRules_primrec {numTags : Nat} :
    Primrec fun input : ShiftMiddleInput numTags =>
      shiftDepartureRules input.1 input.2.1 input.2.2 := by
  have hradiusOffset : Primrec fun input : ShiftMiddleInput numTags =>
      (input.1, input.2.1) :=
    Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hdepart : Primrec fun input : ShiftMiddleInput numTags =>
      departState input.1 input.2.1 :=
    departState_primrec.comp hradiusOffset
  have hmove : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hexpected : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.1.expected :=
    move_expected_primrec.comp hmove
  have hsuccess : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hdeparture : Primrec fun input : ShiftMiddleInput numTags =>
      input.2.2.2.2.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hdepartureSome : Primrec₂ fun input : ShiftMiddleInput numTags =>
      fun direction : Turing.Dir =>
        [FiniteTM0.Rule.mk (departState input.1 input.2.1)
          (boundarySymbol (numTags := numTags) input.2.2.1.expected)
          input.2.2.2.1
          (liftAction (numTags := numTags)
            (MarkerMachine.moveAction direction))] := by
    apply Primrec₂.mk
    apply singleton_primrec
    apply rule_primrec
    · exact hdepart.comp Primrec.fst
    · exact (boundarySymbol_primrec.comp hexpected).comp Primrec.fst
    · exact hsuccess.comp Primrec.fst
    · exact liftAction_primrec.comp
        (moveAction_primrec.comp Primrec.snd)
  have hdepartureRules : Primrec fun input : ShiftMiddleInput numTags =>
      match input.2.2.2.2.2.1 with
      | none => []
      | some direction =>
          [FiniteTM0.Rule.mk (departState input.1 input.2.1)
            (boundarySymbol (numTags := numTags) input.2.2.1.expected)
            input.2.2.2.1
            (liftAction (numTags := numTags)
              (MarkerMachine.moveAction direction))] := by
    exact (Primrec.option_casesOn hdeparture (Primrec.const [])
      hdepartureSome).of_eq fun input => by
        cases input.2.2.2.2.2.1 <;> rfl
  exact hdepartureRules.of_eq fun input => by
    rcases input with ⟨radius, offset, move, success, tag, departure, collision⟩
    cases departure <;> rfl

set_option maxHeartbeats 1000000 in
private theorem shiftMiddle_primrec {numTags : Nat} :
    Primrec fun input : ShiftMiddleInput numTags =>
      continuationMiddle input.1 input.2.1
        (.markerShift input.2.2.1 input.2.2.2.1 input.2.2.2.2.1
          input.2.2.2.2.2.1 input.2.2.2.2.2.2) := by
  exact (Primrec.list_append.comp
    (Primrec.list_append.comp shiftBase_primrec shiftCollisions_primrec)
    shiftDepartureRules_primrec).of_eq fun input => by
      rcases input with ⟨radius, offset, move, success, tag, departure, collision⟩
      cases departure <;> cases collision <;> rfl

private abbrev MiddleInput (numTags : Nat) :=
  Nat × Nat × Command numTags

set_option maxHeartbeats 800000 in
private theorem continuationMiddle_primrec {numTags : Nat} :
    Primrec fun input : MiddleInput numTags =>
      continuationMiddle input.1 input.2.1 input.2.2 := by
  have hcode : Primrec fun input : MiddleInput numTags =>
      Command.equivCode input.2.2 :=
    command_equivCode_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hboundary : Primrec₂ fun input : MiddleInput numTags =>
      fun code : BoundaryNavigationCode numTags =>
        continuationMiddle input.1 input.2.1
          (.boundaryNavigation code.1 code.2.1 code.2.2.1
            code.2.2.2.1 code.2.2.2.2) := by
    apply Primrec₂.mk
    exact boundaryMiddle_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  have htag : Primrec₂ fun input : MiddleInput numTags =>
      fun code : TagNavigationCode numTags =>
        continuationMiddle input.1 input.2.1
          (.tagNavigation code.1 code.2.1 code.2.2) := by
    apply Primrec₂.mk
    exact tagMiddle_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  have hshift : Primrec₂ fun input : MiddleInput numTags =>
      fun code : MarkerShiftCode numTags =>
        continuationMiddle input.1 input.2.1
          (.markerShift code.1 code.2.1 code.2.2.1
            code.2.2.2.1 code.2.2.2.2) := by
    apply Primrec₂.mk
    exact shiftMiddle_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  have hright : Primrec₂ fun input : MiddleInput numTags =>
      fun code : TagNavigationCode numTags ⊕ MarkerShiftCode numTags =>
        match code with
        | .inl tag => continuationMiddle input.1 input.2.1
            (.tagNavigation tag.1 tag.2.1 tag.2.2)
        | .inr shift => continuationMiddle input.1 input.2.1
            (.markerShift shift.1 shift.2.1 shift.2.2.1
              shift.2.2.2.1 shift.2.2.2.2) := by
    apply Primrec₂.mk
    exact (Primrec.sumCasesOn Primrec.snd
      (htag.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
      (hshift.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)).of_eq fun pair => by
          cases pair.2 <;> rfl
  exact (Primrec.sumCasesOn hcode hboundary hright).of_eq fun input => by
    cases input.2.2 <;> rfl

/-- One command's continuation-and-launch rule table is primitive recursive
in its radius, state offset, shared core entry, and command descriptor. -/
theorem continuationTable_primrec {numTags : Nat} :
    Primrec fun input : ContinuationInput numTags =>
      continuationTable input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have hlaunch := singleton_primrec
    (launchRule_primrec (numTags := numTags))
  have hmiddle : Primrec fun input : ContinuationInput numTags =>
      continuationMiddle input.1 input.2.1 input.2.2.2 :=
    continuationMiddle_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hresume := singleton_primrec
    (resumeRule_primrec (numTags := numTags))
  exact (Primrec.list_append.comp
    (Primrec.list_append.comp hlaunch hmiddle) hresume).of_eq fun input =>
      (continuationTable_eq input.1 input.2.1 input.2.2.1 input.2.2.2).symm

private abbrev PrivateControllerInput (numTags : Nat) :=
  Nat × Nat × Command numTags

/-- Relocating the native controller for one varying command is primitive
recursive. -/
theorem privateControllerTable_primrec {numTags : Nat} :
    Primrec fun input : PrivateControllerInput numTags =>
      privateControllerTable input.1 input.2.1 input.2.2 := by
  have hlocal : Primrec fun input : PrivateControllerInput numTags =>
      nativeLocalTable input.1 input.2.2.target
        input.2.2.searchDirection :=
    nativeLocalTable_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (Command.target_primrec.comp (Primrec.snd.comp Primrec.snd))
          (Command.searchDirection_primrec.comp
            (Primrec.snd.comp Primrec.snd))))
  exact FiniteTM0Program.relocate_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd) hlocal)

/-- A complete varying private command block is primitive recursive. -/
theorem commandTable_primrec {numTags : Nat} :
    Primrec fun input : ContinuationInput numTags =>
      commandTable input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  exact Primrec.list_append.comp continuationTable_primrec
    (privateControllerTable_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

/-! ## Primitive-recursive state layout -/

theorem blockWidth_primrec : Primrec blockWidth := by
  exact (Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp Primrec.id (Primrec.const 1)))
      (Primrec.const 3))
    (Primrec.const continuationWidth)).of_eq fun radius => rfl

theorem commandOffset_primrec :
    Primrec fun input : Nat × Nat × Nat =>
      commandOffset input.1 input.2.1 input.2.2 := by
  exact Primrec.nat_add.comp Primrec.fst
    (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd)
      (blockWidth_primrec.comp (Primrec.fst.comp Primrec.snd)))

theorem returnState_primrec {numTags : Nat} :
    Primrec fun input : Nat × Nat × List (Command numTags) × Turing.Dir =>
      returnState input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have hbase : Primrec fun input :
      Nat × Nat × List (Command numTags) × Turing.Dir => input.1 :=
    Primrec.fst
  have hradius : Primrec fun input :
      Nat × Nat × List (Command numTags) × Turing.Dir => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hcommands : Primrec fun input :
      Nat × Nat × List (Command numTags) × Turing.Dir => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hdirection : Primrec fun input :
      Nat × Nat × List (Command numTags) × Turing.Dir => input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hoffset : Primrec fun direction : Turing.Dir =>
      match direction with
      | .left => 0
      | .right => 1 :=
    Primrec.dom_finite _
  exact Primrec.nat_add.comp
    (commandOffset_primrec.comp
      (Primrec.pair hbase
        (Primrec.pair hradius (Primrec.list_length.comp hcommands))))
    (hoffset.comp hdirection)

theorem coreEntry_primrec {numTags : Nat} :
    Primrec fun input : Nat × Nat × List (Command numTags) =>
      coreEntry input.1 input.2.1 input.2.2 := by
  exact Primrec.nat_add.comp
    (commandOffset_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.const 2)

/-! ## Uniformly linking variable command lists -/

private def commandTablesFoldStep {numTags : Nat} (radius sharedCore : Nat)
    (accumulator : Nat × FiniteTM0.Table (AlphabetSize numTags))
    (command : Command numTags) :
    Nat × FiniteTM0.Table (AlphabetSize numTags) :=
  (accumulator.1 + blockWidth radius,
    accumulator.2 ++ commandTable radius accumulator.1 sharedCore command)

private def commandTablesFold {numTags : Nat} (radius sharedCore offset : Nat)
    (commands : List (Command numTags)) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  (commands.foldl (commandTablesFoldStep radius sharedCore) (offset, [])).2

private theorem commandTablesFold_eq {numTags : Nat}
    (radius sharedCore offset : Nat) (commands : List (Command numTags))
    (acc : FiniteTM0.Table (AlphabetSize numTags)) :
    (commands.foldl (commandTablesFoldStep radius sharedCore)
        (offset, acc)).2 =
      acc ++ commandTables radius sharedCore offset commands := by
  induction commands generalizing offset acc with
  | nil => simp [commandTables]
  | cons command commands ih =>
      simp only [List.foldl_cons, commandTablesFoldStep, commandTables]
      rw [ih]
      simp [List.append_assoc]

private abbrev CommandTablesInput (numTags : Nat) :=
  Nat × Nat × Nat × List (Command numTags)

set_option maxHeartbeats 800000 in
private theorem commandTablesFold_primrec {numTags : Nat} :
    Primrec fun input : CommandTablesInput numTags =>
      commandTablesFold input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have hcommands : Primrec fun input : CommandTablesInput numTags =>
      input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hinitial : Primrec fun input : CommandTablesInput numTags =>
      (input.2.2.1,
        ([] : FiniteTM0.Table (AlphabetSize numTags))) :=
    Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const [])
  have hstep : Primrec₂ fun input : CommandTablesInput numTags =>
      fun pair :
        (Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags =>
        commandTablesFoldStep input.1 input.2.1 pair.1 pair.2 := by
    apply Primrec₂.mk
    have hradius : Primrec fun pair : CommandTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hshared : Primrec fun pair : CommandTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hoffset : Primrec fun pair : CommandTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.2.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have hprefix : Primrec fun pair : CommandTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hcommand : Primrec fun pair : CommandTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.2.2 :=
      Primrec.snd.comp Primrec.snd
    have htable : Primrec fun pair : CommandTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        commandTable pair.1.1 pair.2.1.1 pair.1.2.1 pair.2.2 :=
      commandTable_primrec.comp
        (Primrec.pair hradius
          (Primrec.pair hoffset (Primrec.pair hshared hcommand)))
    exact Primrec.pair
      (Primrec.nat_add.comp hoffset (blockWidth_primrec.comp hradius))
      (Primrec.list_append.comp hprefix htable)
  have hfold : Primrec fun input : CommandTablesInput numTags =>
      input.2.2.2.foldl (commandTablesFoldStep input.1 input.2.1)
        (input.2.2.1, []) :=
    Primrec.list_foldl hcommands hinitial hstep
  exact Primrec.snd.comp hfold

/-- Linking a variable list of command blocks is primitive recursive in the
radius, shared core entry, initial offset, and the complete command list. -/
theorem commandTables_primrec {numTags : Nat} :
    Primrec fun input : CommandTablesInput numTags =>
      commandTables input.1 input.2.1 input.2.2.1 input.2.2.2 :=
  commandTablesFold_primrec.of_eq fun input => by
    rw [commandTablesFold]
    simpa using commandTablesFold_eq input.1 input.2.1 input.2.2.1
      input.2.2.2 ([] : FiniteTM0.Table (AlphabetSize numTags))

private def directionalReturn (states : Nat × Nat) :
    Turing.Dir → FiniteTM0.State
  | .left => states.1
  | .right => states.2

private theorem directionalReturn_primrec :
    Primrec fun input : (Nat × Nat) × Turing.Dir =>
      directionalReturn input.1 input.2 := by
  have hdirection : Primrec fun input : (Nat × Nat) × Turing.Dir =>
      dirEquivBool input.2 :=
    (Primrec.of_equiv (e := dirEquivBool)).comp Primrec.snd
  exact (Primrec.cond hdirection
    (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp Primrec.fst)).of_eq fun input => by
      cases input.2 <;> rfl

private def returnTableFoldStep {numTags : Nat} (radius : Nat)
    (sharedReturn : Nat × Nat)
    (accumulator : Nat × FiniteTM0.Table (AlphabetSize numTags))
    (command : Command numTags) :
    Nat × FiniteTM0.Table (AlphabetSize numTags) :=
  (accumulator.1 + blockWidth radius,
    accumulator.2 ++
      [FiniteTM0.Rule.mk
        (directionalReturn sharedReturn command.searchDirection)
        (tagSymbol command.returnTag)
        (resumeState radius accumulator.1) (.write blankSymbol)])

private def returnTableFold {numTags : Nat} (radius : Nat)
    (sharedReturn : Nat × Nat) (offset : Nat)
    (commands : List (Command numTags)) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  (commands.foldl (returnTableFoldStep radius sharedReturn) (offset, [])).2

private theorem returnTableFold_eq {numTags : Nat}
    (radius : Nat) (sharedReturn : Nat × Nat) (offset : Nat)
    (commands : List (Command numTags))
    (acc : FiniteTM0.Table (AlphabetSize numTags)) :
    (commands.foldl (returnTableFoldStep radius sharedReturn)
        (offset, acc)).2 =
      acc ++ returnTable radius (directionalReturn sharedReturn)
        offset commands := by
  induction commands generalizing offset acc with
  | nil => simp [returnTable]
  | cons command commands ih =>
      simp only [List.foldl_cons, returnTableFoldStep, returnTable]
      rw [ih]
      simp [List.append_assoc]

private abbrev ReturnTablesInput (numTags : Nat) :=
  Nat × (Nat × Nat) × Nat × List (Command numTags)

set_option maxHeartbeats 800000 in
private theorem returnTableFold_primrec {numTags : Nat} :
    Primrec fun input : ReturnTablesInput numTags =>
      returnTableFold input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have hcommands : Primrec fun input : ReturnTablesInput numTags =>
      input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hinitial : Primrec fun input : ReturnTablesInput numTags =>
      (input.2.2.1,
        ([] : FiniteTM0.Table (AlphabetSize numTags))) :=
    Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const [])
  have hstep : Primrec₂ fun input : ReturnTablesInput numTags =>
      fun pair :
        (Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags =>
        returnTableFoldStep input.1 input.2.1 pair.1 pair.2 := by
    apply Primrec₂.mk
    have hradius : Primrec fun pair : ReturnTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hshared : Primrec fun pair : ReturnTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hoffset : Primrec fun pair : ReturnTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.2.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have hprefix : Primrec fun pair : ReturnTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hcommand : Primrec fun pair : ReturnTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hreturnTag : Primrec fun pair : ReturnTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        pair.2.2.returnTag :=
      Command.returnTag_primrec.comp hcommand
    have hreturnState : Primrec fun pair : ReturnTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        directionalReturn pair.1.2.1 pair.2.2.searchDirection :=
      directionalReturn_primrec.comp
        (Primrec.pair hshared
          (Command.searchDirection_primrec.comp hcommand))
    have hrule : Primrec fun pair : ReturnTablesInput numTags ×
        ((Nat × FiniteTM0.Table (AlphabetSize numTags)) × Command numTags) =>
        FiniteTM0.Rule.mk
          (directionalReturn pair.1.2.1 pair.2.2.searchDirection)
          (tagSymbol pair.2.2.returnTag)
          (resumeState pair.1.1 pair.2.1.1)
          (.write (blankSymbol (numTags := numTags))) := by
      apply rule_primrec
      · exact hreturnState
      · exact tagSymbol_primrec.comp hreturnTag
      · exact resumeState_primrec.comp (Primrec.pair hradius hoffset)
      · exact Primrec.const
          (FiniteTM0.Action.write (blankSymbol (numTags := numTags)))
    exact Primrec.pair
      (Primrec.nat_add.comp hoffset (blockWidth_primrec.comp hradius))
      (Primrec.list_append.comp hprefix (singleton_primrec hrule))
  have hfold : Primrec fun input : ReturnTablesInput numTags =>
      input.2.2.2.foldl (returnTableFoldStep input.1 input.2.1)
        (input.2.2.1, []) :=
    Primrec.list_foldl hcommands hinitial hstep
  exact Primrec.snd.comp hfold

/-- The directional return dispatcher is primitive recursive in radius, its
left and right return states, initial offset, and the varying command list. -/
theorem returnTable_primrec {numTags : Nat} :
    Primrec fun input : ReturnTablesInput numTags =>
      returnTable input.1 (directionalReturn input.2.1)
        input.2.2.1 input.2.2.2 :=
  returnTableFold_primrec.of_eq fun input => by
    rw [returnTableFold]
    simpa using returnTableFold_eq input.1 input.2.1 input.2.2.1
      input.2.2.2 ([] : FiniteTM0.Table (AlphabetSize numTags))

private abbrev ControllerTableInput (numTags : Nat) :=
  Nat × Nat × List (Command numTags)

/-- The complete generated bounded controller is primitive recursive in its
base state, radius, and varying command list. -/
theorem controllerTable_primrec {numTags : Nat} :
    Primrec fun input : ControllerTableInput numTags =>
      controllerTable input.1 input.2.1 input.2.2 := by
  have hcommands : Primrec fun input : ControllerTableInput numTags =>
      input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hreturnLeft : Primrec fun input : ControllerTableInput numTags =>
      returnState input.1 input.2.1 input.2.2 .left :=
    returnState_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair hcommands (Primrec.const Turing.Dir.left))))
  have hreturnRight : Primrec fun input : ControllerTableInput numTags =>
      returnState input.1 input.2.1 input.2.2 .right :=
    returnState_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair hcommands (Primrec.const Turing.Dir.right))))
  have hcore : Primrec fun input : ControllerTableInput numTags =>
      coreEntry input.1 input.2.1 input.2.2 :=
    coreEntry_primrec
  have hprivate : Primrec fun input : ControllerTableInput numTags =>
      commandTables input.2.1
        (coreEntry input.1 input.2.1 input.2.2) input.1 input.2.2 :=
    commandTables_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair hcore (Primrec.pair Primrec.fst hcommands)))
  have hreturns : Primrec fun input : ControllerTableInput numTags =>
      returnTable input.2.1
        (returnState input.1 input.2.1 input.2.2) input.1 input.2.2 :=
    (returnTable_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.pair hreturnLeft hreturnRight)
          (Primrec.pair Primrec.fst hcommands)))).of_eq fun input => by
            congr 2
            funext direction
            cases direction <;> rfl
  exact Primrec.list_append.comp hprivate hreturns

private abbrev FullTableInput (numTags : Nat) :=
  Nat × Nat × List (Command numTags) ×
    FiniteTM0.Table (AlphabetSize numTags)

/-- Appending a varying finite nested core preserves primitive recursiveness:
the entire bounded-search table compiler is uniform. -/
theorem table_primrec {numTags : Nat} :
    Primrec fun input : FullTableInput numTags =>
      table input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  exact Primrec.list_append.comp
    (controllerTable_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

/-- Compositional form of `controllerTable_primrec`, suitable for a source
compiler whose parameters are themselves primitive recursive. -/
theorem controllerTable_primrec_of {alpha : Type*} [Primcodable alpha]
    {numTags : Nat}
    {base radius : alpha → Nat}
    {commands : alpha → List (Command numTags)}
    (hbase : Primrec base) (hradius : Primrec radius)
    (hcommands : Primrec commands) :
    Primrec fun input => controllerTable (base input) (radius input)
      (commands input) :=
  controllerTable_primrec.comp
    (Primrec.pair hbase (Primrec.pair hradius hcommands))

/-- Compositional uniform compiler theorem.  This is the main API used by
the counter-program compiler. -/
theorem table_primrec_of {alpha : Type*} [Primcodable alpha]
    {numTags : Nat}
    {base radius : alpha → Nat}
    {commands : alpha → List (Command numTags)}
    {core : alpha → FiniteTM0.Table (AlphabetSize numTags)}
    (hbase : Primrec base) (hradius : Primrec radius)
    (hcommands : Primrec commands) (hcore : Primrec core) :
    Primrec fun input => table (base input) (radius input)
      (commands input) (core input) :=
  table_primrec.comp
    (Primrec.pair hbase
      (Primrec.pair hradius (Primrec.pair hcommands hcore)))

/-- Computable form of the uniform table compiler. -/
theorem table_computable {numTags : Nat} :
    Computable fun input : FullTableInput numTags =>
      table input.1 input.2.1 input.2.2.1 input.2.2.2 :=
  (@table_primrec numTags).to_comp

/-- Compositional computability corollary for primitive-recursive compiler
inputs. -/
theorem table_computable_of {alpha : Type*} [Primcodable alpha]
    {numTags : Nat}
    {base radius : alpha → Nat}
    {commands : alpha → List (Command numTags)}
    {core : alpha → FiniteTM0.Table (AlphabetSize numTags)}
    (hbase : Primrec base) (hradius : Primrec radius)
    (hcommands : Primrec commands) (hcore : Primrec core) :
    Computable fun input => table (base input) (radius input)
      (commands input) (core input) :=
  (table_primrec_of hbase hradius hcommands hcore).to_comp

end

end BoundedMarkerProgram
end Hooper
end Kari
end LeanWang
