/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CanonicalInitializerProgram

/-!
# Uniform effectiveness of the canonical initializer

The semantic initializer is code dependent: the designated source code is
stored as the initial right-stack numeral, so the retreat distance and one
inter-boundary gap vary with that code.  This file proves that the generated
instruction list and finite transition table nevertheless vary computably
(indeed, primitive recursively) with the code.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CanonicalInitializerProgram

open Turing
open BoundedMarkerProgram

noncomputable section

private theorem replicate_primrec {α : Type*} [Primcodable α]
    (value : α) {length : Nat.Partrec.Code → Nat}
    (hlength : Primrec length) :
    Primrec fun c => List.replicate (length c) value := by
  have hmap : Primrec fun c : Nat.Partrec.Code =>
      (List.range (length c)).map fun _ => value :=
    Primrec.list_map (Primrec.list_range.comp hlength)
      (Primrec.const value).to₂
  exact hmap.of_eq fun c => by simp

private def placementPrefix {numTags : Nat} (growth : Turing.Dir)
    (tag : Fin numTags) : List (Instruction numTags) :=
  [ writeInstruction blankSymbol (tagSymbol tag)
  , moveInstruction (tagSymbol tag) growth
  , writeInstruction blankSymbol (boundarySymbol 0)
  , moveInstruction (boundarySymbol 0) growth
  , writeInstruction blankSymbol (boundarySymbol 1)
  , moveInstruction (boundarySymbol 1) growth
  ]

private def placementSuffix {numTags : Nat} (growth : Turing.Dir) :
    List (Instruction numTags) :=
  [ writeInstruction blankSymbol (boundarySymbol 2)
  , moveInstruction (boundarySymbol 2) growth
  , writeInstruction blankSymbol (boundarySymbol 3)
  , moveInstruction (boundarySymbol 3) growth
  , writeInstruction blankSymbol (boundarySymbol 4)
  ]

private theorem placementInstructions_eq {numTags : Nat}
    (c : Nat.Partrec.Code) (growth : Turing.Dir) (tag : Fin numTags) :
    placementInstructions c growth tag =
      placementPrefix growth tag ++
        List.replicate (inputGap c)
          (moveInstruction blankSymbol growth) ++
        placementSuffix growth := by
  simp [placementInstructions, placementPrefix, placementSuffix, advance]

/-- The tag-specific guarded initializer path is primitive recursive in the
designated source code. -/
theorem instructions_primrec {numTags : Nat}
    (growth : Turing.Dir) (tag : Fin numTags) :
    Primrec fun c : Nat.Partrec.Code => instructions c growth tag := by
  have hinputGap : Primrec inputGap := by
    exact StackEncoding.sourceInitialRegisters_right_primrec
  have hradius : Primrec fun c : Nat.Partrec.Code =>
      NestingMachine.bound (CanonicalInitializer.radius c) :=
    Primrec.nat_add.comp CanonicalInitializer.radius_primrec
      (Primrec.const 1)
  have hretreat : Primrec fun c : Nat.Partrec.Code =>
      List.replicate
        (NestingMachine.bound (CanonicalInitializer.radius c))
        (moveInstruction (numTags := numTags) blankSymbol
          (NestingMachine.opposite growth)) :=
    replicate_primrec _ hradius
  have hgap : Primrec fun c : Nat.Partrec.Code =>
      List.replicate (inputGap c)
        (moveInstruction (numTags := numTags) blankSymbol growth) :=
    replicate_primrec _ hinputGap
  have hplacement : Primrec fun c : Nat.Partrec.Code =>
      placementInstructions c growth tag := by
    have hprefixed : Primrec fun c : Nat.Partrec.Code =>
        placementPrefix growth tag ++
          List.replicate (inputGap c)
            (moveInstruction (numTags := numTags) blankSymbol growth) :=
      Primrec.list_append.comp (Primrec.const (placementPrefix growth tag))
        hgap
    exact (Primrec.list_append.comp hprefixed
      (Primrec.const (placementSuffix growth))).of_eq fun c => by
        rw [placementInstructions_eq]
  exact (Primrec.list_append.comp hretreat hplacement).of_eq fun c => by
    rfl

/-- Computable form of `instructions_primrec`. -/
theorem instructions_computable {numTags : Nat}
    (growth : Turing.Dir) (tag : Fin numTags) :
    Computable fun c : Nat.Partrec.Code => instructions c growth tag :=
  (instructions_primrec growth tag).to_comp

/-- The uniform private-path width is primitive recursive in the source
code. -/
theorem pathWidth_primrec : Primrec pathWidth := by
  exact (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      CanonicalInitializer.radius_primrec)
    (Primrec.const 7)).of_eq fun c => rfl

/-- The source-state width of a complete tag block is primitive recursive. -/
theorem tagBlockWidth_primrec : Primrec tagBlockWidth := by
  exact Primrec.nat_add.comp pathWidth_primrec (Primrec.const 1)

/-- A fixed tag's private-path offset is primitive recursive whenever the
shared entry is. -/
theorem pathOffset_primrec {numTags : Nat}
    (tag : Fin numTags) {sharedEntry : Nat.Partrec.Code → FiniteTM0.State}
    (hshared : Primrec sharedEntry) :
    Primrec fun c => pathOffset (sharedEntry c) c tag := by
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp hshared (Primrec.const 1))
    (Primrec.nat_mul.comp (Primrec.const tag.val) tagBlockWidth_primrec)

/-- A fixed tag's private-path fall-through state is primitive recursive. -/
theorem pathExit_primrec {numTags : Nat}
    (tag : Fin numTags) {sharedEntry : Nat.Partrec.Code → FiniteTM0.State}
    (hshared : Primrec sharedEntry) :
    Primrec fun c => pathExit (sharedEntry c) c tag :=
  Primrec.nat_add.comp (pathOffset_primrec tag hshared) pathWidth_primrec

/-- The first fresh state after all initializer sources is primitive
recursive in the source code and shared entry. -/
theorem exitState_primrec (numTags : Nat)
    {sharedEntry : Nat.Partrec.Code → FiniteTM0.State}
    (hshared : Primrec sharedEntry) :
    Primrec fun c => exitState (sharedEntry c) c numTags := by
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp hshared (Primrec.const 1))
    (Primrec.nat_mul.comp (Primrec.const numTags) tagBlockWidth_primrec)

/-- Computable form of `exitState_primrec`. -/
theorem exitState_computable (numTags : Nat)
    {sharedEntry : Nat.Partrec.Code → FiniteTM0.State}
    (hshared : Primrec sharedEntry) :
    Computable fun c => exitState (sharedEntry c) c numTags :=
  (exitState_primrec numTags hshared).to_comp

private theorem dispatchRule_primrec {numTags : Nat}
    (tag : Fin numTags) {sharedEntry : Nat.Partrec.Code → FiniteTM0.State}
    (hshared : Primrec sharedEntry) :
    Primrec fun c =>
      FiniteTM0.Rule.mk (sharedEntry c) (tagSymbol tag)
        (pathOffset (sharedEntry c) c tag) (.write blankSymbol) := by
  exact Primrec.pair
    (Primrec.pair hshared (Primrec.const (tagSymbol tag)))
    (Primrec.pair (pathOffset_primrec tag hshared)
      (Primrec.const
        (FiniteTM0.Action.write
          (numSymbols := AlphabetSize numTags) blankSymbol)))

private theorem dispatchTableFrom_primrec {numTags : Nat}
    (tags : List (Fin numTags))
    {sharedEntry : Nat.Partrec.Code → FiniteTM0.State}
    (hshared : Primrec sharedEntry) :
    Primrec fun c => tags.map fun tag =>
      FiniteTM0.Rule.mk (sharedEntry c) (tagSymbol tag)
        (pathOffset (sharedEntry c) c tag) (.write blankSymbol) := by
  induction tags with
  | nil => exact Primrec.const []
  | cons tag tags ih =>
      exact Primrec.list_cons.comp
        (dispatchRule_primrec tag hshared) ih

/-- The shared tag dispatcher is primitive recursive in both the source code
and any primitive-recursive choice of its entry state. -/
theorem dispatchTable_primrec {numTags : Nat}
    {sharedEntry : Nat.Partrec.Code → FiniteTM0.State}
    (hshared : Primrec sharedEntry) :
    Primrec fun c => dispatchTable (sharedEntry c) c numTags := by
  simpa only [dispatchTable] using
    dispatchTableFrom_primrec (List.finRange numTags) hshared

/-- One private tag block is primitive recursive when its entry and selected
continuation state are primitive recursive in the source code. -/
theorem tagBlock_primrec {numTags : Nat} (growth : Turing.Dir)
    (tag : Fin numTags)
    {sharedEntry target : Nat.Partrec.Code → FiniteTM0.State}
    (hshared : Primrec sharedEntry) (htarget : Primrec target) :
    Primrec fun c =>
      tagBlock (sharedEntry c) c growth tag (target c) := by
  have hpath : Primrec fun c =>
      FiniteTM0Path.table (pathOffset (sharedEntry c) c tag)
        (instructions c growth tag) :=
    FiniteTM0Path.table_primrec.comp
      ((pathOffset_primrec tag hshared).pair
        (instructions_primrec growth tag))
  have hfinishRule : Primrec fun c =>
      FiniteTM0.Rule.mk (pathExit (sharedEntry c) c tag)
        (boundarySymbol (numTags := numTags) 4) (target c)
        (FiniteTM0.Action.write
          (boundarySymbol (numTags := numTags) 4)) := by
    exact Primrec.pair
      (Primrec.pair (pathExit_primrec tag hshared)
        (Primrec.const (boundarySymbol (numTags := numTags) 4)))
      (Primrec.pair htarget
        (Primrec.const (FiniteTM0.Action.write
          (boundarySymbol (numTags := numTags) 4))))
  have hfinish : Primrec fun c =>
      [FiniteTM0.Rule.mk (pathExit (sharedEntry c) c tag)
        (boundarySymbol (numTags := numTags) 4) (target c)
        (FiniteTM0.Action.write
          (boundarySymbol (numTags := numTags) 4))] :=
    Primrec.list_cons.comp hfinishRule (Primrec.const [])
  exact Primrec.list_append.comp hpath hfinish

private theorem tagBlocksFrom_primrec {numTags : Nat}
    (tags : List (Fin numTags)) (growth : Fin numTags → Turing.Dir)
    {sharedEntry : Nat.Partrec.Code → FiniteTM0.State}
    (exitFor : Nat.Partrec.Code → Fin numTags → FiniteTM0.State)
    (hshared : Primrec sharedEntry)
    (hexit : ∀ tag, Primrec fun c => exitFor c tag) :
    Primrec fun c => tags.flatMap fun tag =>
      tagBlock (sharedEntry c) c (growth tag) tag (exitFor c tag) := by
  induction tags with
  | nil => exact Primrec.const []
  | cons tag tags ih =>
      exact Primrec.list_append.comp
        (tagBlock_primrec (growth tag) tag hshared (hexit tag)) ih

/-- The complete tag-sensitive initializer table is primitive recursive in
the designated source code.  The finite orientation map is fixed, while the
shared entry and every tag-specific continuation may themselves vary
primitive recursively with the code. -/
theorem table_primrec {numTags : Nat}
    {sharedEntry : Nat.Partrec.Code → FiniteTM0.State}
    (growth : Fin numTags → Turing.Dir)
    (exitFor : Nat.Partrec.Code → Fin numTags → FiniteTM0.State)
    (hshared : Primrec sharedEntry)
    (hexit : ∀ tag, Primrec fun c => exitFor c tag) :
    Primrec fun c =>
      table (sharedEntry c) c numTags growth (exitFor c) := by
  exact Primrec.list_append.comp
    (dispatchTable_primrec hshared)
    (tagBlocksFrom_primrec (List.finRange numTags) growth exitFor
      hshared hexit)

/-- Computable form of `table_primrec`. -/
theorem table_computable_uniform {numTags : Nat}
    {sharedEntry : Nat.Partrec.Code → FiniteTM0.State}
    (growth : Fin numTags → Turing.Dir)
    (exitFor : Nat.Partrec.Code → Fin numTags → FiniteTM0.State)
    (hshared : Primrec sharedEntry)
    (hexit : ∀ tag, Primrec fun c => exitFor c tag) :
    Computable fun c =>
      table (sharedEntry c) c numTags growth (exitFor c) :=
  (table_primrec growth exitFor hshared hexit).to_comp

end

end CanonicalInitializerProgram
end Hooper
end Kari
end LeanWang
