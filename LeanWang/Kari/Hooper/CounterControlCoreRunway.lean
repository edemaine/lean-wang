/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCoreEnvelope
import LeanWang.Kari.Hooper.CounterControlTagFreeOpen

/-!
# The first obstruction beyond a validated counter core

A validated five-boundary core has only two possible outward tails.  Either
every cell beyond boundary `4` is blank, giving a tag-free open core, or there
is a least nonblank cell.  In the latter case all intervening cells form a
finite runway.  When logical coordinate `0` is an actual saved tag, that
runway and its least obstruction assemble into an exact finite core envelope.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCoreRunway

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlCoreFrame CounterControlTagFreeOpen
open CounterControlCoreEnvelope

noncomputable section

private theorem exists_target_matches_of_ne_blank {numTags : Nat}
    (symbol : Symbol numTags) (hne : symbol ≠ blankSymbol) :
    ∃ target : Target numTags, target.Matches symbol := by
  have hval : symbol.val ≠ 0 := by
    intro hzero
    apply hne
    apply Fin.ext
    simpa [blankSymbol, baseSymbol, MarkerMachine.blankSymbol,
      MarkerMachine.encodeSymbol] using hzero
  by_cases hbase : symbol.val < MarkerMachine.AlphabetSize
  · let label : Fin 5 := ⟨symbol.val - 1, by
        simp only [MarkerMachine.AlphabetSize] at hbase
        omega⟩
    refine ⟨Target.boundary label, ?_⟩
    change symbol = boundarySymbol label
    apply Fin.ext
    simp [label, boundarySymbol, baseSymbol, MarkerMachine.boundarySymbol,
      MarkerMachine.encodeSymbol]
    omega
  · have htagLower : MarkerMachine.AlphabetSize ≤ symbol.val :=
      Nat.le_of_not_gt hbase
    let tag : Fin numTags :=
      ⟨symbol.val - MarkerMachine.AlphabetSize, by
        have hsymbol := symbol.isLt
        simp only [AlphabetSize] at hsymbol
        omega⟩
    refine ⟨Target.anyTag, tag, ?_⟩
    apply Fin.ext
    simp [tag, tagSymbol]
    omega

/-- A represented core either has an infinite blank outward runway or has a
least nonblank obstruction beyond boundary `4`. -/
theorem coreOpen_or_firstNonblank {numTags : Nat}
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents registers growth T) :
    CoreOpenRepresents registers growth T ∨
      ∃ distance,
        layoutEnd registers < distance ∧
          (∀ position, layoutEnd registers < position →
            position < distance →
              logicalTape growth T position = blankSymbol) ∧
          logicalTape growth T distance ≠ blankSymbol := by
  classical
  by_cases hopen : ∀ position, layoutEnd registers < position →
      logicalTape growth T position = blankSymbol
  · exact Or.inl ⟨hcore, hopen⟩
  · have hexists : ∃ position,
        layoutEnd registers < position ∧
          logicalTape growth T position ≠ blankSymbol := by
      rcases Classical.exists_not_of_not_forall hopen with
        ⟨position, hposition⟩
      have hpast : layoutEnd registers < position := by
        by_contra hpast
        apply hposition
        intro hpast'
        exact False.elim (hpast hpast')
      have hnonblank : logicalTape growth T position ≠ blankSymbol := by
        intro hblank
        exact hposition (fun _ => hblank)
      exact ⟨position, hpast, hnonblank⟩
    let distance := Nat.find hexists
    have hdistance := Nat.find_spec hexists
    right
    refine ⟨distance, hdistance.1, ?_, hdistance.2⟩
    intro position hpast hbefore
    by_contra hnonblank
    have hminimal : distance ≤ position :=
      Nat.find_min' hexists ⟨hpast, hnonblank⟩
    omega

/-- If coordinate `0` is a genuine saved tag, the first finite obstruction
is recognized by one of the controller's boundary-or-tag targets and hence
forms an exact `CoreEnvelope`. -/
theorem taggedCore_open_or_envelope {numTags : Nat}
    {registers : Registers} {growth : Turing.Dir}
    {returnTag : Fin numTags} {T : FullTM0.Tape (Symbol numTags)}
    (hcore : TaggedCoreRepresents registers growth returnTag T) :
    CoreOpenRepresents registers growth T ∨
      ∃ distance target,
        CoreEnvelope registers growth returnTag distance target T := by
  rcases coreOpen_or_firstNonblank hcore.toCoreRepresents with
    hopen | ⟨distance, hbefore, hrunway, hnonblank⟩
  · exact Or.inl hopen
  · rcases exists_target_matches_of_ne_blank
        (logicalTape growth T distance) hnonblank with ⟨target, htarget⟩
    exact Or.inr ⟨distance, target,
      { toTaggedCoreRepresents := hcore
        core_before_target := hbefore
        runway := hrunway
        target_matches := htarget }⟩

end

end CounterControlCoreRunway
end Hooper
end Kari
end LeanWang
