/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlControllerEntrySemantics
import LeanWang.Kari.Hooper.CounterControlSearchSystem

/-!
# Arbitrary tapes at compiled search entries

An arbitrary one-sided tape ray has a least nonblank cell or is blank
forever.  At the least nonblank cell, either the selected command recognizes
its target, giving a genuine `SearchGap`, or the cell is a wrong nonblank.

The native bounded scan has particularly simple behavior on this
decomposition.  A wrong nonblank which fits in the remaining private scan
causes the complete machine to halt.  A blank prefix through the last private
scan position reaches the command's exact launch state (or has already
halted).  The only semantic obligation not settled locally is therefore the
extended converse-Basic-Lemma case: a launch whose remaining ray has no
genuine matching target must halt.

`gap_of_reachable_search_on_immortal_orbit` packages this boundary cleanly.
Given that launch obligation, every compiled search entry reached on an
immortal orbit has a genuine finite matching gap.  In particular, a farther
wrong first nonblank is not incorrectly treated as a local scan failure: it
is routed through the launch obligation.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlArbitrarySearch

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlSearchSystem

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

universe u

/-! ## One-sided tape-ray geometry -/

/-- Every cell on the one-sided ray beginning at the head is blank. -/
def BlankRay {Gamma : Type u} (IsBlank : Gamma → Prop)
    (T : FullTM0.Tape Gamma) (direction : Turing.Dir) : Prop :=
  ∀ distance : Nat,
    IsBlank (T (FullTM0.Tape.offset direction distance))

/-- The cell at `distance` is the first nonblank cell on the selected ray. -/
def FirstNonblank {Gamma : Type u} (IsBlank : Gamma → Prop)
    (T : FullTM0.Tape Gamma) (direction : Turing.Dir)
    (distance : Nat) : Prop :=
  (∀ i < distance,
      IsBlank (T (FullTM0.Tape.offset direction i))) ∧
    ¬ IsBlank (T (FullTM0.Tape.offset direction distance))

/-- A blank gap ending at a nonblank symbol which is not the desired mark. -/
def WrongGap {Gamma : Type u} (IsBlank IsMark : Gamma → Prop)
    (T : FullTM0.Tape Gamma) (direction : Turing.Dir)
    (distance : Nat) : Prop :=
  FirstNonblank IsBlank T direction distance ∧
    ¬ IsMark (T (FullTM0.Tape.offset direction distance))

namespace FirstNonblank

variable {Gamma : Type u} {IsBlank : Gamma → Prop}
variable {T : FullTM0.Tape Gamma} {direction : Turing.Dir}
variable {distance : Nat}

theorem blank (h : FirstNonblank IsBlank T direction distance)
    {i : Nat} (hi : i < distance) :
    IsBlank (T (FullTM0.Tape.offset direction i)) :=
  h.1 i hi

theorem nonblank (h : FirstNonblank IsBlank T direction distance) :
    ¬ IsBlank (T (FullTM0.Tape.offset direction distance)) :=
  h.2

end FirstNonblank

namespace WrongGap

variable {Gamma : Type u} {IsBlank IsMark : Gamma → Prop}
variable {T : FullTM0.Tape Gamma} {direction : Turing.Dir}
variable {distance : Nat}

theorem blank (h : WrongGap IsBlank IsMark T direction distance)
    {i : Nat} (hi : i < distance) :
    IsBlank (T (FullTM0.Tape.offset direction i)) :=
  h.1.blank hi

theorem nonblank (h : WrongGap IsBlank IsMark T direction distance) :
    ¬ IsBlank (T (FullTM0.Tape.offset direction distance)) :=
  h.1.nonblank

theorem not_marked (h : WrongGap IsBlank IsMark T direction distance) :
    ¬ IsMark (T (FullTM0.Tape.offset direction distance)) :=
  h.2

/-- Moving once toward a wrong cell at distance `k + 1` leaves a wrong gap
of distance `k`. -/
theorem tail {k : Nat}
    (h : WrongGap IsBlank IsMark T direction (k + 1)) :
    WrongGap IsBlank IsMark (T.move direction) direction k := by
  constructor
  · constructor
    · intro i hi
      simpa using h.blank (Nat.succ_lt_succ hi)
    · simpa using h.nonblank
  · simpa using h.not_marked

end WrongGap

/-- A one-sided ray either has a least nonblank cell or is blank forever. -/
theorem firstNonblank_or_blankRay {Gamma : Type u}
    (IsBlank : Gamma → Prop) (T : FullTM0.Tape Gamma)
    (direction : Turing.Dir) :
    (∃ distance, FirstNonblank IsBlank T direction distance) ∨
      BlankRay IsBlank T direction := by
  classical
  by_cases hnonblank : ∃ distance : Nat,
      ¬ IsBlank (T (FullTM0.Tape.offset direction distance))
  · left
    let distance := Nat.find hnonblank
    refine ⟨distance, ?_, Nat.find_spec hnonblank⟩
    intro i hi
    by_contra hiBlank
    have hle := Nat.find_min' hnonblank hiBlank
    omega
  · right
    intro distance
    by_contra hiBlank
    exact hnonblank ⟨distance, hiBlank⟩

/-- Trichotomy for an arbitrary one-sided search ray: a genuine marked gap,
a least wrong nonblank, or a ray which is blank forever. -/
theorem searchGap_or_wrongGap_or_blankRay {Gamma : Type u}
    (IsBlank IsMark : Gamma → Prop) (T : FullTM0.Tape Gamma)
    (direction : Turing.Dir) :
    (∃ distance, SearchGap IsBlank IsMark T direction distance) ∨
      (∃ distance, WrongGap IsBlank IsMark T direction distance) ∨
      BlankRay IsBlank T direction := by
  classical
  rcases firstNonblank_or_blankRay IsBlank T direction with
    ⟨distance, hfirst⟩ | hallBlank
  · by_cases hmark :
        IsMark (T (FullTM0.Tape.offset direction distance))
    · exact Or.inl ⟨distance, hfirst.1, hmark⟩
    · exact Or.inr (Or.inl ⟨distance, hfirst, hmark⟩)
  · exact Or.inr (Or.inr hallBlank)

/-- Prefixing a genuine search gap by `prefix` blank cells gives a search
gap whose distance is increased by `prefix`. -/
theorem SearchGap.prepend_moveN {Gamma : Type u}
    {IsBlank IsMark : Gamma → Prop} {T : FullTM0.Tape Gamma}
    {direction : Turing.Dir} {pref distance : Nat}
    (hprefix : ∀ i < pref,
      IsBlank (T (FullTM0.Tape.offset direction i)))
    (hgap : SearchGap IsBlank IsMark
      (T.moveN direction pref) direction distance) :
    SearchGap IsBlank IsMark T direction (pref + distance) := by
  constructor
  · intro i hi
    by_cases hiprefix : i < pref
    · exact hprefix i hiprefix
    · have hprefixLe : pref ≤ i := Nat.le_of_not_gt hiprefix
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hprefixLe
      have hj : j < distance := by omega
      simpa [FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_add,
        add_comm, add_left_comm, add_assoc] using hgap.blank hj
  · simpa [FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_add,
      add_comm, add_left_comm, add_assoc] using hgap.marked

/-! ## Private bounded scans inside the complete controller -/

/-- A path through a right-hand table survives a source-disjoint prefix. -/
private theorem reaches_append_right_of_source_disjoint {numSymbols : Nat}
    (first second : FiniteTM0.Table numSymbols)
    (hdisjoint : ∀ state,
      state ∈ FiniteTM0.sourceStates second →
      state ∉ FiniteTM0.sourceStates first)
    {start finish :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (hreach : FullTM0.Reaches (FiniteTM0.machine second) start finish) :
    FullTM0.Reaches (FiniteTM0.machine (first ++ second)) start finish := by
  apply Relation.ReflTransGen.mono ?_ hreach
  intro current next hstep
  have hright : current.q ∈ FiniteTM0.sourceStates second := by
    by_contra hsource
    have hnone := FiniteTM0.machine_eq_none_of_state_not_mem
      hsource current.tape.read
    have hstepNone :
        FullTM0.step (FiniteTM0.machine second) current = none := by
      unfold FullTM0.step
      rw [hnone]
      rfl
    rw [hstepNone] at hstep
    simp at hstep
  have hlookup :
      FiniteTM0.lookupAction first current.q current.tape.read = none := by
    cases hfirst : FiniteTM0.lookupAction first current.q current.tape.read with
    | none => rfl
    | some result =>
        exfalso
        apply hdisjoint current.q hright
        rcases result with ⟨target, action⟩
        have hrule := FiniteTM0.rule_mem_of_lookupAction_eq_some hfirst
        exact List.mem_map.mpr
          ⟨FiniteTM0.Rule.mk current.q current.tape.read target action,
            hrule, rfl⟩
  simp only [FullTM0.step, FiniteTM0.machine_apply,
    FiniteTM0Program.lookupAction_append, hlookup]
  exact hstep

/-- A guarded sequence of blank scan moves in one selected command is also
an execution of the complete counter controller. -/
theorem scan_moves_reaches
    (base : Nat) (c : Nat.Partrec.Code) {commandOffset : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (progress distance : Nat)
    (hbound : progress + distance ≤
      NestingMachine.bound (CanonicalInitializer.radius c))
    (T : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ i < distance,
      T (FullTM0.Tape.offset command.searchDirection i) = blankSymbol) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨commandOffset + progress, T⟩
      ⟨commandOffset + (progress + distance),
        T.moveN command.searchDirection distance⟩ := by
  let radius := CanonicalInitializer.radius c
  have hscan := BoundedMarkerProgram.nativeScan_moves_reaches
    radius command.target command.searchDirection progress distance
    (by simpa [radius] using hbound) T hblank
  have hlocal := FiniteTM0Program.reaches_append_left
    (nativeScanTable radius command.target command.searchDirection)
    (liftTable (numTags := numTags)
      (NestingMachine.unwindTable radius command.searchDirection)) hscan
  have hprivate : FullTM0.Reaches
      (FiniteTM0.machine
        (privateControllerTable radius commandOffset command))
      ⟨commandOffset + progress, T⟩
      ⟨commandOffset + (progress + distance),
        T.moveN command.searchDirection distance⟩ := by
    have hrelocated := FiniteTM0Program.reaches_relocate commandOffset
      (nativeLocalTable radius command.target command.searchDirection) hlocal
    simpa [privateControllerTable, nativeLocalTable,
      FiniteTM0Program.liftCfg] using hrelocated
  have hcommand : FullTM0.Reaches
      (FiniteTM0.machine
        (commandTable radius commandOffset
          (coreEntry base radius (commands base c)) command))
      ⟨commandOffset + progress, T⟩
      ⟨commandOffset + (progress + distance),
        T.moveN command.searchDirection distance⟩ := by
    have hlift := reaches_append_right_of_source_disjoint
      (continuationTable radius commandOffset
        (coreEntry base radius (commands base c)) command)
      (privateControllerTable radius commandOffset command)
      (fun state hprivate hcontinuation =>
        private_continuation_source_disjoint radius commandOffset
          (coreEntry base radius (commands base c)) command state
          hprivate hcontinuation)
      hprivate
    simpa [commandTable] using hlift
  exact BoundedMarkerProgram.table_reaches_of_commandAt
    (coreTable base c) (by simpa [radius] using hat) hcommand

/-- A least wrong nonblank which still fits in the remaining native scan
forces the complete machine to halt. -/
theorem haltsFrom_scan_of_wrongGap
    (base : Nat) (c : Nat.Partrec.Code) {commandOffset : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (progress distance : Nat)
    (hbound : progress + distance ≤
      NestingMachine.bound (CanonicalInitializer.radius c))
    (T : FullTM0.Tape (Symbol numTags))
    (hwrong : WrongGap (fun symbol => symbol = blankSymbol)
      command.target.Matches T command.searchDirection distance) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      ⟨commandOffset + progress, T⟩ := by
  have hmoves := scan_moves_reaches base c hat progress distance hbound T
    (fun i hi => hwrong.blank hi)
  let endpoint := T.moveN command.searchDirection distance
  have hnotBlank : endpoint.read ≠ blankSymbol := by
    simpa [endpoint, FullTM0.Tape.read_moveN] using hwrong.nonblank
  have hnotTarget : ¬ command.target.Matches endpoint.read := by
    simpa [endpoint, FullTM0.Tape.read_moveN] using hwrong.not_marked
  rcases CounterControlControllerEntrySemantics.scan_step_or_haltsFrom
      base c hat (progress + distance) hbound endpoint with
    hhalts | ⟨hmatch, _hfound⟩ |
      ⟨hblank, _hadvanceOrLaunch⟩
  · exact FullTM0.HaltsFrom.of_reaches hmoves hhalts
  · exact False.elim (hnotTarget hmatch)
  · exact False.elim (hnotBlank hblank)

/-- The same local mismatch fact, prepended by an arbitrary finite path to
the private scan position. -/
theorem haltsFrom_of_reaches_scan_wrongGap
    (base : Nat) (c : Nat.Partrec.Code)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    {commandOffset : Nat} {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (progress distance : Nat)
    (hbound : progress + distance ≤
      NestingMachine.bound (CanonicalInitializer.radius c))
    (T : FullTM0.Tape (Symbol numTags))
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨commandOffset + progress, T⟩)
    (hwrong : WrongGap (fun symbol => symbol = blankSymbol)
      command.target.Matches T command.searchDirection distance) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start :=
  FullTM0.HaltsFrom.of_reaches hreach
    (haltsFrom_scan_of_wrongGap base c hat progress distance hbound T hwrong)

/-! ## Exhausted searches and the extended launch obligation -/

/-- Exact command-local launch configuration after exhausting the bounded
blank prefix of a canonical search entry. -/
def exhaustedLaunchCfg (base : Nat) (c : Nat.Partrec.Code)
    (search : Search) (outer : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  ⟨launchState (CanonicalInitializer.radius c)
      (CounterControlSearchSystem.commandOffset base c search),
    outer.moveN (command base c search).searchDirection
      (NestingMachine.bound (CanonicalInitializer.radius c))⟩

/-- A canonical search entry whose tape is blank through its final private
scan cell either already halts or reaches its exact launch configuration. -/
theorem reaches_exhaustedLaunch_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) (search : Search)
    (outer : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ i ≤ NestingMachine.bound (CanonicalInitializer.radius c),
      outer (FullTM0.Tape.offset
        (command base c search).searchDirection i) = blankSymbol) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ((searchSystem base c).startCfg search outer) ∨
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ((searchSystem base c).startCfg search outer)
        (exhaustedLaunchCfg base c search outer) := by
  let radius := CanonicalInitializer.radius c
  let bound := NestingMachine.bound radius
  have hat : CommandAt radius base
      (CounterControlSearchSystem.commandOffset base c search)
      (command base c search) (commands base c) := by
    simpa [radius, command, CounterControlSearchSystem.commandOffset] using
      (CounterControlWellFormed.compileCommand_commandAt base c search)
  have hmoves := scan_moves_reaches base c hat 0 bound
    (by simp [bound, radius]) outer
    (fun i hi => hblank i (by simpa [bound, radius] using hi.le))
  have hread :
      (outer.moveN (command base c search).searchDirection bound).read =
        blankSymbol := by
    simpa [FullTM0.Tape.read_moveN, bound, radius] using
      hblank (NestingMachine.bound (CanonicalInitializer.radius c))
        (Nat.le_refl _)
  rcases CounterControlControllerEntrySemantics.scan_step_or_haltsFrom
      base c hat bound (by simp [bound, radius])
      (outer.moveN (command base c search).searchDirection bound) with
    hhalts | ⟨hmatch, _hfound⟩ |
      ⟨_hblank, ⟨hlt, _hadvance⟩ | ⟨heq, hlaunch⟩⟩
  · left
    apply FullTM0.HaltsFrom.of_reaches ?_ hhalts
    simpa [searchSystem, SearchSystem.startCfg,
      CounterControlSearchSystem.commandOffset,
      Nat.add_assoc, bound] using hmoves
  · exact False.elim
      (BoundedMarkerProgram.target_not_blank (command base c search).target
        (by
          rw [← hread]
          exact hmatch))
  · exfalso
    simp [bound, radius] at hlt
  · right
    have hstep : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨CounterControlSearchSystem.commandOffset base c search + bound,
          outer.moveN (command base c search).searchDirection bound⟩
        (exhaustedLaunchCfg base c search outer) := by
      apply Relation.ReflTransGen.single
      simpa [exhaustedLaunchCfg, heq, radius, bound] using hlaunch
    have hmoves' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ((searchSystem base c).startCfg search outer)
        ⟨CounterControlSearchSystem.commandOffset base c search + bound,
          outer.moveN (command base c search).searchDirection bound⟩ := by
      simpa [searchSystem, SearchSystem.startCfg,
        CounterControlSearchSystem.commandOffset,
        Nat.add_assoc, bound] using hmoves
    exact hmoves'.trans hstep

/-- The one missing arbitrary-ray launch obligation.  It is intentionally
stated at the exact command-local launch state: whenever the remaining ray
contains no genuine matching search gap, the launched computation halts.

This includes a wrong first nonblank beyond the native scan radius, even if
matching symbols occur still farther away, because such a ray has no genuine
blank-to-target `SearchGap`. -/
def NoTargetLaunchHalts (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ (search : Search) (launchTape : FullTM0.Tape (Symbol numTags)),
    (¬ ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (command base c search).target.Matches launchTape
        (command base c search).searchDirection distance) →
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      ⟨launchState (CanonicalInitializer.radius c)
          (CounterControlSearchSystem.commandOffset base c search), launchTape⟩

/-- Conditional arbitrary-search converse.  Once no-target launches are
known mortal, an immortal orbit cannot reach a compiled search entry unless
that search has a genuine finite matching gap. -/
theorem gap_of_reachable_search_on_immortal_orbit
    (base : Nat) (c : Nat.Partrec.Code)
    (hlaunch : NoTargetLaunchHalts base c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    {search : Search} {outer : FullTM0.Tape (Symbol numTags)}
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ((searchSystem base c).startCfg search outer)) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (command base c search).target.Matches outer
        (command base c search).searchDirection distance := by
  classical
  by_contra hgap
  have hnoGap : ¬ ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (command base c search).target.Matches outer
        (command base c search).searchDirection distance := hgap
  have contradicts_immortality :
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start →
        False :=
    (FullTM0.HaltsFrom.immortalFrom_iff_not
      (CounterControlNestingBridge.machine base c) start).mp himmortal
  rcases searchGap_or_wrongGap_or_blankRay
      (fun symbol : Symbol numTags => symbol = blankSymbol)
      (command base c search).target.Matches outer
      (command base c search).searchDirection with
    hmatching | ⟨distance, hwrong⟩ | hallBlank
  · exact False.elim (hnoGap hmatching)
  · let bound := NestingMachine.bound (CanonicalInitializer.radius c)
    by_cases hnear : distance ≤ bound
    · have hhalts := haltsFrom_of_reaches_scan_wrongGap base c
          (CounterControlWellFormed.compileCommand_commandAt base c search)
          0 distance (by simpa [bound] using hnear) outer
          (by simpa [searchSystem, SearchSystem.startCfg,
            CounterControlSearchSystem.commandOffset,
            command] using hreach)
          (by simpa [command] using hwrong)
      exact contradicts_immortality hhalts
    · have hfar : bound < distance := Nat.lt_of_not_ge hnear
      have hblankThrough : ∀ i ≤ bound,
          outer (FullTM0.Tape.offset
            (command base c search).searchDirection i) = blankSymbol := by
        intro i hi
        exact hwrong.blank (hi.trans_lt hfar)
      rcases reaches_exhaustedLaunch_or_haltsFrom base c search outer
          (by simpa [bound] using hblankThrough) with
        hsearchHalts | htoLaunch
      · exact contradicts_immortality
          (FullTM0.HaltsFrom.of_reaches hreach hsearchHalts)
      · have hprefix : ∀ i < bound,
            outer (FullTM0.Tape.offset
              (command base c search).searchDirection i) = blankSymbol := by
          intro i hi
          exact hblankThrough i hi.le
        have hnoRemainingGap : ¬ ∃ remaining,
            SearchGap (fun symbol => symbol = blankSymbol)
              (command base c search).target.Matches
              (outer.moveN (command base c search).searchDirection bound)
              (command base c search).searchDirection remaining := by
          rintro ⟨remaining, hremaining⟩
          exact hnoGap ⟨bound + remaining,
            SearchGap.prepend_moveN hprefix hremaining⟩
        have hlaunchHalts := hlaunch search
          (outer.moveN (command base c search).searchDirection bound)
          hnoRemainingGap
        apply contradicts_immortality
        apply FullTM0.HaltsFrom.of_reaches (hreach.trans htoLaunch)
        simpa [exhaustedLaunchCfg, bound] using hlaunchHalts
  · let bound := NestingMachine.bound (CanonicalInitializer.radius c)
    have hblankThrough : ∀ i ≤ bound,
        outer (FullTM0.Tape.offset
          (command base c search).searchDirection i) = blankSymbol := by
      intro i _hi
      exact hallBlank i
    rcases reaches_exhaustedLaunch_or_haltsFrom base c search outer
        (by simpa [bound] using hblankThrough) with
      hsearchHalts | htoLaunch
    · exact contradicts_immortality
        (FullTM0.HaltsFrom.of_reaches hreach hsearchHalts)
    · have hprefix : ∀ i < bound,
          outer (FullTM0.Tape.offset
            (command base c search).searchDirection i) = blankSymbol := by
        intro i _hi
        exact hallBlank i
      have hnoRemainingGap : ¬ ∃ remaining,
          SearchGap (fun symbol => symbol = blankSymbol)
            (command base c search).target.Matches
            (outer.moveN (command base c search).searchDirection bound)
            (command base c search).searchDirection remaining := by
        rintro ⟨remaining, hremaining⟩
        exact hnoGap ⟨bound + remaining,
          SearchGap.prepend_moveN hprefix hremaining⟩
      have hlaunchHalts := hlaunch search
        (outer.moveN (command base c search).searchDirection bound)
        hnoRemainingGap
      apply contradicts_immortality
      apply FullTM0.HaltsFrom.of_reaches (hreach.trans htoLaunch)
      simpa [exhaustedLaunchCfg, bound] using hlaunchHalts

end

end CounterControlArbitrarySearch
end Hooper
end Kari
end LeanWang
