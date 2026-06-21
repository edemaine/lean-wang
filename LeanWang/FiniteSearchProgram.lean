/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/
import LeanWang.Machine

/-!
Finite Boolean search programs.

This file builds a small generated `TableProgram` that scans a finite list of
Boolean markers. At state `i`, a `true` marker jumps to halt and a `false`
marker advances to state `i + 1`; after the list is exhausted, the machine loops
right forever on blank tape. This is a finite control-flow fragment of the
eventual fuel-search compiler.
-/

namespace LeanWang

namespace FiniteSearchProgram

def transition (halt i : Nat) (b : Bool) : TableTransition where
  state := i
  read := 0
  write := 0
  next := if b then halt else i + 1
  move := Move.right

def loopTransition (i : Nat) : TableTransition where
  state := i
  read := 0
  write := 0
  next := i
  move := Move.right

def foldStep (bs : List Bool)
    (s : List TableTransition × Nat) (b : Bool) :
    List TableTransition × Nat :=
  (s.1 ++ [transition (bs.length + 1) s.2 b], s.2 + 1)

def foldStep₂ (bs : List Bool) (p : (List TableTransition × Nat) × Bool) :
    List TableTransition × Nat :=
  foldStep bs p.1 p.2

def folded (bs : List Bool) : List TableTransition × Nat :=
  bs.foldl (fun s b => foldStep₂ bs (s, b)) ([], 0)

def transitions (bs : List Bool) : List TableTransition :=
  (folded bs).1 ++ [loopTransition (folded bs).2]

def coreTransitionsFrom (halt i : Nat) : List Bool → List TableTransition
  | [] => []
  | b :: bs => transition halt i b :: coreTransitionsFrom halt (i + 1) bs

def transitionsFrom (halt i : Nat) : List Bool → List TableTransition
  | [] => [loopTransition i]
  | b :: bs => transition halt i b :: transitionsFrom halt (i + 1) bs

def program (bs : List Bool) : TableProgram where
  symbols := []
  states := List.range (bs.length + 1)
  blank := 0
  start := 0
  halt := bs.length + 1
  table := transitions bs

theorem foldStep₂_snd (bs : List Bool)
    (s : List TableTransition × Nat) (b : Bool) :
    (foldStep₂ bs (s, b)).2 = s.2 + 1 := by
  rfl

theorem foldl_foldStep₂_snd (bs : List Bool) :
    ∀ xs : List Bool, ∀ s : List TableTransition × Nat,
      (xs.foldl (fun acc b => foldStep₂ bs (acc, b)) s).2 = s.2 + xs.length
  | [], s => by
      simp
  | b :: xs, s => by
      rw [List.foldl_cons, foldl_foldStep₂_snd bs xs (foldStep₂ bs (s, b))]
      rw [foldStep₂_snd]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem folded_snd (bs : List Bool) :
    (folded bs).2 = bs.length := by
  unfold folded
  simpa using foldl_foldStep₂_snd bs bs (([] : List TableTransition), 0)

theorem foldl_foldStep₂_eq_coreTransitionsFrom (bs : List Bool) :
    ∀ xs : List Bool, ∀ s : List TableTransition × Nat,
      xs.foldl (fun acc b => foldStep₂ bs (acc, b)) s =
        (s.1 ++ coreTransitionsFrom (bs.length + 1) s.2 xs, s.2 + xs.length)
  | [], s => by
      simp [coreTransitionsFrom]
  | b :: xs, s => by
      rw [List.foldl_cons, foldl_foldStep₂_eq_coreTransitionsFrom bs xs (foldStep₂ bs (s, b))]
      simp [foldStep₂, foldStep, coreTransitionsFrom, List.append_assoc,
        Nat.add_comm, Nat.add_left_comm]

theorem folded_eq_coreTransitionsFrom (bs : List Bool) :
    folded bs = (coreTransitionsFrom (bs.length + 1) 0 bs, bs.length) := by
  unfold folded
  simpa using foldl_foldStep₂_eq_coreTransitionsFrom bs bs (([] : List TableTransition), 0)

theorem coreTransitionsFrom_append_loop (halt i : Nat) :
    ∀ bs : List Bool,
      coreTransitionsFrom halt i bs ++ [loopTransition (i + bs.length)] =
        transitionsFrom halt i bs
  | [] => by
      rfl
  | b :: bs => by
      simp only [coreTransitionsFrom, transitionsFrom]
      rw [show i + (b :: bs).length = i + 1 + bs.length by
        simp [Nat.add_comm, Nat.add_left_comm]]
      exact congrArg (fun table => transition halt i b :: table)
        (coreTransitionsFrom_append_loop halt (i + 1) bs)

theorem transitions_eq_transitionsFrom (bs : List Bool) :
    transitions bs = transitionsFrom (bs.length + 1) 0 bs := by
  rw [transitions, folded_eq_coreTransitionsFrom]
  simpa using coreTransitionsFrom_append_loop (bs.length + 1) 0 bs

theorem find?_transitionsFrom_replicate_false (halt i n : Nat) :
    ∀ bs : List Bool,
      (transitionsFrom halt i (List.replicate n false ++ bs)).find?
          (fun e => e.matchesInput (i + n) 0) =
        match bs with
        | [] => some (loopTransition (i + n))
        | b :: _ => some (transition halt (i + n) b)
  | [] => by
      induction n generalizing i with
      | zero =>
          simp [transitionsFrom, loopTransition]
      | succ n ih =>
          simp only [List.replicate_succ, List.append_nil, transitionsFrom, List.find?_cons]
          have hhead :
              (transition halt i false).matchesInput (i + (n + 1)) 0 = false := by
            apply TableTransition.matchesInput_mk_of_state_ne
            omega
          rw [hhead]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1)
  | b :: bs => by
      induction n generalizing i with
      | zero =>
          simp [transitionsFrom, transition]
      | succ n ih =>
          simp only [List.replicate_succ, List.cons_append, transitionsFrom, List.find?_cons]
          have hhead :
              (transition halt i false).matchesInput (i + (n + 1)) 0 = false := by
            apply TableTransition.matchesInput_mk_of_state_ne
            omega
          rw [hhead]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1)

theorem program_transition?_after_false_prefix (n : Nat) :
    ∀ bs : List Bool,
      (program (List.replicate n false ++ bs)).toTableMachine.transition? n 0 =
        match bs with
        | [] => some (loopTransition n)
        | b :: _ => some (transition ((List.replicate n false ++ bs).length + 1) n b)
  | [] => by
      unfold TableMachine.transition?
      rw [show (program (List.replicate n false ++ [])).toTableMachine.table =
          transitionsFrom ((List.replicate n false ++ []).length + 1) 0
            (List.replicate n false ++ []) by
        simp [program, TableProgram.toTableMachine, transitions_eq_transitionsFrom]]
      simpa [Nat.zero_add, List.length_replicate] using
        find?_transitionsFrom_replicate_false (n + 1) 0 n []
  | b :: bs => by
      unfold TableMachine.transition?
      rw [show (program (List.replicate n false ++ (b :: bs))).toTableMachine.table =
          transitionsFrom ((List.replicate n false ++ (b :: bs)).length + 1) 0
            (List.replicate n false ++ (b :: bs)) by
        simp [program, TableProgram.toTableMachine, transitions_eq_transitionsFrom]]
      simpa [List.length_replicate] using find?_transitionsFrom_replicate_false
        ((List.replicate n false ++ (b :: bs)).length + 1) 0 n (b :: bs)

theorem foldl_foldStep₂_fst_append (bs : List Bool) :
    ∀ xs : List Bool, ∀ s : List TableTransition × Nat,
      ∃ rest : List TableTransition,
        (xs.foldl (fun acc b => foldStep₂ bs (acc, b)) s).1 = s.1 ++ rest
  | [], s => by
      exact ⟨[], by simp⟩
  | b :: xs, s => by
      rcases foldl_foldStep₂_fst_append bs xs (foldStep₂ bs (s, b)) with
        ⟨rest, hrest⟩
      refine ⟨[transition (bs.length + 1) s.2 b] ++ rest, ?_⟩
      rw [List.foldl_cons, hrest]
      simp [foldStep₂, foldStep, List.append_assoc]

@[simp]
theorem program_start (bs : List Bool) :
    (program bs).start = 0 := rfl

@[simp]
theorem program_blank (bs : List Bool) :
    (program bs).blank = 0 := rfl

@[simp]
theorem program_halt (bs : List Bool) :
    (program bs).halt = bs.length + 1 := rfl

theorem program_start_ne_halt (bs : List Bool) :
    (program bs).start ≠ (program bs).halt := by
  simp

theorem program_nil_not_halts :
    ¬ (program []).toMachine.HaltsEmpty := by
  let e := loopTransition 0
  have htable : (program []).table = e :: [] := by
    rfl
  have hfind : (program []).toTableMachine.transition? (program []).start (program []).blank =
      some e :=
    TableProgram.transition?_eq_some_of_table_head_matches htable
      (by simp [e, loopTransition])
  have hwrite : e.write ∈ (program []).supportedSymbols := by
    simp [e, loopTransition, TableProgram.supportedSymbols]
  have hnext : e.next ∈ (program []).supportedStates := by
    simp [e, loopTransition, TableProgram.supportedStates]
  have hloop : e.action = ((program []).blank, (program []).start, Move.right) := by
    rfl
  exact TableProgram.not_haltsEmpty_of_initial_right_blank_loop
    (program_start_ne_halt []) hfind hwrite hnext hloop

theorem program_cons_true_halts (bs : List Bool) :
    (program (true :: bs)).toMachine.HaltsEmpty := by
  let e := transition ((true :: bs).length + 1) 0 true
  rcases foldl_foldStep₂_fst_append (true :: bs) bs ([e], 1) with ⟨rest, hrest⟩
  have hrest' :
      (List.foldl
        (fun s b => (s.1 ++ [transition ((true :: bs).length + 1) s.2 b], s.2 + 1))
        ([e], 1) bs).1 = [e] ++ rest := by
    simpa [foldStep₂, foldStep] using hrest
  have hrest'' :
      (List.foldl
        (fun s b => (s.1 ++ [transition (bs.length + 1 + 1) s.2 b], s.2 + 1))
        ([transition (bs.length + 1 + 1) 0 true], 1) bs).1 =
        [transition (bs.length + 1 + 1) 0 true] ++ rest := by
    simpa [e] using hrest'
  have htable : ∃ table : List TableTransition,
      (program (true :: bs)).table = e :: table := by
    refine ⟨rest ++ [loopTransition (folded (true :: bs)).2], ?_⟩
    change
      (List.foldl
        (fun s b => (s.1 ++ [transition (bs.length + 1 + 1) s.2 b], s.2 + 1))
        ([transition (bs.length + 1 + 1) 0 true], 1) bs).1 ++
          [loopTransition
            (List.foldl
              (fun s b => (s.1 ++ [transition (bs.length + 1 + 1) s.2 b], s.2 + 1))
              ([transition (bs.length + 1 + 1) 0 true], 1) bs).2] =
        transition (bs.length + 1 + 1) 0 true ::
          (rest ++
            [loopTransition
              (List.foldl
                (fun s b => (s.1 ++ [transition (bs.length + 1 + 1) s.2 b], s.2 + 1))
                ([transition (bs.length + 1 + 1) 0 true], 1) bs).2])
    rw [hrest'']
    rfl
  rcases htable with ⟨table, htable⟩
  have hfind :
      (program (true :: bs)).toTableMachine.transition?
          (program (true :: bs)).start (program (true :: bs)).blank = some e :=
    TableProgram.transition?_eq_some_of_table_head_matches htable
      (by simp [e, transition])
  have hwrite : e.write ∈ (program (true :: bs)).supportedSymbols := by
    simp [e, transition, TableProgram.supportedSymbols]
  have hnext : e.next ∈ (program (true :: bs)).supportedStates := by
    simp [e, transition, TableProgram.supportedStates]
  have hhalt : e.next = (program (true :: bs)).halt := by
    simp [e, transition]
  exact TableProgram.toMachine_haltsEmpty_of_initial_transition_to_halt
    hfind hwrite hnext hhalt

theorem program_cons_false_runEmpty_one (bs : List Bool) :
    (program (false :: bs)).toMachine.runEmpty 1 =
      { tape := fun _ => 0, head := 1, state := 1 } := by
  let e := transition ((false :: bs).length + 1) 0 false
  have htable : (program (false :: bs)).table =
      e :: transitionsFrom ((false :: bs).length + 1) 1 bs := by
    change transitions (false :: bs) =
      transition ((false :: bs).length + 1) 0 false ::
        transitionsFrom ((false :: bs).length + 1) 1 bs
    rw [transitions_eq_transitionsFrom]
    rfl
  have hfind :
      (program (false :: bs)).toTableMachine.transition?
          (program (false :: bs)).start (program (false :: bs)).blank = some e :=
    TableProgram.transition?_eq_some_of_table_head_matches htable
      (by simp [e, transition])
  have hwrite : e.write ∈ (program (false :: bs)).supportedSymbols := by
    simp [e, transition, TableProgram.supportedSymbols]
  have hnext : e.next ∈ (program (false :: bs)).supportedStates := by
    unfold TableProgram.supportedStates
    right
    right
    change 1 ∈ List.range ((false :: bs).length + 1)
    rw [List.mem_range]
    simp
  have hstart : (program (false :: bs)).start ≠ (program (false :: bs)).halt :=
    program_start_ne_halt (false :: bs)
  have hrun := TableProgram.toMachine_runEmpty_one_of_initial_transition
    hstart hfind hwrite hnext
  simpa [e, transition, Move.apply] using hrun

theorem transition_primrec :
    Primrec (fun p : Nat × Nat × Bool => transition p.1 p.2.1 p.2.2) := by
  unfold transition
  have hnext : Primrec (fun p : Nat × Nat × Bool =>
      if p.2.2 then p.1 else p.2.1 + 1) := by
    have hpred : PrimrecPred (fun p : Nat × Nat × Bool => p.2.2 = true) :=
      Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true)
    exact Primrec.ite hpred Primrec.fst
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
  exact TableTransition.mk_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const 0)
          (Primrec.pair hnext (Primrec.const Move.right)))))

theorem loopTransition_primrec :
    Primrec loopTransition := by
  unfold loopTransition
  exact TableTransition.mk_primrec.comp
    (Primrec.pair Primrec.id
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const 0)
          (Primrec.pair Primrec.id (Primrec.const Move.right)))))

theorem foldStep₂_primrec :
    Primrec₂ foldStep₂ := by
  apply Primrec₂.mk
  unfold foldStep₂ foldStep
  have hhalt : Primrec (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
      p.1.length + 1) :=
    Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)
  have hacc : Primrec (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
      p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hstate : Primrec (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
      p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hbit : Primrec (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
      p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have htransition : Primrec
      (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
        transition (p.1.length + 1) p.2.1.2 p.2.2) :=
    transition_primrec.comp (Primrec.pair hhalt (Primrec.pair hstate hbit))
  have hsingleton : Primrec
      (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
        [transition (p.1.length + 1) p.2.1.2 p.2.2]) :=
    Primrec.list_cons.comp htransition (Primrec.const [])
  have htransitions : Primrec
      (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
        p.2.1.1 ++ [transition (p.1.length + 1) p.2.1.2 p.2.2]) :=
    Primrec.list_append.comp hacc hsingleton
  have hnextState : Primrec
      (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
        p.2.1.2 + 1) :=
    Primrec.succ.comp hstate
  exact Primrec.pair htransitions hnextState

theorem folded_primrec :
    Primrec folded := by
  unfold folded
  exact Primrec.list_foldl Primrec.id
    (Primrec.const (([] : List TableTransition), 0)) foldStep₂_primrec

theorem transitions_primrec :
    Primrec transitions := by
  unfold transitions
  have hloop : Primrec (fun bs : List Bool => loopTransition (folded bs).2) :=
    loopTransition_primrec.comp (Primrec.snd.comp folded_primrec)
  have hsingleton : Primrec (fun bs : List Bool => [loopTransition (folded bs).2]) :=
    Primrec.list_cons.comp hloop (Primrec.const ([] : List TableTransition))
  exact Primrec.list_append.comp (Primrec.fst.comp folded_primrec) hsingleton

theorem program_primrec :
    Primrec program := by
  unfold program
  have hlengthSucc : Primrec (fun bs : List Bool => bs.length + 1) :=
    Primrec.succ.comp Primrec.list_length
  exact TableProgram.mk_primrec.comp
    (Primrec.pair (Primrec.const ([] : List Nat))
      (Primrec.pair (Primrec.list_range.comp hlengthSucc)
        (Primrec.pair (Primrec.const 0)
          (Primrec.pair (Primrec.const 0)
            (Primrec.pair hlengthSucc transitions_primrec)))))

theorem program_computable :
    Computable program :=
  program_primrec.to_comp

end FiniteSearchProgram

end LeanWang
