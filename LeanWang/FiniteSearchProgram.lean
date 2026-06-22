/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.FuelMachine
import LeanWang.Machine

/-!
Finite Boolean search programs.

This file builds a small generated `TableProgram` that scans a finite list of
Boolean markers. At state `i`, a `true` marker jumps to halt and a `false`
marker advances to state `i + 1`; after the list is exhausted, the machine loops
right forever on blank tape. This is a finite control-flow fragment of the
eventual fuel-search compiler/reduction.
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

theorem replicate_false_append_split {k n : Nat} (hk : k ≤ n) (bs : List Bool) :
    List.replicate n false ++ bs =
      List.replicate k false ++ (List.replicate (n - k) false ++ bs) := by
  rw [← List.append_assoc, ← List.replicate_add]
  rw [Nat.add_sub_of_le hk]

theorem replicate_false_append_split_succ {k n : Nat} (hk : k + 1 ≤ n)
    (bs : List Bool) :
    List.replicate n false ++ bs =
      List.replicate k false ++
        (false :: (List.replicate (n - (k + 1)) false ++ bs)) := by
  rw [replicate_false_append_split (k := k) (n := n) (by omega) bs]
  rw [show n - k = n - (k + 1) + 1 by omega]
  simp [List.replicate_succ]

theorem program_runEmpty_false_prefix_aux (n : Nat) (bs : List Bool) :
    ∀ k : Nat, k ≤ n →
      (program (List.replicate n false ++ bs)).toMachine.runEmpty k =
        { tape := fun _ => 0, head := k, state := k }
  | 0, _ => by
      rfl
  | k + 1, hk => by
      have hk' : k ≤ n := by omega
      rw [Machine.runEmpty_succ, program_runEmpty_false_prefix_aux n bs k hk']
      have hsplit := replicate_false_append_split_succ (k := k) (n := n) hk bs
      have hfind :=
        program_transition?_after_false_prefix k
          (false :: (List.replicate (n - (k + 1)) false ++ bs))
      rw [← hsplit] at hfind
      have hstate :
          k ≠ (program (List.replicate n false ++ bs)).halt := by
        simp [program, List.length_replicate]
        omega
      have hwrite :
          (transition ((List.replicate n false ++ bs).length + 1) k false).write ∈
            (program (List.replicate n false ++ bs)).supportedSymbols := by
        simp [transition, TableProgram.supportedSymbols, program]
      have hnext :
          (transition ((List.replicate n false ++ bs).length + 1) k false).next ∈
            (program (List.replicate n false ++ bs)).supportedStates := by
        unfold TableProgram.supportedStates
        right
        right
        change k + 1 ∈ List.range ((List.replicate n false ++ bs).length + 1)
        rw [List.mem_range]
        simp [List.length_replicate]
        omega
      simpa [transition, Move.apply] using
        TableProgram.toMachine_nextID_of_transition?_eq_some
          (P := program (List.replicate n false ++ bs))
          (c := { tape := fun _ => 0, head := k, state := k })
          hstate hfind hwrite hnext

theorem program_runEmpty_false_prefix (n : Nat) (bs : List Bool) :
    (program (List.replicate n false ++ bs)).toMachine.runEmpty n =
      { tape := fun _ => 0, head := n, state := n } :=
  program_runEmpty_false_prefix_aux n bs n (by rfl)

theorem program_replicate_false_cons_true_halts (n : Nat) (bs : List Bool) :
    (program (List.replicate n false ++ true :: bs)).toMachine.HaltsEmpty := by
  let P := program (List.replicate n false ++ true :: bs)
  let e := transition ((List.replicate n false ++ true :: bs).length + 1) n true
  refine ⟨n + 1, ?_⟩
  rw [Machine.runEmpty_succ, program_runEmpty_false_prefix n (true :: bs)]
  have hfind : P.toTableMachine.transition? n 0 = some e := by
    simpa [P, e] using program_transition?_after_false_prefix n (true :: bs)
  have hstate : n ≠ P.halt := by
    simp [P, program, List.length_replicate]
    omega
  have hwrite : e.write ∈ P.supportedSymbols := by
    simp [P, e, transition, TableProgram.supportedSymbols, program]
  have hnext : e.next ∈ P.supportedStates := by
    simp [P, e, transition, TableProgram.supportedStates, program]
  have hnextID :=
    TableProgram.toMachine_nextID_of_transition?_eq_some
      (P := P) (c := { tape := fun _ => 0, head := n, state := n })
      hstate hfind hwrite hnext
  simpa [P, e, transition, program, List.length_replicate] using
    congrArg ID.state hnextID

theorem program_runEmpty_all_false_from_loop (n : Nat) :
    ∀ m : Nat,
      (program (List.replicate n false)).toMachine.runEmpty (n + m) =
        { tape := fun _ => 0, head := n + m, state := n }
  | 0 => by
      simpa using program_runEmpty_false_prefix n []
  | m + 1 => by
      let P := program (List.replicate n false)
      let e := loopTransition n
      rw [show n + (m + 1) = n + m + 1 by omega]
      rw [Machine.runEmpty_succ, program_runEmpty_all_false_from_loop n m]
      have hfind : P.toTableMachine.transition? n 0 = some e := by
        simpa [P, e] using program_transition?_after_false_prefix n []
      have hstate : n ≠ P.halt := by
        simp [P, program, List.length_replicate]
      have hwrite : e.write ∈ P.supportedSymbols := by
        simp [P, e, loopTransition, TableProgram.supportedSymbols, program]
      have hnext : e.next ∈ P.supportedStates := by
        simp [P, e, loopTransition, TableProgram.supportedStates, program,
          List.length_replicate]
      simpa [P, e, loopTransition, Move.apply, Nat.add_assoc] using
        TableProgram.toMachine_nextID_of_transition?_eq_some
          (P := P) (c := { tape := fun _ => 0, head := n + m, state := n })
          hstate hfind hwrite hnext

theorem program_all_false_not_halts (n : Nat) :
    ¬ (program (List.replicate n false)).toMachine.HaltsEmpty := by
  rintro ⟨t, ht⟩
  by_cases htn : t ≤ n
  · have hrun :
        (program (List.replicate n false)).toMachine.runEmpty t =
          { tape := fun _ => 0, head := t, state := t } := by
        simpa using program_runEmpty_false_prefix_aux n [] t htn
    rw [hrun] at ht
    simp [program, List.length_replicate] at ht
    omega
  · have hnt : n ≤ t := by omega
    rcases Nat.exists_eq_add_of_le hnt with ⟨m, rfl⟩
    have hrun := program_runEmpty_all_false_from_loop n m
    rw [hrun] at ht
    simp [program, List.length_replicate] at ht

theorem eq_replicate_false_of_true_not_mem :
    ∀ bs : List Bool, true ∉ bs → bs = List.replicate bs.length false
  | [], _ => by
      rfl
  | b :: bs, hmem => by
      cases b
      · have htail : true ∉ bs := by
          intro h
          exact hmem (by simp [h])
        have ih := eq_replicate_false_of_true_not_mem bs htail
        change false :: bs = false :: List.replicate bs.length false
        rw [ih]
        simp
      · exact False.elim (hmem (by simp))

theorem exists_replicate_false_cons_true_of_true_mem :
    ∀ bs : List Bool, true ∈ bs →
      ∃ n : Nat, ∃ rest : List Bool, bs = List.replicate n false ++ true :: rest
  | [], hmem => by
      simp at hmem
  | b :: bs, hmem => by
      cases b
      · have htail : true ∈ bs := by
          simpa using hmem
        rcases exists_replicate_false_cons_true_of_true_mem bs htail with
          ⟨n, rest, hbs⟩
        refine ⟨n + 1, rest, ?_⟩
        simp [List.replicate_succ, hbs]
      · exact ⟨0, bs, by rfl⟩

theorem program_correct (bs : List Bool) :
    (program bs).toMachine.HaltsEmpty ↔ true ∈ bs := by
  constructor
  · intro hhalts
    by_contra hmem
    have hfalse := eq_replicate_false_of_true_not_mem bs hmem
    rw [hfalse] at hhalts
    exact program_all_false_not_halts bs.length hhalts
  · intro hmem
    rcases exists_replicate_false_cons_true_of_true_mem bs hmem with
      ⟨n, rest, rfl⟩
    exact program_replicate_false_cons_true_halts n rest

/-- The finite list of fuel-search predicate values tested below `bound`. -/
def fuelPrefix (P : Nat → Bool) (bound : Nat) : List Bool :=
  (List.range bound).map P

theorem fuelPrefix_primrec {P : Nat → Bool} (hP : Primrec P) :
    Primrec (fuelPrefix P) := by
  unfold fuelPrefix
  have hmap : Primrec₂ fun _bound k : Nat => P k := by
    apply Primrec₂.mk
    exact hP.comp Primrec.snd
  exact Primrec.list_map Primrec.list_range hmap

theorem true_mem_fuelPrefix_iff (P : Nat → Bool) (bound : Nat) :
    true ∈ fuelPrefix P bound ↔ ∃ k : Nat, k < bound ∧ P k = true := by
  unfold fuelPrefix
  constructor
  · intro h
    rw [List.mem_map] at h
    rcases h with ⟨k, hk, htrue⟩
    exact ⟨k, by simpa using hk, htrue⟩
  · rintro ⟨k, hk, htrue⟩
    rw [List.mem_map]
    exact ⟨k, by simpa using hk, htrue⟩

theorem program_fuelPrefix_correct (P : Nat → Bool) (bound : Nat) :
    (program (fuelPrefix P bound)).toMachine.HaltsEmpty ↔
      ∃ k : Nat, k < bound ∧ P k = true := by
  rw [program_correct, true_mem_fuelPrefix_iff]

theorem exists_program_fuelPrefix_halts_iff_fuelMachine_halts
    (P : Nat → Bool) :
    (∃ bound : Nat, (program (fuelPrefix P bound)).toMachine.HaltsEmpty) ↔
      FuelMachine.Halts P := by
  rw [FuelMachine.halts_iff_exists_true]
  constructor
  · rintro ⟨bound, hhalts⟩
    rcases (program_fuelPrefix_correct P bound).1 hhalts with ⟨k, _hk, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    exact (program_fuelPrefix_correct P (k + 1)).2
      ⟨k, Nat.lt_succ_self k, hk⟩

/-- A bounded fuel-search prefix for a parameterized Boolean predicate. -/
def fuelPrefixParam {α : Type} (P : α → Nat → Bool) (a : α) (bound : Nat) :
    List Bool :=
  fuelPrefix (P a) bound

theorem fuelPrefixParam_primrec {α : Type} [Primcodable α] {P : α → Nat → Bool}
    (hP : Primrec fun p : α × Nat => P p.1 p.2) :
    Primrec (fun p : α × Nat => fuelPrefixParam P p.1 p.2) := by
  unfold fuelPrefixParam fuelPrefix
  have hmap : Primrec₂ fun p : α × Nat => fun k : Nat => P p.1 k := by
    apply Primrec₂.mk
    exact hP.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_map (Primrec.list_range.comp Primrec.snd) hmap

theorem program_fuelPrefixParam_correct {α : Type} (P : α → Nat → Bool)
    (a : α) (bound : Nat) :
    (program (fuelPrefixParam P a bound)).toMachine.HaltsEmpty ↔
      ∃ k : Nat, k < bound ∧ P a k = true := by
  exact program_fuelPrefix_correct (P a) bound

theorem exists_program_fuelPrefixParam_halts_iff_fuelMachine_halts
    {α : Type} (P : α → Nat → Bool) (a : α) :
    (∃ bound : Nat, (program (fuelPrefixParam P a bound)).toMachine.HaltsEmpty) ↔
      FuelMachine.Halts (P a) := by
  exact exists_program_fuelPrefix_halts_iff_fuelMachine_halts (P a)

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
