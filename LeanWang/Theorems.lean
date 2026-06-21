/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/
import LeanWang.Compactness
import LeanWang.FuelMachine
import LeanWang.Machine
import LeanWang.MachineTiles
import Mathlib.Computability.Reduce
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
Main theorem surface for the Wang-tile undecidability proof.

This file collects the main reduction theorems. The final undecidability theorem
is currently parameterized by the two external construction obligations: a
compiler from Mathlib partial-recursive codes to finite table machines, and a
concrete scaffold satisfying the abstract square-forcing property.
-/

namespace LeanWang

open Nat.Partrec (Code)

theorem part_dom_map_iff {α β : Type} (f : α → β) (p : Part α) :
    (f <$> p).Dom ↔ p.Dom := by
  rw [Part.map_eq_map]
  rfl

/--
Bounded Mathlib code evaluation succeeds at some fuel exactly when full
evaluation is defined.
-/
theorem code_eval_dom_iff_exists_evaln (c : Code) (n : Nat) :
    (Nat.Partrec.Code.eval c n).Dom ↔
      ∃ k x : Nat, x ∈ Nat.Partrec.Code.evaln k c n := by
  constructor
  · intro hdom
    rcases Part.dom_iff_mem.1 hdom with ⟨x, hx⟩
    rcases Nat.Partrec.Code.evaln_complete.1 hx with ⟨k, hk⟩
    exact ⟨k, x, hk⟩
  · rintro ⟨k, x, hx⟩
    exact Part.dom_iff_mem.2 ⟨x, Nat.Partrec.Code.evaln_sound hx⟩

/-- Boolean bounded halting predicate for `Nat.Partrec.Code.evaln`. -/
def codeEvalnHalts (c : Code) (n k : Nat) : Bool :=
  (Nat.Partrec.Code.evaln k c n).isSome

theorem code_eval_dom_iff_exists_codeEvalnHalts (c : Code) (n : Nat) :
    (Nat.Partrec.Code.eval c n).Dom ↔ ∃ k : Nat, codeEvalnHalts c n k = true := by
  rw [code_eval_dom_iff_exists_evaln]
  constructor
  · rintro ⟨k, x, hx⟩
    refine ⟨k, ?_⟩
    cases h : Nat.Partrec.Code.evaln k c n with
    | none =>
        simp [Option.mem_def, h] at hx
    | some y =>
        simp [codeEvalnHalts, h]
  · rintro ⟨k, hk⟩
    cases h : Nat.Partrec.Code.evaln k c n with
    | none =>
        simp [codeEvalnHalts, h] at hk
    | some x =>
        exact ⟨k, x, by simp [Option.mem_def, h]⟩

theorem codeEvalnHalts_primrec :
    Primrec fun a : (Nat × Code) × Nat => codeEvalnHalts a.1.2 a.2 a.1.1 := by
  simpa [codeEvalnHalts] using
    Primrec.option_isSome.comp Nat.Partrec.Code.primrec_evaln

theorem codeEvaln_nonhalting_undecidable :
    ¬ ComputablePred (fun c : Code => ¬ ∃ k : Nat, codeEvalnHalts c 0 k = true) := by
  intro h
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    h.of_eq fun c => by
      rw [code_eval_dom_iff_exists_codeEvalnHalts]
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

theorem codeEvalnFuelMachine_correct (c : Code) (n : Nat) :
    FuelMachine.Halts (codeEvalnHalts c n) ↔ (Nat.Partrec.Code.eval c n).Dom := by
  rw [FuelMachine.halts_iff_exists_true, code_eval_dom_iff_exists_codeEvalnHalts]

/--
Every Mathlib `Nat.Partrec.Code` has a corresponding `Turing.ToPartrec.Code`
whose singleton-list output is defined exactly when the original unary code is
defined.
-/
theorem exists_toPartrecCode_for_natPartrecCode (c : Code) :
    ∃ tc : Turing.ToPartrec.Code,
      ∀ n : Nat,
        (Turing.ToPartrec.Code.eval tc [n]).Dom ↔
          (Nat.Partrec.Code.eval c n).Dom := by
  have hpart : Partrec (Nat.Partrec.Code.eval c) :=
    (Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.id).of_eq
      fun n => by rfl
  rcases Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.2 hpart) with
    ⟨tc, htc⟩
  refine ⟨tc, fun n => ?_⟩
  let v : List.Vector Nat 1 := ⟨[n], by simp⟩
  have hv : v.head = n := rfl
  have htc' :
      Turing.ToPartrec.Code.eval tc [n] =
        pure <$> Nat.Partrec.Code.eval c n := by
    simpa [v, hv] using htc v
  rw [htc']
  exact part_dom_map_iff pure (Nat.Partrec.Code.eval c n)

/--
Mathlib's TM2 evaluator for the translated `ToPartrec.Code` halts exactly when
the original `Nat.Partrec.Code` halts on input `0`.
-/
theorem exists_tm2_for_natPartrecCode (c : Code) :
    ∃ tc : Turing.ToPartrec.Code,
      (StateTransition.eval
          (Turing.TM2.step Turing.PartrecToTM2.tr)
          (Turing.PartrecToTM2.init tc [0])).Dom ↔
        (Nat.Partrec.Code.eval c 0).Dom := by
  rcases exists_toPartrecCode_for_natPartrecCode c with ⟨tc, htc⟩
  refine ⟨tc, ?_⟩
  rw [Turing.PartrecToTM2.tr_eval tc [0]]
  exact (part_dom_map_iff Turing.PartrecToTM2.halt
    (Turing.ToPartrec.Code.eval tc [0])).trans (htc 0)

/-- A small sample table program, useful for concrete tests and examples. -/
def dummyProgram : TableProgram where
  symbols := []
  states := []
  blank := 0
  start := 0
  halt := 1
  table := [{
    state := 0
    read := 0
    write := 0
    next := 1
    move := Move.right
  }]

/-- A compiler from Mathlib partial-recursive codes into finite table-machine data. -/
structure TableCompiler where
  compile : Code → TableProgram
  compile_computable : Computable compile
  correct : ∀ c : Code,
    Machine.HaltsEmpty (compile c).toMachine ↔ (Nat.Partrec.Code.eval c 0).Dom

/--
A smaller compiler obligation: implement the fuel-search machine for the
primitive-recursive bounded evaluator predicate.
-/
structure FuelTableCompiler where
  compile : Code → TableProgram
  compile_computable : Computable compile
  correct : ∀ c : Code,
    Machine.HaltsEmpty (compile c).toMachine ↔ FuelMachine.Halts (codeEvalnHalts c 0)

def FuelTableCompiler.toTableCompiler (C : FuelTableCompiler) : TableCompiler where
  compile := C.compile
  compile_computable := C.compile_computable
  correct := by
    intro c
    exact (C.correct c).trans (codeEvalnFuelMachine_correct c 0)

/-- Compile a Mathlib partial-recursive code into finite machine data. -/
def programTable (C : TableCompiler) (c : Code) : TableProgram :=
  C.compile c

theorem programTable_computable (C : TableCompiler) : Computable (programTable C) := by
  exact C.compile_computable

/-- Compile a Mathlib partial-recursive code into the concrete one-tape machine model. -/
def programMachine (C : TableCompiler) (c : Code) : Machine :=
  (programTable C c).toMachine

/-- Correctness of a compiler from partial-recursive codes to concrete machines. -/
theorem programMachine_correct (C : TableCompiler) (c : Code) :
    Machine.HaltsEmpty (programMachine C c) ↔ (Nat.Partrec.Code.eval c 0).Dom :=
  C.correct c

/-- Correctness of the machine-to-Wang-tile fixed domino construction. -/
theorem machineTiles_correct (M : Machine) :
    TilesQuarterWithSeed (machineTiles M) (machineSeed M) ↔ ¬ Machine.HaltsEmpty M := by
  constructor
  · intro htiles hhalts
    rcases hhalts with ⟨n, hhalt⟩
    exact not_tilesQuarterWithSeed_machineTiles_of_halts_at n hhalt htiles
  · intro hnonhalts
    exact tilesQuarterWithSeed_machineTiles_of_not_halts hnonhalts

/-- Correctness of the table-program fixed-domino construction. -/
theorem tableProgramFixedDomino_correct (P : TableProgram) :
    TilesQuarterWithSeed (tableProgramFixedDomino P).1 (tableProgramFixedDomino P).2 ↔
      ¬ Machine.HaltsEmpty P.toMachine := by
  unfold tableProgramFixedDomino tableProgramTiles tableProgramSeed
  exact machineTiles_correct P.toMachine

/-- Fixed domino instance produced from a partial-recursive code. -/
def fixedDominoReduction (C : TableCompiler) (c : Code) : TileSet × WangTile :=
  tableProgramFixedDominoData (programTable C c)

theorem fixedDominoReduction_computable (C : TableCompiler) :
    Computable (fixedDominoReduction C) := by
  exact tableProgramFixedDominoData_computable.comp (programTable_computable C)

/-- Correctness of the fixed domino reduction from nonhalting. -/
theorem fixedDominoReduction_correct (C : TableCompiler) (c : Code) :
    TilesQuarterWithSeed (fixedDominoReduction C c).1 (fixedDominoReduction C c).2 ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  unfold fixedDominoReduction
  rw [tableProgramFixedDominoData_seed_eq]
  rw [tilesQuarterWithSeed_congr
    (tableProgramFixedDominoData_mem_iff (programTable C c))]
  rw [tableProgramFixedDomino_correct]
  change ¬ Machine.HaltsEmpty (programMachine C c) ↔ ¬ (Nat.Partrec.Code.eval c 0).Dom
  rw [programMachine_correct C]

/-- The fixed domino problem is undecidable, in reduction form. -/
theorem fixed_domino_problem_undecidable (C : TableCompiler) :
    ¬ ComputablePred
      (fun c : Code =>
        TilesQuarterWithSeed (fixedDominoReduction C c).1 (fixedDominoReduction C c).2) := by
  intro h
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    h.of_eq fun c => fixedDominoReduction_correct C c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/-- The fixed-corner finite-square problem is undecidable, in reduction form. -/
theorem fixed_corner_square_problem_undecidable (C : TableCompiler) :
    ¬ ComputablePred
      (fun c : Code =>
        ∀ n : Nat, 0 < n → TileableFixedCornerSquare
          (fixedDominoReduction C c).1 (fixedDominoReduction C c).2 n) := by
  intro h
  apply fixed_domino_problem_undecidable C
  exact h.of_eq fun c =>
    (tilesQuarterWithSeed_iff_all_fixedCornerSquares
      (fixedDominoReduction C c).1 (fixedDominoReduction C c).2).symm

/-- Fixed-domino undecidability from the smaller fuel-search compiler obligation. -/
theorem fixed_domino_problem_undecidable_of_fuelCompiler (C : FuelTableCompiler) :
    ¬ ComputablePred
      (fun c : Code =>
        TilesQuarterWithSeed
          (fixedDominoReduction C.toTableCompiler c).1
          (fixedDominoReduction C.toTableCompiler c).2) :=
  fixed_domino_problem_undecidable C.toTableCompiler

/-- Fixed-corner square undecidability from the smaller fuel-search compiler obligation. -/
theorem fixed_corner_square_problem_undecidable_of_fuelCompiler (C : FuelTableCompiler) :
    ¬ ComputablePred
      (fun c : Code =>
        ∀ n : Nat, 0 < n → TileableFixedCornerSquare
          (fixedDominoReduction C.toTableCompiler c).1
          (fixedDominoReduction C.toTableCompiler c).2 n) :=
  fixed_corner_square_problem_undecidable C.toTableCompiler

/-- Data for a scaffold tileset used to force arbitrarily large free squares. -/
structure Scaffold where
  tiles : TileSet
  active : WangTile → Bool
  corner : WangTile
  active_primrec : Primrec active

/--
Payload symbols carried by a scaffold tile. Active scaffold cells carry the
instance tileset, with the marked corner restricted to the requested seed.
Inactive scaffold cells carry one dummy payload tile, so they do not force the
instance tileset outside the free regions.
-/
def scaffoldPayloads (S : Scaffold) (T : TileSet) (seed b : WangTile) : TileSet :=
  if S.active b then
    if b = S.corner then T.filter fun p => p = seed else T
  else
    [monochromeTile]

/-- Combine a scaffold with a fixed-corner square instance. -/
def combineWithScaffold (S : Scaffold) (T : TileSet) (seed : WangTile) : TileSet :=
  S.tiles.flatMap fun b =>
    (scaffoldPayloads S T seed b).map fun p => WangTile.product b p

theorem mem_combineWithScaffold_iff {S : Scaffold} {T : TileSet}
    {seed tile : WangTile} :
    tile ∈ combineWithScaffold S T seed ↔
      ∃ b ∈ S.tiles, ∃ p : WangTile,
        (S.active b = true → p ∈ T ∧ (b = S.corner → p = seed)) ∧
          (S.active b = false → p = monochromeTile) ∧
          WangTile.product b p = tile := by
  constructor
  · intro htile
    rw [combineWithScaffold, List.mem_flatMap] at htile
    rcases htile with ⟨b, hb, hpayload⟩
    by_cases hactive : S.active b = true
    · rw [scaffoldPayloads, if_pos hactive] at hpayload
      by_cases hcorner : b = S.corner
      · rw [if_pos hcorner, List.mem_map] at hpayload
        rcases hpayload with ⟨p, hp, htile⟩
        refine ⟨b, hb, p, ?_⟩
        have hmem : S.active b = true → p ∈ T ∧ (b = S.corner → p = seed) := by
          intro _hactive
          exact ⟨(List.mem_filter.1 hp).1,
            by intro _; exact of_decide_eq_true (List.mem_filter.1 hp).2⟩
        have hinactive : S.active b = false → p = monochromeTile := by
          intro hfalse
          rw [hactive] at hfalse
          nomatch hfalse
        exact And.intro hmem (And.intro hinactive htile)
      · rw [if_neg hcorner, List.mem_map] at hpayload
        rcases hpayload with ⟨p, hp, htile⟩
        refine ⟨b, hb, p, ?_⟩
        have hmem : S.active b = true → p ∈ T ∧ (b = S.corner → p = seed) := by
          intro _hactive
          exact ⟨hp, by intro hbcorner; exact False.elim (hcorner hbcorner)⟩
        have hinactive : S.active b = false → p = monochromeTile := by
          intro hfalse
          rw [hactive] at hfalse
          nomatch hfalse
        exact And.intro hmem (And.intro hinactive htile)
    · have hfalse : S.active b = false := by
        cases h : S.active b
        · rfl
        · exact False.elim (hactive h)
      rw [scaffoldPayloads, if_neg hactive, List.mem_map] at hpayload
      rcases hpayload with ⟨p, hp, htile⟩
      rw [List.mem_singleton] at hp
      refine ⟨b, hb, p, ?_⟩
      have hmem : S.active b = true → p ∈ T ∧ (b = S.corner → p = seed) := by
        intro htrue
        rw [hfalse] at htrue
        nomatch htrue
      have hinactive : S.active b = false → p = monochromeTile := by
        intro _
        exact hp
      exact And.intro hmem (And.intro hinactive htile)
  · rintro ⟨b, hb, p, hactiveMem, hinactive, htile⟩
    rw [combineWithScaffold, List.mem_flatMap]
    refine ⟨b, hb, ?_⟩
    by_cases hactive : S.active b = true
    · rw [scaffoldPayloads, if_pos hactive]
      by_cases hcorner : b = S.corner
      · rw [if_pos hcorner, List.mem_map]
        exact ⟨p, List.mem_filter.2 ⟨(hactiveMem hactive).1,
          decide_eq_true ((hactiveMem hactive).2 hcorner)⟩, htile⟩
      · rw [if_neg hcorner, List.mem_map]
        exact ⟨p, (hactiveMem hactive).1, htile⟩
    · rw [scaffoldPayloads, if_neg hactive, List.mem_map]
      exact ⟨p, by rw [List.mem_singleton]; exact hinactive (by
        cases h : S.active b
        · rfl
        · exact False.elim (hactive h)), htile⟩

theorem payload_mem_of_product_corner_mem_combineWithScaffold {S : Scaffold}
    {T : TileSet} {seed payload : WangTile}
    (hactive : S.active S.corner = true)
    (htile : WangTile.product S.corner payload ∈ combineWithScaffold S T seed) :
    payload ∈ T := by
  rcases mem_combineWithScaffold_iff.1 htile with ⟨b, _hb, p, hactiveMem, _hinactive, hproduct⟩
  have hparts : b = S.corner ∧ p = payload := product_eq_iff.1 hproduct
  simpa [hparts.2] using (hactiveMem (by simpa [hparts.1] using hactive)).1

theorem payload_eq_seed_of_product_corner_mem_combineWithScaffold {S : Scaffold}
    {T : TileSet} {seed payload : WangTile}
    (hactive : S.active S.corner = true)
    (htile : WangTile.product S.corner payload ∈ combineWithScaffold S T seed) :
    payload = seed := by
  rcases mem_combineWithScaffold_iff.1 htile with ⟨b, _hb, p, hactiveMem, _hinactive, hproduct⟩
  have hparts : b = S.corner ∧ p = payload := product_eq_iff.1 hproduct
  exact hparts.2.symm.trans ((hactiveMem (by simpa [hparts.1] using hactive)).2 hparts.1)

theorem payload_mem_of_active_product_mem_combineWithScaffold {S : Scaffold}
    {T : TileSet} {seed base payload : WangTile}
    (hactive : S.active base = true)
    (htile : WangTile.product base payload ∈ combineWithScaffold S T seed) :
    payload ∈ T := by
  rcases mem_combineWithScaffold_iff.1 htile with ⟨b, _hb, p, hactiveMem, _hinactive, hproduct⟩
  have hparts : b = base ∧ p = payload := product_eq_iff.1 hproduct
  simpa [hparts.2] using (hactiveMem (by simpa [hparts.1] using hactive)).1

theorem payload_eq_seed_of_active_corner_product_mem_combineWithScaffold {S : Scaffold}
    {T : TileSet} {seed base payload : WangTile}
    (hactive : S.active base = true) (hcorner : base = S.corner)
    (htile : WangTile.product base payload ∈ combineWithScaffold S T seed) :
    payload = seed := by
  rcases mem_combineWithScaffold_iff.1 htile with ⟨b, _hb, p, hactiveMem, _hinactive, hproduct⟩
  have hparts : b = base ∧ p = payload := product_eq_iff.1 hproduct
  exact hparts.2.symm.trans
    ((hactiveMem (by simpa [hparts.1] using hactive)).2 (hparts.1.trans hcorner))

theorem tilesPlane_scaffold_of_tilesPlane_combineWithScaffold {S : Scaffold}
    {T : TileSet} {seed : WangTile}
    (h : TilesPlane (combineWithScaffold S T seed)) :
    TilesPlane S.tiles := by
  classical
  rcases h with ⟨x, hx⟩
  have hdecode : ∀ p : Int × Int,
      ∃ b : TileIn S.tiles, ∃ payload : WangTile,
        WangTile.product b.1 payload = (x p).1 := by
    intro p
    rcases mem_combineWithScaffold_iff.1 (x p).2 with
      ⟨b, hb, payload, _hactiveMem, _hinactive, htile⟩
    exact ⟨⟨b, hb⟩, payload, htile⟩
  let baseAt : Int × Int → TileIn S.tiles := fun p => Classical.choose (hdecode p)
  let payloadAt : Int × Int → WangTile := fun p =>
    Classical.choose (Classical.choose_spec (hdecode p))
  have hproduct : ∀ p : Int × Int,
      WangTile.product (baseAt p).1 (payloadAt p) = (x p).1 := by
    intro p
    exact Classical.choose_spec (Classical.choose_spec (hdecode p))
  refine ⟨baseAt, ?_⟩
  constructor
  · intro p
    have hmatch : WangTile.HMatches
        (WangTile.product (baseAt p).1 (payloadAt p))
        (WangTile.product (baseAt (p.1 + 1, p.2)).1 (payloadAt (p.1 + 1, p.2))) := by
      simpa [hproduct p, hproduct (p.1 + 1, p.2)] using hx.1 p
    exact (WangTile.HMatches_product_iff
      (baseAt p).1 (payloadAt p)
      (baseAt (p.1 + 1, p.2)).1 (payloadAt (p.1 + 1, p.2))).1 hmatch |>.1
  · intro p
    have hmatch : WangTile.VMatches
        (WangTile.product (baseAt p).1 (payloadAt p))
        (WangTile.product (baseAt (p.1, p.2 + 1)).1 (payloadAt (p.1, p.2 + 1))) := by
      simpa [hproduct p, hproduct (p.1, p.2 + 1)] using hx.2 p
    exact (WangTile.VMatches_product_iff
      (baseAt p).1 (payloadAt p)
      (baseAt (p.1, p.2 + 1)).1 (payloadAt (p.1, p.2 + 1))).1 hmatch |>.1

/-- Decoded layers of a finite rectangle over a scaffold-combined tileset. -/
def ValidCombinedRectangleLayers (S : Scaffold) (T : TileSet) (seed : WangTile)
    {w h : Nat} (rect baseRect payloadRect : Rectangle w h) : Prop :=
  ValidRectangle S.tiles baseRect ∧
    (∀ i : Fin w, ∀ j : Fin h,
      WangTile.product (baseRect i j) (payloadRect i j) = rect i j) ∧
    (∀ i : Fin w, ∀ j : Fin h,
      S.active (baseRect i j) = true →
        payloadRect i j ∈ T ∧ (baseRect i j = S.corner → payloadRect i j = seed)) ∧
    (∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
      WangTile.HMatches (payloadRect i j) (payloadRect ⟨i.val + 1, hi⟩ j)) ∧
    (∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
      WangTile.VMatches (payloadRect i j) (payloadRect i ⟨j.val + 1, hj⟩))

theorem exists_validCombinedRectangleLayers_of_validRectangle_combineWithScaffold
    {S : Scaffold} {T : TileSet} {seed : WangTile}
    {w h : Nat} {rect : Rectangle w h}
    (hrect : ValidRectangle (combineWithScaffold S T seed) rect) :
    ∃ baseRect payloadRect : Rectangle w h,
      ValidCombinedRectangleLayers S T seed rect baseRect payloadRect := by
  classical
  have hdecode : ∀ i : Fin w, ∀ j : Fin h,
      ∃ b : TileIn S.tiles, ∃ payload : WangTile,
        (S.active b.1 = true →
          payload ∈ T ∧ (b.1 = S.corner → payload = seed)) ∧
          WangTile.product b.1 payload = rect i j := by
    intro i j
    rcases mem_combineWithScaffold_iff.1 (hrect.1 i j) with
      ⟨b, hb, payload, hactiveMem, _hinactive, htile⟩
    exact ⟨⟨b, hb⟩, payload, hactiveMem, htile⟩
  let baseAt : Fin w → Fin h → TileIn S.tiles := fun i j => Classical.choose (hdecode i j)
  let payloadAt : Rectangle w h := fun i j =>
    Classical.choose (Classical.choose_spec (hdecode i j))
  have hactiveMem : ∀ i : Fin w, ∀ j : Fin h,
      S.active (baseAt i j).1 = true →
        payloadAt i j ∈ T ∧ ((baseAt i j).1 = S.corner → payloadAt i j = seed) := by
    intro i j
    exact (Classical.choose_spec (Classical.choose_spec (hdecode i j))).1
  have hproduct : ∀ i : Fin w, ∀ j : Fin h,
      WangTile.product (baseAt i j).1 (payloadAt i j) = rect i j := by
    intro i j
    exact (Classical.choose_spec (Classical.choose_spec (hdecode i j))).2
  refine ⟨fun i j => (baseAt i j).1, payloadAt, ?_⟩
  unfold ValidCombinedRectangleLayers
  constructor
  · constructor
    · intro i j
      exact (baseAt i j).2
    constructor
    · intro i j hi
      have hmatch : WangTile.HMatches
          (WangTile.product (baseAt i j).1 (payloadAt i j))
          (WangTile.product (baseAt ⟨i.val + 1, hi⟩ j).1
            (payloadAt ⟨i.val + 1, hi⟩ j)) := by
        simpa [hproduct i j, hproduct ⟨i.val + 1, hi⟩ j] using hrect.2.1 i j hi
      exact (WangTile.HMatches_product_iff
        (baseAt i j).1 (payloadAt i j)
        (baseAt ⟨i.val + 1, hi⟩ j).1 (payloadAt ⟨i.val + 1, hi⟩ j)).1 hmatch |>.1
    · intro i j hj
      have hmatch : WangTile.VMatches
          (WangTile.product (baseAt i j).1 (payloadAt i j))
          (WangTile.product (baseAt i ⟨j.val + 1, hj⟩).1
            (payloadAt i ⟨j.val + 1, hj⟩)) := by
        simpa [hproduct i j, hproduct i ⟨j.val + 1, hj⟩] using hrect.2.2 i j hj
      exact (WangTile.VMatches_product_iff
        (baseAt i j).1 (payloadAt i j)
        (baseAt i ⟨j.val + 1, hj⟩).1 (payloadAt i ⟨j.val + 1, hj⟩)).1 hmatch |>.1
  constructor
  · intro i j
    exact hproduct i j
  constructor
  · intro i j
    exact hactiveMem i j
  constructor
  · intro i j hi
    have hmatch : WangTile.HMatches
        (WangTile.product (baseAt i j).1 (payloadAt i j))
        (WangTile.product (baseAt ⟨i.val + 1, hi⟩ j).1
          (payloadAt ⟨i.val + 1, hi⟩ j)) := by
      simpa [hproduct i j, hproduct ⟨i.val + 1, hi⟩ j] using hrect.2.1 i j hi
    exact (WangTile.HMatches_product_iff
      (baseAt i j).1 (payloadAt i j)
      (baseAt ⟨i.val + 1, hi⟩ j).1 (payloadAt ⟨i.val + 1, hi⟩ j)).1 hmatch |>.2
  · intro i j hj
    have hmatch : WangTile.VMatches
        (WangTile.product (baseAt i j).1 (payloadAt i j))
        (WangTile.product (baseAt i ⟨j.val + 1, hj⟩).1
          (payloadAt i ⟨j.val + 1, hj⟩)) := by
      simpa [hproduct i j, hproduct i ⟨j.val + 1, hj⟩] using hrect.2.2 i j hj
    exact (WangTile.VMatches_product_iff
      (baseAt i j).1 (payloadAt i j)
      (baseAt i ⟨j.val + 1, hj⟩).1 (payloadAt i ⟨j.val + 1, hj⟩)).1 hmatch |>.2

theorem validRectangle_payload_of_validCombinedRectangleLayers_of_active
    {S : Scaffold} {T : TileSet} {seed : WangTile}
    {w h : Nat} {rect baseRect payloadRect : Rectangle w h}
    (hlayers : ValidCombinedRectangleLayers S T seed rect baseRect payloadRect)
    (hactive : ∀ i : Fin w, ∀ j : Fin h, S.active (baseRect i j) = true) :
    ValidRectangle T payloadRect := by
  constructor
  · intro i j
    exact (hlayers.2.2.1 i j (hactive i j)).1
  constructor
  · intro i j hi
    exact hlayers.2.2.2.1 i j hi
  · intro i j hj
    exact hlayers.2.2.2.2 i j hj

theorem tileableFixedCornerSquare_payload_of_validCombinedRectangleLayers_of_active_corner
    {S : Scaffold} {T : TileSet} {seed : WangTile}
    {n : Nat} {rect baseRect payloadRect : Rectangle n n}
    (hn : 0 < n)
    (hlayers : ValidCombinedRectangleLayers S T seed rect baseRect payloadRect)
    (hactive : ∀ i : Fin n, ∀ j : Fin n, S.active (baseRect i j) = true)
    (hcorner : baseRect ⟨0, hn⟩ ⟨0, hn⟩ = S.corner) :
    TileableFixedCornerSquare T seed n := by
  refine ⟨hn, payloadRect, ?_, ?_⟩
  · exact validRectangle_payload_of_validCombinedRectangleLayers_of_active hlayers hactive
  · exact (hlayers.2.2.1 ⟨0, hn⟩ ⟨0, hn⟩ (hactive ⟨0, hn⟩ ⟨0, hn⟩)).2 hcorner

def PlaneTilingHasActiveCornerBaseWindows (S : Scaffold) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold S T seed)),
    ValidPlaneTiling (combineWithScaffold S T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ origin : Int × Int, ∃ baseRect : Rectangle n n,
          (∀ i : Fin n, ∀ j : Fin n, S.active (baseRect i j) = true) ∧
            baseRect ⟨0, hn⟩ ⟨0, hn⟩ = S.corner ∧
            ∀ i : Fin n, ∀ j : Fin n, ∃ payload : WangTile,
              WangTile.product (baseRect i j) payload =
                (x (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val)).1

def PlaneTilingForcesActiveCornerWindows (S : Scaffold) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold S T seed)),
    ValidPlaneTiling (combineWithScaffold S T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ rect baseRect payloadRect : Rectangle n n,
          ValidCombinedRectangleLayers S T seed rect baseRect payloadRect ∧
            (∀ i : Fin n, ∀ j : Fin n, S.active (baseRect i j) = true) ∧
            baseRect ⟨0, hn⟩ ⟨0, hn⟩ = S.corner

theorem planeTilingForcesActiveCornerWindows_of_hasActiveCornerBaseWindows
    {S : Scaffold} (hS : PlaneTilingHasActiveCornerBaseWindows S) :
    PlaneTilingForcesActiveCornerWindows S := by
  intro T seed x hx n hn
  rcases hS x hx n hn with ⟨origin, forcedBase, hforcedActive, hforcedCorner, hforcedProduct⟩
  let rect : Rectangle n n := fun i j =>
    (x (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val)).1
  have hrect : ValidRectangle (combineWithScaffold S T seed) rect := by
    constructor
    · intro i j
      exact (x (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val)).2
    constructor
    · intro i j hi
      convert hx.1 (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val) using 2
      ext
      all_goals simp [Nat.cast_add, add_assoc]
    · intro i j hj
      convert hx.2 (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val) using 2
      ext
      all_goals simp [Nat.cast_add, add_assoc]
  rcases exists_validCombinedRectangleLayers_of_validRectangle_combineWithScaffold
      (S := S) (T := T) (seed := seed) hrect with
    ⟨baseRect, payloadRect, hlayers⟩
  refine ⟨rect, baseRect, payloadRect, hlayers, ?_, ?_⟩
  · intro i j
    rcases hforcedProduct i j with ⟨payload, hproduct⟩
    have hbase : baseRect i j = forcedBase i j := by
      exact (product_eq_iff.1 ((hlayers.2.1 i j).trans hproduct.symm)).1
    simpa [hbase] using hforcedActive i j
  · rcases hforcedProduct ⟨0, hn⟩ ⟨0, hn⟩ with ⟨payload, hproduct⟩
    have hbase : baseRect ⟨0, hn⟩ ⟨0, hn⟩ = forcedBase ⟨0, hn⟩ ⟨0, hn⟩ := by
      exact (product_eq_iff.1 ((hlayers.2.1 ⟨0, hn⟩ ⟨0, hn⟩).trans hproduct.symm)).1
    exact hbase.trans hforcedCorner

def ForcesActiveCornerSquares (S : Scaffold) : Prop :=
  ∀ {T : TileSet} {seed : WangTile},
    TilesPlane (combineWithScaffold S T seed) →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ rect baseRect payloadRect : Rectangle n n,
          ValidCombinedRectangleLayers S T seed rect baseRect payloadRect ∧
            (∀ i : Fin n, ∀ j : Fin n, S.active (baseRect i j) = true) ∧
            baseRect ⟨0, hn⟩ ⟨0, hn⟩ = S.corner

theorem forcesActiveCornerSquares_of_planeTilingForcesActiveCornerWindows
    {S : Scaffold} (hS : PlaneTilingForcesActiveCornerWindows S) :
    ForcesActiveCornerSquares S := by
  intro T seed htiles n hn
  rcases htiles with ⟨x, hx⟩
  exact hS x hx n hn

def RealizesActiveCornerSquares (S : Scaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    (∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n) →
      TilesPlane (combineWithScaffold S T seed)

theorem all_fixedCornerSquares_of_tilesPlane_combineWithScaffold
    {S : Scaffold} (hS : ForcesActiveCornerSquares S)
    {T : TileSet} {seed : WangTile}
    (h : TilesPlane (combineWithScaffold S T seed)) :
    ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n := by
  intro n hn
  rcases hS h n hn with ⟨rect, baseRect, payloadRect, hlayers, hactive, hcorner⟩
  exact tileableFixedCornerSquare_payload_of_validCombinedRectangleLayers_of_active_corner
    hn hlayers hactive hcorner

theorem combineWithScaffold_primrec (S : Scaffold) :
    Primrec (fun p : TileSet × WangTile => combineWithScaffold S p.1 p.2) := by
  classical
  unfold combineWithScaffold
  refine Primrec.list_flatMap (Primrec.const S.tiles) ?_
  apply Primrec₂.mk
  have hpayload : Primrec fun a : (TileSet × WangTile) × WangTile =>
      scaffoldPayloads S a.1.1 a.1.2 a.2 := by
    unfold scaffoldPayloads
    have hactive : Primrec fun a : (TileSet × WangTile) × WangTile => S.active a.2 :=
      S.active_primrec.comp Primrec.snd
    refine Primrec.ite (Primrec.eq.comp hactive (Primrec.const true)) ?_
      (Primrec.const ([monochromeTile] : TileSet))
    refine Primrec.ite ?_ ?_ ?_
    · exact Primrec.eq.comp Primrec.snd (Primrec.const S.corner)
    · exact (PrimrecRel.listFilter (R := fun p seed : WangTile => p = seed) Primrec.eq).comp
        (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    · exact Primrec.fst.comp Primrec.fst
  refine Primrec.list_map hpayload ?_
  rw [← Primrec₂.uncurry]
  exact WangTile.product_primrec.comp
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem combineWithScaffold_computable (S : Scaffold) :
    Computable (fun p : TileSet × WangTile => combineWithScaffold S p.1 p.2) :=
  (combineWithScaffold_primrec S).to_comp

/-- The abstract property required of a scaffold for the Berger/Robinson reduction. -/
def IsScaffold (S : Scaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    TilesPlane (combineWithScaffold S T seed) ↔
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n

theorem isScaffold_of_realizesActiveCornerSquares_of_forcesActiveCornerSquares
    {S : Scaffold}
    (hrealizes : RealizesActiveCornerSquares S)
    (hforces : ForcesActiveCornerSquares S) :
    IsScaffold S := by
  intro T seed
  constructor
  · intro htiles
    exact all_fixedCornerSquares_of_tilesPlane_combineWithScaffold hforces htiles
  · intro hsquares
    exact hrealizes T seed hsquares

/-- The concrete Ollinger/Robinson scaffold tileset. -/
def ollingerScaffold : Scaffold where
  tiles := []
  active := fun t => decide (t = monochromeTile)
  corner := monochromeTile
  active_primrec :=
    Primrec.eq.decide.comp Primrec.id (Primrec.const monochromeTile)

/-- Abstract scaffold reduction from fixed-corner squares to ordinary plane tiling. -/
theorem scaffold_reduction_correct {S : Scaffold} (hS : IsScaffold S)
    (T : TileSet) (seed : WangTile) :
    TilesPlane (combineWithScaffold S T seed) ↔
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n :=
  hS T seed

/-- The final Berger/Robinson tileset produced from a partial-recursive code and a scaffold. -/
def dominoReduction (S : Scaffold) (C : TableCompiler) (c : Code) : TileSet :=
  combineWithScaffold S (fixedDominoReduction C c).1 (fixedDominoReduction C c).2

theorem dominoReduction_computable (S : Scaffold) (C : TableCompiler) :
    Computable (dominoReduction S C) := by
  unfold dominoReduction
  exact (combineWithScaffold_computable S).comp (fixedDominoReduction_computable C)

/-- Correctness of the final domino reduction from nonhalting. -/
theorem dominoReduction_correct {S : Scaffold} (hS : IsScaffold S)
    (C : TableCompiler) (c : Code) :
    TilesPlane (dominoReduction S C c) ↔ ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [dominoReduction]
  exact (scaffold_reduction_correct hS
    (fixedDominoReduction C c).1 (fixedDominoReduction C c).2).trans
      ((tilesQuarterWithSeed_iff_all_fixedCornerSquares
        (fixedDominoReduction C c).1 (fixedDominoReduction C c).2).symm.trans
          (fixedDominoReduction_correct C c))

/-- Encoded version of `dominoReduction`, using the canonical finite tileset encoding. -/
def dominoReductionCode (S : Scaffold) (C : TableCompiler) (c : Code) : Nat :=
  encodeTileSet (dominoReduction S C c)

/-- Computability target for the encoded final reduction. -/
theorem dominoReductionCode_computable (S : Scaffold) (C : TableCompiler) :
    Computable (dominoReductionCode S C) := by
  unfold dominoReductionCode
  exact encodeTileSet_computable.comp (dominoReduction_computable S C)

/-- Correctness target for the encoded final reduction. -/
theorem dominoReductionCode_correct {S : Scaffold} (hS : IsScaffold S)
    (C : TableCompiler) (c : Code) :
    TilesPlane (decodeTileSet (dominoReductionCode S C c)) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [dominoReductionCode, decodeTileSet_encodeTileSet]
  exact dominoReduction_correct hS C c

/-- The domino problem is undecidable for finite Wang tilesets, assuming a scaffold
and a compiler from partial-recursive codes to table machines. -/
theorem domino_problem_undecidable_of_scaffold
    (S : Scaffold) (hS : IsScaffold S) (C : TableCompiler) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  intro h
  have hdomino : ComputablePred
      (fun c : Code => TilesPlane (dominoReduction S C c)) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun T : TileSet => TilesPlane T)
        (dominoReduction_computable S C)) h
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hdomino.of_eq fun c => dominoReduction_correct hS C c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/-- The domino problem is undecidable for encoded finite Wang tilesets, assuming a scaffold
and a compiler from partial-recursive codes to table machines. -/
theorem encoded_domino_problem_undecidable_of_scaffold
    (S : Scaffold) (hS : IsScaffold S) (C : TableCompiler) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  intro h
  have hencoded : ComputablePred
      (fun c : Code => TilesPlane (decodeTileSet (dominoReductionCode S C c))) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun n : Nat => TilesPlane (decodeTileSet n))
        (dominoReductionCode_computable S C)) h
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hencoded.of_eq fun c => dominoReductionCode_correct hS C c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/--
Encoded domino undecidability from a scaffold and the smaller fuel-search
compiler obligation.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_fuelCompiler
    (S : Scaffold) (hS : IsScaffold S) (C : FuelTableCompiler) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold S hS C.toTableCompiler

/--
Unencoded domino undecidability from a scaffold and the smaller fuel-search
compiler obligation.
-/
theorem domino_problem_undecidable_of_scaffold_fuelCompiler
    (S : Scaffold) (hS : IsScaffold S) (C : FuelTableCompiler) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold S hS C.toTableCompiler

end LeanWang
