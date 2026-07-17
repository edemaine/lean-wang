/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Computable finite Wang-tiling search

This module proves that the executable exhaustive search in `LeanWang.Basic`
decides finite rectangular and square tilability.  It also packages the square
predicate as a primitive-recursive, hence computable, predicate for use in the
co-r.e. upper bound for the plane domino problem.
-/

namespace LeanWang

/-- Flatten a rectangle in row-major order. -/
def flatListOfRectangle {w h : Nat} (x : Rectangle w h) : List WangTile :=
  List.ofFn fun k : Fin (h * w) =>
    let ji := (finProdFinEquiv).symm k
    x ji.2 ji.1

@[simp]
theorem flatListOfRectangle_length {w h : Nat} (x : Rectangle w h) :
    (flatListOfRectangle x).length = w * h := by
  simp [flatListOfRectangle, Nat.mul_comm]

theorem flatTile_flatListOfRectangle {w h : Nat} (x : Rectangle w h)
    (i : Fin w) (j : Fin h) :
    flatTile (flatListOfRectangle x) w i j = x i j := by
  unfold flatTile
  rw [List.getD_eq_getElem]
  · simp only [flatListOfRectangle, List.getElem_ofFn]
    simpa [rectIndex, finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using
      congrArg (fun ji : Fin h × Fin w => x ji.2 ji.1)
        ((finProdFinEquiv).symm_apply_apply (j, i))
  · rw [flatListOfRectangle_length]
    simpa [rectIndex, Nat.add_comm, Nat.mul_comm] using
      (finProdFinEquiv (j, i)).isLt

/-- Turn a flat row-major list into a rectangle, using `flatTile`'s default off range. -/
def rectangleOfFlatList (xs : List WangTile) (w h : Nat) : Rectangle w h :=
  fun i j => flatTile xs w i j

theorem validRectangle_of_flatValidRectangle (T : TileSet) (w h : Nat)
    (xs : List WangTile) (valid : FlatValidRectangle T w h xs) :
    ValidRectangle T (rectangleOfFlatList xs w h) := by
  exact ⟨fun i j => (valid.2 i i.isLt j j.isLt).1,
    ⟨fun i j hi => (valid.2 i i.isLt j j.isLt).2.1 hi,
      fun i j hj => (valid.2 i i.isLt j j.isLt).2.2 hj⟩⟩

theorem mem_words_iff {alphabet : List WangTile} {n : Nat} {xs : List WangTile} :
    xs ∈ words alphabet n ↔ xs.length = n ∧ ∀ tile ∈ xs, tile ∈ alphabet := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [words]
  | succ n ih => cases xs <;> simp [words, ih, and_left_comm, and_assoc, and_comm]

theorem flatListOfRectangle_mem_words {T : TileSet} {w h : Nat}
    {x : Rectangle w h} (valid : ValidRectangle T x) :
    flatListOfRectangle x ∈ words T (w * h) := by
  rw [mem_words_iff]
  refine ⟨flatListOfRectangle_length x, ?_⟩
  intro tile htile
  simp only [flatListOfRectangle, List.mem_ofFn] at htile
  rcases htile with ⟨k, rfl⟩
  exact valid.1 ((finProdFinEquiv).symm k).2 ((finProdFinEquiv).symm k).1

theorem flatListOfRectangle_flatValid {T : TileSet} {w h : Nat}
    {x : Rectangle w h} (valid : ValidRectangle T x) :
    FlatValidRectangle T w h (flatListOfRectangle x) := by
  constructor
  · exact flatListOfRectangle_length x
  · intro i hi j hj
    simp only [flatTile_flatListOfRectangle x ⟨i, hi⟩ ⟨j, hj⟩]
    refine ⟨valid.1 ⟨i, hi⟩ ⟨j, hj⟩, ?_, ?_⟩
    · intro hright
      rw [flatTile_flatListOfRectangle x ⟨i + 1, hright⟩ ⟨j, hj⟩]
      exact valid.2.1 ⟨i, hi⟩ ⟨j, hj⟩ hright
    · intro hup
      rw [flatTile_flatListOfRectangle x ⟨i, hi⟩ ⟨j + 1, hup⟩]
      exact valid.2.2 ⟨i, hi⟩ ⟨j, hj⟩ hup

theorem exists_flatValidRectangle_iff_tileableRectangle (T : TileSet) (w h : Nat) :
    (∃ xs ∈ words T (w * h), FlatValidRectangle T w h xs) ↔
      TileableRectangle T w h := by
  constructor
  · rintro ⟨xs, _hword, hvalid⟩
    exact ⟨rectangleOfFlatList xs w h,
      validRectangle_of_flatValidRectangle T w h xs hvalid⟩
  · rintro ⟨x, hvalid⟩
    exact ⟨flatListOfRectangle x, flatListOfRectangle_mem_words hvalid,
      flatListOfRectangle_flatValid hvalid⟩

private theorem wangTuple_primrec : Primrec WangTile.toTuple := by
  change Primrec WangTile.equivTuple
  exact Primrec.of_equiv

private theorem wangN_primrec : Primrec WangTile.n := by
  exact Primrec.fst.comp wangTuple_primrec

private theorem wangS_primrec : Primrec WangTile.s := by
  exact Primrec.fst.comp (Primrec.snd.comp wangTuple_primrec)

private theorem wangE_primrec : Primrec WangTile.e := by
  exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp wangTuple_primrec))

private theorem wangW_primrec : Primrec WangTile.w := by
  exact Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp wangTuple_primrec))

private theorem hMatches_primrec : PrimrecRel WangTile.HMatches := by
  exact Primrec.eq.comp (wangE_primrec.comp Primrec.fst)
    (wangW_primrec.comp Primrec.snd)

private theorem vMatches_primrec : PrimrecRel WangTile.VMatches := by
  exact Primrec.eq.comp (wangN_primrec.comp Primrec.fst)
    (wangS_primrec.comp Primrec.snd)

private theorem tileMem_primrec :
    PrimrecRel fun (T : TileSet) (tile : WangTile) => tile ∈ T := by
  exact (PrimrecRel.exists_mem_list (@Primrec.eq WangTile _)).of_eq (by simp)

private abbrev RectangleParams := TileSet × (Nat × Nat)
private abbrev FlatInput := RectangleParams × List WangTile
private abbrev CellInput := FlatInput × (Nat × Nat)

private def paramsTiles (p : RectangleParams) : TileSet := p.1
private def paramsWidth (p : RectangleParams) : Nat := p.2.1
private def paramsHeight (p : RectangleParams) : Nat := p.2.2
private def inputParams (a : FlatInput) : RectangleParams := a.1
private def inputList (a : FlatInput) : List WangTile := a.2
private def cellInput (a : CellInput) : FlatInput := a.1
private def cellI (a : CellInput) : Nat := a.2.1
private def cellJ (a : CellInput) : Nat := a.2.2

private theorem paramsTiles_primrec : Primrec paramsTiles := Primrec.fst
private theorem paramsWidth_primrec : Primrec paramsWidth :=
  Primrec.fst.comp Primrec.snd
private theorem paramsHeight_primrec : Primrec paramsHeight :=
  Primrec.snd.comp Primrec.snd
private theorem inputParams_primrec : Primrec inputParams := Primrec.fst
private theorem inputList_primrec : Primrec inputList := Primrec.snd
private theorem cellInput_primrec : Primrec cellInput := Primrec.fst
private theorem cellI_primrec : Primrec cellI := Primrec.fst.comp Primrec.snd
private theorem cellJ_primrec : Primrec cellJ := Primrec.snd.comp Primrec.snd

private def cellWidth (a : CellInput) : Nat := paramsWidth (inputParams (cellInput a))
private def cellList (a : CellInput) : List WangTile := inputList (cellInput a)
private def cellIndex (a : CellInput) : Nat :=
  rectIndex (cellWidth a) (cellI a) (cellJ a)

private theorem cellWidth_primrec : Primrec cellWidth :=
  paramsWidth_primrec.comp (inputParams_primrec.comp cellInput_primrec)

private theorem cellList_primrec : Primrec cellList :=
  inputList_primrec.comp cellInput_primrec

private theorem cellIndex_primrec : Primrec cellIndex := by
  unfold cellIndex rectIndex
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp cellJ_primrec cellWidth_primrec)
    cellI_primrec

private def cellTile (a : CellInput) : WangTile :=
  flatTile (cellList a) (cellWidth a) (cellI a) (cellJ a)

private theorem cellTile_primrec : Primrec cellTile := by
  unfold cellTile flatTile
  exact (Primrec.list_getD monochromeTile).comp cellList_primrec cellIndex_primrec

private def rightCellInput (a : CellInput) : CellInput :=
  (cellInput a, (cellI a + 1, cellJ a))

private def upperCellInput (a : CellInput) : CellInput :=
  (cellInput a, (cellI a, cellJ a + 1))

private theorem rightCellInput_primrec : Primrec rightCellInput := by
  exact Primrec.pair cellInput_primrec
    (Primrec.pair (Primrec.succ.comp cellI_primrec) cellJ_primrec)

private theorem upperCellInput_primrec : Primrec upperCellInput := by
  exact Primrec.pair cellInput_primrec
    (Primrec.pair cellI_primrec (Primrec.succ.comp cellJ_primrec))

private def CellValid (a : CellInput) : Prop :=
  cellTile a ∈ paramsTiles (inputParams (cellInput a)) ∧
    (cellI a + 1 < cellWidth a →
      WangTile.HMatches (cellTile a) (cellTile (rightCellInput a))) ∧
    (cellJ a + 1 < paramsHeight (inputParams (cellInput a)) →
      WangTile.VMatches (cellTile a) (cellTile (upperCellInput a)))

private instance (a : CellInput) : Decidable (CellValid a) := by
  unfold CellValid
  infer_instance

private theorem cellValid_primrec : PrimrecPred CellValid := by
  let hmem : PrimrecPred fun a : CellInput =>
      cellTile a ∈ paramsTiles (inputParams (cellInput a)) :=
    tileMem_primrec.comp
      (paramsTiles_primrec.comp (inputParams_primrec.comp cellInput_primrec))
      cellTile_primrec
  let hrightBound : PrimrecPred fun a : CellInput => cellI a + 1 < cellWidth a :=
    Primrec.nat_lt.comp (Primrec.succ.comp cellI_primrec) cellWidth_primrec
  let hrightMatch : PrimrecPred fun a : CellInput =>
      WangTile.HMatches (cellTile a) (cellTile (rightCellInput a)) :=
    hMatches_primrec.comp cellTile_primrec
      (cellTile_primrec.comp rightCellInput_primrec)
  let huppBound : PrimrecPred fun a : CellInput =>
      cellJ a + 1 < paramsHeight (inputParams (cellInput a)) :=
    Primrec.nat_lt.comp (Primrec.succ.comp cellJ_primrec)
      (paramsHeight_primrec.comp (inputParams_primrec.comp cellInput_primrec))
  let huppMatch : PrimrecPred fun a : CellInput =>
      WangTile.VMatches (cellTile a) (cellTile (upperCellInput a)) :=
    vMatches_primrec.comp cellTile_primrec
      (cellTile_primrec.comp upperCellInput_primrec)
  exact hmem.and ((hrightBound.not.or hrightMatch).and
    (huppBound.not.or huppMatch)) |>.of_eq (by
      intro a
      simp only [CellValid, ← imp_iff_not_or])

private def flatInputCell (a : FlatInput) (i j : Nat) : CellInput :=
  (a, (i, j))

private theorem flatInputCell_primrec :
    Primrec fun p : Nat × (FlatInput × Nat) =>
      flatInputCell p.2.1 p.2.2 p.1 := by
  exact Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst)

private theorem primrecRel_forall_lt {beta : Type*} [Primcodable beta]
    {R : Nat → beta → Prop} (hR : PrimrecRel R) :
    PrimrecRel fun n b => ∀ x < n, R x b := by
  classical
  exact (hR.forall_mem_list.comp₂
    (Primrec.list_range.comp₂ Primrec₂.left) Primrec₂.right).of_eq (by simp)

private theorem allCells_primrec : PrimrecPred fun a : FlatInput =>
    ∀ i < paramsWidth (inputParams a),
      ∀ j < paramsHeight (inputParams a), CellValid (flatInputCell a i j) := by
  let hcell : PrimrecRel fun j (ai : FlatInput × Nat) =>
      CellValid (flatInputCell ai.1 ai.2 j) :=
    cellValid_primrec.comp flatInputCell_primrec
  let hallJ : PrimrecRel fun n (ai : FlatInput × Nat) =>
      ∀ j < n, CellValid (flatInputCell ai.1 ai.2 j) :=
    primrecRel_forall_lt hcell
  let hrow : PrimrecRel fun i (a : FlatInput) =>
      ∀ j < paramsHeight (inputParams a), CellValid (flatInputCell a i j) :=
    hallJ.comp₂
      (paramsHeight_primrec.comp₂ (inputParams_primrec.comp₂ Primrec₂.right))
      ((Primrec₂.pair).comp₂ Primrec₂.right Primrec₂.left)
  let hallI : PrimrecRel fun n (a : FlatInput) =>
      ∀ i < n, ∀ j < paramsHeight (inputParams a),
        CellValid (flatInputCell a i j) :=
    primrecRel_forall_lt hrow
  exact hallI.comp
    (paramsWidth_primrec.comp inputParams_primrec) Primrec.id

private def flatValidInput (a : FlatInput) : Prop :=
  FlatValidRectangle (paramsTiles (inputParams a))
    (paramsWidth (inputParams a)) (paramsHeight (inputParams a)) (inputList a)

private instance (a : FlatInput) : Decidable (flatValidInput a) := by
  unfold flatValidInput
  infer_instance

private theorem flatValidInput_primrec : PrimrecPred flatValidInput := by
  let hlength : PrimrecPred fun a : FlatInput =>
      (inputList a).length =
        paramsWidth (inputParams a) * paramsHeight (inputParams a) :=
    Primrec.eq.comp
      (Primrec.list_length.comp inputList_primrec)
      (Primrec.nat_mul.comp
        (paramsWidth_primrec.comp inputParams_primrec)
        (paramsHeight_primrec.comp inputParams_primrec))
  exact hlength.and allCells_primrec |>.of_eq (by
    intro a
    simp only [flatValidInput, FlatValidRectangle, CellValid, flatInputCell,
      cellTile, cellList, cellWidth, cellInput, cellI, cellJ, inputParams,
      inputList, paramsTiles, paramsWidth, paramsHeight]
    rfl)

private theorem words_primrec :
    Primrec₂ (words : List WangTile → Nat → List (List WangTile)) := by
  let step : List WangTile → Nat × List (List WangTile) → List (List WangTile) :=
    fun alphabet state => state.2.flatMap fun tail =>
      alphabet.map fun head => head :: tail
  have hmap : Primrec₂ fun
      (q : List WangTile × (Nat × List (List WangTile)))
      (tail : List WangTile) => q.1.map fun head => head :: tail := by
    exact Primrec.list_map (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
  have hstep : Primrec₂ step := by
    exact Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) hmap
  exact (Primrec.nat_rec (Primrec.const ([[]] : List (List WangTile))) hstep).of_eq
    (by intro alphabet n; induction n <;> simp [words, step, *])

private def rectangleParamsWords (p : RectangleParams) : List (List WangTile) :=
  words (paramsTiles p) (paramsWidth p * paramsHeight p)

private theorem rectangleParamsWords_primrec : Primrec rectangleParamsWords := by
  exact words_primrec.comp paramsTiles_primrec
    (Primrec.nat_mul.comp paramsWidth_primrec paramsHeight_primrec)

private theorem flatValidRelation_primrec : PrimrecRel fun
    (xs : List WangTile) (p : RectangleParams) =>
      FlatValidRectangle (paramsTiles p) (paramsWidth p) (paramsHeight p) xs := by
  exact flatValidInput_primrec.comp (Primrec.pair Primrec.snd Primrec.fst)

private theorem tileableRectangle_primrec : PrimrecPred fun p : RectangleParams =>
    TileableRectangle (paramsTiles p) (paramsWidth p) (paramsHeight p) := by
  let hsearch : PrimrecPred fun p : RectangleParams =>
      ∃ xs ∈ rectangleParamsWords p,
        FlatValidRectangle (paramsTiles p) (paramsWidth p) (paramsHeight p) xs :=
    flatValidRelation_primrec.exists_mem_list.comp
      rectangleParamsWords_primrec Primrec.id
  exact hsearch.of_eq fun p =>
    exists_flatValidRectangle_iff_tileableRectangle
      (paramsTiles p) (paramsWidth p) (paramsHeight p)

theorem tileableSquare_primrec : PrimrecPred fun p : TileSet × Nat =>
    TileableSquare p.1 p.2 := by
  exact tileableRectangle_primrec.comp
    (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd Primrec.snd))

theorem tileableSquare_computablePred : ComputablePred fun p : TileSet × Nat =>
    TileableSquare p.1 p.2 :=
  tileableSquare_primrec.computablePred

@[simp]
theorem validRectListBool_eq_true (T : TileSet) (w h : Nat) (xs : List WangTile) :
    validRectListBool T w h xs = true ↔ FlatValidRectangle T w h xs := by
  simp [validRectListBool]

theorem tileableRectangleBool_eq_true (T : TileSet) (w h : Nat) :
    tileableRectangleBool T w h = true ↔ TileableRectangle T w h := by
  rw [tileableRectangleBool, List.any_eq_true]
  simpa only [validRectListBool_eq_true] using
    exists_flatValidRectangle_iff_tileableRectangle T w h

theorem tileableSquareBool_eq_true (T : TileSet) (n : Nat) :
    tileableSquareBool T n = true ↔ TileableSquare T n := by
  exact tileableRectangleBool_eq_true T n n

theorem tileableSquareBool_computable :
    Computable fun p : TileSet × Nat => tileableSquareBool p.1 p.2 := by
  rcases tileableSquare_primrec with ⟨decision, hprim⟩
  letI := decision
  exact hprim.to_comp.of_eq fun p => by
    apply Bool.eq_iff_iff.2
    simpa using (tileableSquareBool_eq_true p.1 p.2).symm

end LeanWang
