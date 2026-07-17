/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Affine
import LeanWang.Kari.SignedPrimrec
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite transducers for integer-coded rational affine maps

This file makes the finite-enumeration step in Kari's construction explicit.
An affine branch on three coordinates is stored by integer numerators and a
positive common denominator.  Given finite input and output digit alphabets and
a carry bound, `IntegerAffineBranch.transducer` enumerates exactly the local
carry equations

`cₗ + A a + b = d a' + cᵣ`.

Digit colors canonically encode integer triples.  Horizontal colors additionally
carry the branch tag, so carry states belonging to distinct branches cannot
match.  The final theorem lifts the scaled integer equation to the generic
rational-affine semantics of `Affine.lean`.
-/

namespace LeanWang
namespace Kari

/-- The fixed three-dimensional integer vectors used by Kari's affine coding. -/
structure IntVector3 where
  x : Int
  y : Int
  z : Int
deriving DecidableEq, Repr

namespace IntVector3

/-- Integer triples use the standard primitive-recursive product encoding. -/
def equivTuple : IntVector3 ≃ Int × Int × Int where
  toFun v := (v.x, v.y, v.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := by
    intro v
    cases v
    rfl
  right_inv := by
    rintro ⟨x, y, z⟩
    rfl

instance instPrimcodableIntVector3 : Primcodable IntVector3 :=
  Primcodable.ofEquiv (Int × Int × Int) equivTuple

/-- The zero integer vector. -/
protected def zero : IntVector3 :=
  ⟨0, 0, 0⟩

/-- Pointwise addition. -/
protected def add (u v : IntVector3) : IntVector3 :=
  ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

/-- Integer scalar multiplication. -/
protected def smul (n : Int) (v : IntVector3) : IntVector3 :=
  ⟨n * v.x, n * v.y, n * v.z⟩

/-- Interpret an integer triple as a rational vector. -/
def toRat (v : IntVector3) : Fin 3 → ℚ
  | ⟨0, _⟩ => v.x
  | ⟨1, _⟩ => v.y
  | ⟨2, _⟩ => v.z

@[simp] theorem toRat_zero : IntVector3.zero.toRat = 0 := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem toRat_add (u v : IntVector3) :
    (u.add v).toRat = u.toRat + v.toRat := by
  funext i
  fin_cases i <;> simp [IntVector3.add, toRat]

@[simp] theorem toRat_smul (n : Int) (v : IntVector3) :
    (IntVector3.smul n v).toRat = (n : ℚ) • v.toRat := by
  funext i
  fin_cases i <;> simp [IntVector3.smul, toRat]

/-- Signed integers are encoded by alternating nonnegative and negative values. -/
def intCode : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

theorem intCode_eq_encode (n : Int) :
    intCode n = Encodable.encode n := by
  cases n <;> rfl

theorem intCode_primrec : Primrec intCode := by
  exact (Primrec.encode : Primrec (Encodable.encode : Int → Nat)).of_eq fun n =>
    (intCode_eq_encode n).symm

/-- Inverse of `intCode`. -/
def intDecode (n : Nat) : Int :=
  if Even n then Int.ofNat (n / 2) else Int.negSucc (n / 2)

@[simp] theorem intDecode_intCode (n : Int) : intDecode (intCode n) = n := by
  cases n with
  | ofNat n =>
      simp [intCode, intDecode]
  | negSucc n =>
      simp [intCode, intDecode]
      omega

/-- Canonical natural-number color of an integer vector. -/
def code (v : IntVector3) : Nat :=
  Nat.pair (intCode v.x) (Nat.pair (intCode v.y) (intCode v.z))

theorem equivTuple_primrec : Primrec equivTuple := by
  simpa [equivTuple] using
    (Primrec.of_equiv (e := equivTuple) : Primrec equivTuple)

theorem x_primrec : Primrec IntVector3.x :=
  Primrec.fst.comp equivTuple_primrec

theorem y_primrec : Primrec IntVector3.y :=
  Primrec.fst.comp (Primrec.snd.comp equivTuple_primrec)

theorem z_primrec : Primrec IntVector3.z :=
  Primrec.snd.comp (Primrec.snd.comp equivTuple_primrec)

theorem code_primrec : Primrec code :=
  Primrec₂.natPair.comp (intCode_primrec.comp x_primrec)
    (Primrec₂.natPair.comp (intCode_primrec.comp y_primrec)
      (intCode_primrec.comp z_primrec))

/-- Construct an integer vector from its primitive-recursive tuple code. -/
theorem ofTuple_primrec : Primrec equivTuple.symm := by
  simpa using
    (Primrec.of_equiv_symm (e := equivTuple) : Primrec equivTuple.symm)

/-- Pointwise addition of integer vectors is primitive recursive. -/
theorem add_primrec : Primrec₂ IntVector3.add := by
  apply Primrec.of_equiv_iff equivTuple |>.mp
  exact Primrec.pair
    (SignedPrimrec.intAdd.comp (x_primrec.comp Primrec.fst)
      (x_primrec.comp Primrec.snd))
    (Primrec.pair
      (SignedPrimrec.intAdd.comp (y_primrec.comp Primrec.fst)
        (y_primrec.comp Primrec.snd))
      (SignedPrimrec.intAdd.comp (z_primrec.comp Primrec.fst)
        (z_primrec.comp Primrec.snd)))

/-- Integer scalar multiplication of a vector is primitive recursive. -/
theorem smul_primrec : Primrec₂ IntVector3.smul := by
  apply Primrec.of_equiv_iff equivTuple |>.mp
  exact Primrec.pair
    (SignedPrimrec.intMul.comp Primrec.fst (x_primrec.comp Primrec.snd))
    (Primrec.pair
      (SignedPrimrec.intMul.comp Primrec.fst (y_primrec.comp Primrec.snd))
      (SignedPrimrec.intMul.comp Primrec.fst (z_primrec.comp Primrec.snd)))

/-- Decode a vector color. -/
def decode (n : Nat) : IntVector3 :=
  ⟨intDecode n.unpair.1,
    intDecode n.unpair.2.unpair.1,
    intDecode n.unpair.2.unpair.2⟩

@[simp] theorem decode_code (v : IntVector3) : decode (code v) = v := by
  cases v
  simp [decode, code]

theorem code_injective : Function.Injective code := by
  intro u v h
  simpa only [decode_code] using congrArg decode h

/-- All integers in the closed interval `[-bound, bound]`. -/
def boundedIntegers (bound : Nat) : List Int :=
  ((List.range (bound + 1)).map Int.ofNat) ++
    ((List.range bound).map Int.negSucc)

/-- The finite signed interval enumeration is primitive recursive. -/
theorem boundedIntegers_primrec : Primrec boundedIntegers := by
  unfold boundedIntegers
  exact Primrec.list_append.comp
    (Primrec.list_map (Primrec.list_range.comp Primrec.succ)
      (SignedPrimrec.intOfNat.comp Primrec.snd).to₂)
    (Primrec.list_map Primrec.list_range
      (SignedPrimrec.intNegSucc.comp Primrec.snd).to₂)

@[simp] theorem mem_boundedIntegers (z : Int) (bound : Nat) :
    z ∈ boundedIntegers bound ↔ -(bound : Int) ≤ z ∧ z ≤ bound := by
  cases z with
  | ofNat n =>
      simp [boundedIntegers]
      omega
  | negSucc n =>
      simp [boundedIntegers]
      omega

/-- All triples whose coordinates lie in the closed interval `[-bound, bound]`. -/
def bounded (bound : Nat) : List IntVector3 :=
  let coordinates := boundedIntegers bound
  coordinates.flatMap fun x =>
    coordinates.flatMap fun y =>
      coordinates.map fun z => ⟨x, y, z⟩

/-- The finite box of bounded integer vectors is primitive recursive. -/
theorem bounded_primrec : Primrec bounded := by
  let mkVector : Int → Int → Int → IntVector3 := fun x y z => ⟨x, y, z⟩
  have hmk : Primrec fun p : Int × Int × Int => mkVector p.1 p.2.1 p.2.2 := by
    exact ofTuple_primrec
  unfold bounded
  apply Primrec.list_flatMap boundedIntegers_primrec
  apply Primrec₂.mk
  apply Primrec.list_flatMap
    (boundedIntegers_primrec.comp Primrec.fst)
  apply Primrec₂.mk
  apply Primrec.list_map
    (boundedIntegers_primrec.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec₂.mk (hmk.comp
    ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))

theorem mem_bounded (v : IntVector3) (bound : Nat) :
    v ∈ bounded bound ↔
      -(bound : Int) ≤ v.x ∧ v.x ≤ bound ∧
      -(bound : Int) ≤ v.y ∧ v.y ≤ bound ∧
      -(bound : Int) ≤ v.z ∧ v.z ≤ bound := by
  rcases v with ⟨x, y, z⟩
  simp [bounded, and_assoc]

end IntVector3

/-- A `3 × 3` integer matrix, written out to keep the construction directly
executable and its finite encoding independent of matrix-library internals. -/
structure IntMatrix3 where
  xx : Int
  xy : Int
  xz : Int
  yx : Int
  yy : Int
  yz : Int
  zx : Int
  zy : Int
  zz : Int
deriving DecidableEq, Repr

namespace IntMatrix3

/-- Matrices are equivalent to their nine entries. -/
def equivTuple : IntMatrix3 ≃
    Int × Int × Int × Int × Int × Int × Int × Int × Int where
  toFun A := (A.xx, A.xy, A.xz, A.yx, A.yy, A.yz, A.zx, A.zy, A.zz)
  invFun p :=
    ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1,
      p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2⟩
  left_inv := by
    intro A
    cases A
    rfl
  right_inv := by
    rintro ⟨xx, xy, xz, yx, yy, yz, zx, zy, zz⟩
    rfl

/-- A shallower product encoding by matrix rows, used to keep primitive-
recursion proof terms manageable. -/
def equivRows : IntMatrix3 ≃ IntVector3 × IntVector3 × IntVector3 where
  toFun A :=
    (⟨A.xx, A.xy, A.xz⟩, ⟨A.yx, A.yy, A.yz⟩, ⟨A.zx, A.zy, A.zz⟩)
  invFun p :=
    ⟨p.1.x, p.1.y, p.1.z, p.2.1.x, p.2.1.y, p.2.1.z,
      p.2.2.x, p.2.2.y, p.2.2.z⟩
  left_inv := by
    intro A
    cases A
    rfl
  right_inv := by
    rintro ⟨⟨xx, xy, xz⟩, ⟨yx, yy, yz⟩, ⟨zx, zy, zz⟩⟩
    rfl

instance instPrimcodableIntMatrix3 : Primcodable IntMatrix3 :=
  Primcodable.ofEquiv (IntVector3 × IntVector3 × IntVector3) equivRows

/-- Extract the row-vector code of an integer matrix. -/
theorem equivRows_primrec : Primrec equivRows := by
  simpa [equivRows] using
    (Primrec.of_equiv (e := equivRows) : Primrec equivRows)

/-- Matrix-vector multiplication. -/
def mulVec (A : IntMatrix3) (v : IntVector3) : IntVector3 :=
  ⟨A.xx * v.x + A.xy * v.y + A.xz * v.z,
    A.yx * v.x + A.yy * v.y + A.yz * v.z,
    A.zx * v.x + A.zy * v.y + A.zz * v.z⟩

set_option maxHeartbeats 1000000 in
-- The nested `Primrec` closure proof requires substantial instance normalization.
/-- Integer matrix-vector multiplication is primitive recursive. -/
theorem mulVec_primrec : Primrec₂ mulVec := by
  have hrowX : Primrec fun A : IntMatrix3 => (⟨A.xx, A.xy, A.xz⟩ : IntVector3) :=
    Primrec.fst.comp equivRows_primrec
  have hrowY : Primrec fun A : IntMatrix3 => (⟨A.yx, A.yy, A.yz⟩ : IntVector3) :=
    Primrec.fst.comp (Primrec.snd.comp equivRows_primrec)
  have hrowZ : Primrec fun A : IntMatrix3 => (⟨A.zx, A.zy, A.zz⟩ : IntVector3) :=
    Primrec.snd.comp (Primrec.snd.comp equivRows_primrec)
  have hxx : Primrec IntMatrix3.xx := IntVector3.x_primrec.comp hrowX
  have hxy : Primrec IntMatrix3.xy := IntVector3.y_primrec.comp hrowX
  have hxz : Primrec IntMatrix3.xz := IntVector3.z_primrec.comp hrowX
  have hyx : Primrec IntMatrix3.yx := IntVector3.x_primrec.comp hrowY
  have hyy : Primrec IntMatrix3.yy := IntVector3.y_primrec.comp hrowY
  have hyz : Primrec IntMatrix3.yz := IntVector3.z_primrec.comp hrowY
  have hzx : Primrec IntMatrix3.zx := IntVector3.x_primrec.comp hrowZ
  have hzy : Primrec IntMatrix3.zy := IntVector3.y_primrec.comp hrowZ
  have hzz : Primrec IntMatrix3.zz := IntVector3.z_primrec.comp hrowZ
  have hxx' : Primrec fun p : IntMatrix3 × IntVector3 => p.1.xx :=
    hxx.comp Primrec.fst
  have hxy' : Primrec fun p : IntMatrix3 × IntVector3 => p.1.xy :=
    hxy.comp Primrec.fst
  have hxz' : Primrec fun p : IntMatrix3 × IntVector3 => p.1.xz :=
    hxz.comp Primrec.fst
  have hyx' : Primrec fun p : IntMatrix3 × IntVector3 => p.1.yx :=
    hyx.comp Primrec.fst
  have hyy' : Primrec fun p : IntMatrix3 × IntVector3 => p.1.yy :=
    hyy.comp Primrec.fst
  have hyz' : Primrec fun p : IntMatrix3 × IntVector3 => p.1.yz :=
    hyz.comp Primrec.fst
  have hzx' : Primrec fun p : IntMatrix3 × IntVector3 => p.1.zx :=
    hzx.comp Primrec.fst
  have hzy' : Primrec fun p : IntMatrix3 × IntVector3 => p.1.zy :=
    hzy.comp Primrec.fst
  have hzz' : Primrec fun p : IntMatrix3 × IntVector3 => p.1.zz :=
    hzz.comp Primrec.fst
  have hvx : Primrec fun p : IntMatrix3 × IntVector3 => p.2.x :=
    IntVector3.x_primrec.comp Primrec.snd
  have hvy : Primrec fun p : IntMatrix3 × IntVector3 => p.2.y :=
    IntVector3.y_primrec.comp Primrec.snd
  have hvz : Primrec fun p : IntMatrix3 × IntVector3 => p.2.z :=
    IntVector3.z_primrec.comp Primrec.snd
  have hx := SignedPrimrec.intAdd.comp
    (SignedPrimrec.intAdd.comp
      (SignedPrimrec.intMul.comp hxx' hvx)
      (SignedPrimrec.intMul.comp hxy' hvy))
    (SignedPrimrec.intMul.comp hxz' hvz)
  have hy := SignedPrimrec.intAdd.comp
    (SignedPrimrec.intAdd.comp
      (SignedPrimrec.intMul.comp hyx' hvx)
      (SignedPrimrec.intMul.comp hyy' hvy))
    (SignedPrimrec.intMul.comp hyz' hvz)
  have hz := SignedPrimrec.intAdd.comp
    (SignedPrimrec.intAdd.comp
      (SignedPrimrec.intMul.comp hzx' hvx)
      (SignedPrimrec.intMul.comp hzy' hvy))
    (SignedPrimrec.intMul.comp hzz' hvz)
  exact (IntVector3.ofTuple_primrec.comp (hx.pair (hy.pair hz))).of_eq
    fun p => by cases p.1; cases p.2; rfl

/-- The rational linear map obtained by dividing all matrix entries by `d`. -/
def toLinearMap (A : IntMatrix3) (d : Nat) : Module.End ℚ (Fin 3 → ℚ) where
  toFun v := fun
    | ⟨0, _⟩ =>
        (A.xx * v 0 + A.xy * v 1 + A.xz * v 2) / d
    | ⟨1, _⟩ =>
        (A.yx * v 0 + A.yy * v 1 + A.yz * v 2) / d
    | ⟨2, _⟩ =>
        (A.zx * v 0 + A.zy * v 1 + A.zz * v 2) / d
  map_add' := by
    intro u v
    funext i
    fin_cases i <;> simp only [Pi.add_apply] <;> ring
  map_smul' := by
    intro q v
    funext i
    fin_cases i <;>
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

end IntMatrix3

/-- One rational affine branch, with a positive common denominator and a tag
reserved for its horizontal carry colors. -/
structure IntegerAffineBranch where
  tag : Nat
  denominator : Nat
  denominator_pos : 0 < denominator
  linearNumerator : IntMatrix3
  offsetNumerator : IntVector3
deriving Repr

namespace IntegerAffineBranch

/-- A branch is effectively encoded by its tag, positive denominator, matrix,
and offset.  Packing the positivity proof into `PNat` keeps it proof-irrelevant. -/
def equivTuple : IntegerAffineBranch ≃ Nat × PNat × IntMatrix3 × IntVector3 where
  toFun branch :=
    (branch.tag, ⟨branch.denominator, branch.denominator_pos⟩,
      branch.linearNumerator, branch.offsetNumerator)
  invFun p :=
    { tag := p.1
      denominator := p.2.1.val
      denominator_pos := p.2.1.property
      linearNumerator := p.2.2.1
      offsetNumerator := p.2.2.2 }
  left_inv := by
    intro branch
    cases branch
    rfl
  right_inv := by
    rintro ⟨tag, denominator, linear, offset⟩
    rcases denominator with ⟨denominator, positive⟩
    rfl

instance instPrimcodableIntegerAffineBranch : Primcodable IntegerAffineBranch :=
  Primcodable.ofEquiv (Nat × PNat × IntMatrix3 × IntVector3) equivTuple

/-- Raw branch data used by the effective construction.  Keeping the program
on this product type avoids asking the primitive-recursion framework to unfold
the proof-bearing `IntegerAffineBranch` encoding. -/
abbrev BranchData := Nat × PNat × IntMatrix3 × IntVector3

/-- Interpret raw branch data as the mathematical branch structure. -/
def ofData (data : BranchData) : IntegerAffineBranch :=
  equivTuple.symm data

/-- The rational affine map represented by an integer-coded branch. -/
def rationalMap (branch : IntegerAffineBranch) :
    RationalAffineMap (Fin 3 → ℚ) where
  linear := branch.linearNumerator.toLinearMap branch.denominator
  offset := fun i => branch.offsetNumerator.toRat i / branch.denominator

/-- The scaled local carry equation used to decide whether to emit a transition. -/
def LocalEquation (branch : IntegerAffineBranch)
    (input output left right : IntVector3) : Prop :=
  left.add ((branch.linearNumerator.mulVec input).add branch.offsetNumerator) =
    (IntVector3.smul (branch.denominator : Int) output).add
      right

instance (branch : IntegerAffineBranch) (input output left right : IntVector3) :
    Decidable (branch.LocalEquation input output left right) := by
  unfold LocalEquation
  infer_instance

/-- Branch-tagged horizontal color of a carry vector. -/
def carryColor (branch : IntegerAffineBranch) (carry : IntVector3) : Nat :=
  Nat.pair branch.tag carry.code

/-- Decode the integer vector stored in a horizontal color.  Its tag is ignored
by the numerical interpretation and is used only to prevent horizontal matches. -/
def carryValue (branch : IntegerAffineBranch) (color : Nat) : Fin 3 → ℚ :=
  fun i => (IntVector3.decode color.unpair.2).toRat i / branch.denominator

/-- Decode the integer vector stored in a vertical digit color. -/
def digitValue (color : Nat) : Fin 3 → ℚ :=
  (IntVector3.decode color).toRat

@[simp] theorem carryValue_carryColor (branch : IntegerAffineBranch)
    (carry : IntVector3) :
    branch.carryValue (branch.carryColor carry) =
      fun i => carry.toRat i / branch.denominator := by
  funext i
  simp [carryValue, carryColor]

@[simp] theorem digitValue_code (digit : IntVector3) :
    digitValue digit.code = digit.toRat := by
  simp [digitValue]

/-- Distinct branches have disjoint horizontal color sets. -/
theorem carryColor_eq_iff (branch branch' : IntegerAffineBranch)
    (carry carry' : IntVector3) :
    branch.carryColor carry = branch'.carryColor carry' ↔
      branch.tag = branch'.tag ∧ carry = carry' := by
  simp [carryColor, Nat.pair_eq_pair, IntVector3.code_injective.eq_iff]

/-- The transition associated with one solution of the local carry equation. -/
def transition (branch : IntegerAffineBranch)
    (input output left right : IntVector3) : Transition where
  input := input.code
  output := output.code
  left := branch.carryColor left
  right := branch.carryColor right

/-- Ordered Cartesian product of two finite lists. -/
def listProduct {α β : Type*} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x => ys.map fun y => (x, y)

/-- Cartesian product of primitive-codable lists is primitive recursive. -/
theorem listProduct_primrec {α β : Type*} [Primcodable α] [Primcodable β] :
    Primrec₂ (@listProduct α β) := by
  apply Primrec₂.mk
  apply Primrec.list_flatMap Primrec.fst
  apply Primrec₂.mk
  apply Primrec.list_map (Primrec.snd.comp Primrec.fst)
  exact Primrec₂.mk (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)

@[simp] theorem mem_listProduct {α β : Type*} {xs : List α} {ys : List β}
    {x : α} {y : β} :
    (x, y) ∈ listProduct xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  simp [listProduct]

/-- Candidate quadruples before checking the local affine equation.  The
staged products keep the executable construction and its effectiveness proof
shallow while preserving the usual lexicographic enumeration order. -/
def candidates (inputs outputs carries : List IntVector3) :
    List (IntVector3 × IntVector3 × IntVector3 × IntVector3) :=
  (listProduct (listProduct (listProduct inputs outputs) carries) carries).map
    fun p => (p.1.1.1, p.1.1.2, p.1.2, p.2)

/-- Candidate-quadruple enumeration is primitive recursive. -/
theorem candidates_primrec : Primrec fun p :
    List IntVector3 × List IntVector3 × List IntVector3 =>
    candidates p.1 p.2.1 p.2.2 := by
  unfold candidates
  have hpairs : Primrec fun p :
      List IntVector3 × List IntVector3 × List IntVector3 =>
      listProduct p.1 p.2.1 :=
    listProduct_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have htriples : Primrec fun p :
      List IntVector3 × List IntVector3 × List IntVector3 =>
      listProduct (listProduct p.1 p.2.1) p.2.2 :=
    listProduct_primrec.comp hpairs (Primrec.snd.comp Primrec.snd)
  have hquadruples : Primrec fun p :
      List IntVector3 × List IntVector3 × List IntVector3 =>
      listProduct (listProduct (listProduct p.1 p.2.1) p.2.2) p.2.2 :=
    listProduct_primrec.comp htriples (Primrec.snd.comp Primrec.snd)
  apply Primrec.list_map hquadruples
  exact Primrec₂.mk (Primrec.pair
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))))

/-- Enumerate the finite transducer for a branch and a carry bound. -/
def transducer (branch : IntegerAffineBranch)
    (inputs outputs : List IntVector3) (carryBound : Nat) : Transducer :=
  ((candidates inputs outputs (IntVector3.bounded carryBound)).filter fun candidate =>
      branch.LocalEquation candidate.1 candidate.2.1 candidate.2.2.1 candidate.2.2.2).map
    fun candidate => branch.transition
      candidate.1 candidate.2.1 candidate.2.2.1 candidate.2.2.2

/-- The local carry equation, evaluated directly on raw branch data. -/
def LocalEquationData (data : BranchData)
    (input output left right : IntVector3) : Prop :=
  left.add ((data.2.2.1.mulVec input).add data.2.2.2) =
    (IntVector3.smul (data.2.1.val : Int) output).add right

instance (data : BranchData) (input output left right : IntVector3) :
    Decidable (LocalEquationData data input output left right) := by
  unfold LocalEquationData
  infer_instance

/-- Carry colors, evaluated directly on raw branch data. -/
def carryColorData (data : BranchData) (carry : IntVector3) : Nat :=
  Nat.pair data.1 carry.code

/-- Transitions, evaluated directly on raw branch data. -/
def transitionData (data : BranchData)
    (input output left right : IntVector3) : Transition where
  input := input.code
  output := output.code
  left := carryColorData data left
  right := carryColorData data right

theorem localEquationData_iff (data : BranchData)
    (input output left right : IntVector3) :
    LocalEquationData data input output left right ↔
      (ofData data).LocalEquation input output left right := by
  rfl

theorem transitionData_eq (data : BranchData)
    (input output left right : IntVector3) :
    transitionData data input output left right =
      (ofData data).transition input output left right := by
  rfl

/-- Test and emit one raw-data transition candidate. -/
def emitTransitionData (data : BranchData)
    (candidate : IntVector3 × IntVector3 × IntVector3 × IntVector3) :
    Option Transition :=
  if LocalEquationData data candidate.1 candidate.2.1 candidate.2.2.1 candidate.2.2.2
  then some (transitionData data
    candidate.1 candidate.2.1 candidate.2.2.1 candidate.2.2.2)
  else none

/-- The finite transducer program evaluated directly on raw branch data. -/
def transducerData (data : BranchData)
    (inputs outputs : List IntVector3) (carryBound : Nat) : Transducer :=
  (candidates inputs outputs (IntVector3.bounded carryBound)).filterMap
    (emitTransitionData data)

/-- Raw execution agrees definitionally with the mathematical branch view. -/
theorem transducerData_eq_transducer (data : BranchData)
    (inputs outputs : List IntVector3) (carryBound : Nat) :
    transducerData data inputs outputs carryBound =
      (ofData data).transducer inputs outputs carryBound := by
  unfold transducerData transducer emitTransitionData
  induction candidates inputs outputs (IntVector3.bounded carryBound) with
  | nil => rfl
  | cons candidate candidates ih =>
    by_cases h : LocalEquationData data candidate.1 candidate.2.1
      candidate.2.2.1 candidate.2.2.2
    · have hm : (ofData data).LocalEquation candidate.1 candidate.2.1
          candidate.2.2.1 candidate.2.2.2 :=
        (localEquationData_iff data _ _ _ _).mp h
      simp only [transitionData_eq] at ih
      simp [h, hm, ih, transitionData_eq]
    · have hm : ¬(ofData data).LocalEquation candidate.1 candidate.2.1
          candidate.2.2.1 candidate.2.2.2 := fun hm =>
        h ((localEquationData_iff data _ _ _ _).mpr hm)
      simp [h, hm, ih]

/-- The local raw-data equation is a primitive-recursive relation. -/
theorem localEquationData_primrec : PrimrecRel fun data
    (candidate : IntVector3 × IntVector3 × IntVector3 × IntVector3) =>
    LocalEquationData data candidate.1 candidate.2.1 candidate.2.2.1 candidate.2.2.2 := by
  have hdata : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.1 := Primrec.fst
  have hinput : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have houtput : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hleft : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hright : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hdenominator : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => (p.1.2.1.val : Int) :=
    SignedPrimrec.intOfNat.comp (SignedPrimrec.pnatVal.comp
      (Primrec.fst.comp (Primrec.snd.comp hdata)))
  have hlinear : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hdata))
  have hoffset : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hdata))
  have hmatrixInput := IntMatrix3.mulVec_primrec.comp hlinear hinput
  have hlhs := IntVector3.add_primrec.comp hleft
    (IntVector3.add_primrec.comp hmatrixInput hoffset)
  have hrhs := IntVector3.add_primrec.comp
    (IntVector3.smul_primrec.comp hdenominator houtput) hright
  exact Primrec.eq.comp hlhs hrhs

/-- Pairing a raw branch tag with a carry vector is primitive recursive. -/
theorem carryColorTag_primrec :
    Primrec₂ fun tag carry => Nat.pair tag (IntVector3.code carry) :=
  Primrec₂.natPair.comp
    Primrec.fst
    (IntVector3.code_primrec.comp Primrec.snd)

/-- Constructing a transition from raw branch data and a candidate quadruple
is primitive recursive. -/
theorem transitionData_primrec : Primrec fun p : BranchData ×
    (IntVector3 × IntVector3 × IntVector3 × IntVector3) =>
    transitionData p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have hdata : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.1 := Primrec.fst
  have hinput : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have houtput : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hleft : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hright : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hOfTuple : Primrec Transition.equivEdgeTuple.symm := by
    simpa using (Primrec.of_equiv_symm (e := Transition.equivEdgeTuple) :
      Primrec Transition.equivEdgeTuple.symm)
  have hinputCode := IntVector3.code_primrec.comp hinput
  have houtputCode := IntVector3.code_primrec.comp houtput
  have htag : Primrec fun p : BranchData ×
      (IntVector3 × IntVector3 × IntVector3 × IntVector3) => p.1.1 :=
    Primrec.fst.comp hdata
  have hleftColor := carryColorTag_primrec.comp htag hleft
  have hrightColor := carryColorTag_primrec.comp htag hright
  exact (hOfTuple.comp
    (houtputCode.pair (hinputCode.pair (hrightColor.pair hleftColor)))).of_eq
      fun p => by rcases p with ⟨data, input, output, left, right⟩
                  rcases data with ⟨tag, denominator, linear, offset⟩
                  rfl

/-- Testing and emitting one raw-data candidate is primitive recursive. -/
theorem emitTransitionData_primrec : Primrec₂ emitTransitionData := by
  exact (Primrec.ite localEquationData_primrec
    (Primrec.option_some.comp transitionData_primrec)
    (Primrec.const none)).of_eq fun p => by
      unfold emitTransitionData
      rfl

/-- Filtering and emitting a candidate list for fixed raw branch data is
primitive recursive. -/
theorem emitTransitionListData_primrec : Primrec₂ fun (data : BranchData)
    (candidates : List (IntVector3 × IntVector3 × IntVector3 × IntVector3)) =>
    List.filterMap (emitTransitionData data) candidates := by
  exact Primrec.listFilterMap Primrec.snd
    (emitTransitionData_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)

/-- The complete raw-data transducer enumeration is primitive recursive. -/
theorem transducerData_primrec : Primrec fun p : BranchData ×
    List IntVector3 × List IntVector3 × Nat =>
    transducerData p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hdata : Primrec fun p : BranchData ×
      List IntVector3 × List IntVector3 × Nat => p.1 := Primrec.fst
  have hinputs : Primrec fun p : BranchData ×
      List IntVector3 × List IntVector3 × Nat => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have houtputs : Primrec fun p : BranchData ×
      List IntVector3 × List IntVector3 × Nat => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hbound : Primrec fun p : BranchData ×
      List IntVector3 × List IntVector3 × Nat => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hcandidates := candidates_primrec.comp
    (hinputs.pair (houtputs.pair (IntVector3.bounded_primrec.comp hbound)))
  exact emitTransitionListData_primrec.comp hdata hcandidates

/-- Computable form of `transducerData_primrec`. -/
theorem transducerData_computable : Computable fun p : BranchData ×
    List IntVector3 × List IntVector3 × Nat =>
    transducerData p.1 p.2.1 p.2.2.1 p.2.2.2 :=
  transducerData_primrec.to_comp

/-- Membership exposes exactly the finite alphabets, bounded carries, and local
integer equation used by the generator. -/
theorem mem_transducer_iff (branch : IntegerAffineBranch)
    (inputs outputs : List IntVector3) (carryBound : Nat) (t : Transition) :
    t ∈ branch.transducer inputs outputs carryBound ↔
      ∃ input output left right,
        input ∈ inputs ∧ output ∈ outputs ∧
          left ∈ IntVector3.bounded carryBound ∧
          right ∈ IntVector3.bounded carryBound ∧
          branch.LocalEquation input output left right ∧
          branch.transition input output left right = t := by
  constructor
  · intro ht
    rw [transducer, List.mem_map] at ht
    rcases ht with ⟨candidate, hcandidate, htransition⟩
    have hfiltered := List.mem_filter.mp hcandidate
    rcases candidate with ⟨input, output, left, right⟩
    have hcandidates :
        ((input ∈ inputs ∧ output ∈ outputs) ∧
          left ∈ IntVector3.bounded carryBound) ∧
          right ∈ IntVector3.bounded carryBound := by
      simpa [candidates] using hfiltered.1
    exact ⟨input, output, left, right, hcandidates.1.1.1, hcandidates.1.1.2,
      hcandidates.1.2, hcandidates.2,
      of_decide_eq_true hfiltered.2, htransition⟩
  · rintro ⟨input, output, left, right, hinput, houtput, hleft, hright,
      hequation, rfl⟩
    rw [transducer, List.mem_map]
    refine ⟨(input, output, left, right), ?_, rfl⟩
    apply List.mem_filter.mpr
    refine ⟨?_, decide_eq_true hequation⟩
    simp [candidates, hinput, houtput, hleft, hright]

/-- Every emitted transition uses the branch's tag on both horizontal colors. -/
theorem horizontal_tags_of_mem_transducer (branch : IntegerAffineBranch)
    (inputs outputs : List IntVector3) (carryBound : Nat) (t : Transition)
    (ht : t ∈ branch.transducer inputs outputs carryBound) :
    t.left.unpair.1 = branch.tag ∧ t.right.unpair.1 = branch.tag := by
  rw [mem_transducer_iff] at ht
  rcases ht with ⟨input, output, left, right, _, _, _, _, _, rfl⟩
  simp [transition, carryColor]

/-- A solution of the scaled integer equation satisfies the corresponding
rational affine carry equation. -/
theorem transition_satisfiesAffine (branch : IntegerAffineBranch)
    (input output left right : IntVector3)
    (heq : branch.LocalEquation input output left right) :
    (branch.transition input output left right).SatisfiesAffine
      branch.rationalMap digitValue branch.carryValue := by
  rcases input with ⟨ix, iy, iz⟩
  rcases output with ⟨ox, oy, oz⟩
  rcases left with ⟨lx, ly, lz⟩
  rcases right with ⟨rx, ry, rz⟩
  simp only [LocalEquation, IntVector3.smul, IntMatrix3.mulVec,
    IntVector3.add, IntVector3.mk.injEq] at heq
  rcases heq with ⟨hx, hy, hz⟩
  rw [Transition.SatisfiesAffine]
  simp only [transition, carryValue_carryColor, digitValue_code]
  funext i
  have hden : (branch.denominator : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt branch.denominator_pos
  fin_cases i
  · simp [RationalAffineMap.apply_eq, rationalMap, IntMatrix3.toLinearMap,
      IntVector3.toRat]
    field_simp
    exact_mod_cast hx
  · simp [RationalAffineMap.apply_eq, rationalMap, IntMatrix3.toLinearMap,
      IntVector3.toRat]
    field_simp
    exact_mod_cast hy
  · simp [RationalAffineMap.apply_eq, rationalMap, IntMatrix3.toLinearMap,
      IntVector3.toRat]
    field_simp
    exact_mod_cast hz

/-- Every transition emitted by the finite enumeration satisfies the branch's
rational affine map. -/
theorem satisfiesAffine_of_mem_transducer (branch : IntegerAffineBranch)
    (inputs outputs : List IntVector3) (carryBound : Nat) (t : Transition)
    (ht : t ∈ branch.transducer inputs outputs carryBound) :
    t.SatisfiesAffine branch.rationalMap digitValue branch.carryValue := by
  rw [mem_transducer_iff] at ht
  rcases ht with ⟨input, output, left, right, _, _, _, _, heq, rfl⟩
  exact branch.transition_satisfiesAffine input output left right heq

end IntegerAffineBranch

end Kari
end LeanWang
