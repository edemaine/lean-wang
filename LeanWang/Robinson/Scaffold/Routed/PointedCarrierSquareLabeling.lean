/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Compactness
import LeanWang.Robinson.Scaffold.Routed.PointedCarrierLabeling

/-!
# Routed pointed carrier potentials on finite squares

Robinson substitution supertiles are naturally indexed by `Fin n × Fin n`,
whereas the compactness layer uses centered integer boxes.  This file packages
the carrier-potential obligation on finite squares, proves that it is preserved
by cropping, and converts squares cofinal in size to the centered-box API.
-/

namespace LeanWang
namespace RoutedPointedCarrierSquareLabeling

open RoutedPointedCarrierLabeling
open RoutedPointedCoreLabeling

/-- A finite scaffold square equipped with the two one-dimensional potentials
needed to route any pointed payload plane. -/
structure SquarePotential (S : RoutedScaffold) (n : Nat) where
  base : Rectangle n n
  base_valid : ValidRectangle S.tiles base
  point : Fin n → Fin n → Int × Int
  horizontal : Fin n → Fin n → EdgeLabel
  vertical : Fin n → Fin n → EdgeLabel
  corner_zero : ∀ i j, S.role (base i j) = .corner → point i j = (0, 0)
  hcompatible :
    ∀ i j, ∀ hi : i.val + 1 < n,
      (S.role (base i j)).isHorizontalCarrier = true →
      (S.role (base ⟨i.val + 1, hi⟩ j)).isHorizontalCarrier = true →
      EdgeLabel.Compatible
        (match S.role (base i j) with
          | .active | .corner => .east (point i j)
          | .horizontal => horizontal i j
          | .inactive | .vertical => .zero)
        (match S.role (base ⟨i.val + 1, hi⟩ j) with
          | .active | .corner => .west (point ⟨i.val + 1, hi⟩ j)
          | .horizontal => horizontal ⟨i.val + 1, hi⟩ j
          | .inactive | .vertical => .zero)
  vcompatible :
    ∀ i j, ∀ hj : j.val + 1 < n,
      (S.role (base i j)).isVerticalCarrier = true →
      (S.role (base i ⟨j.val + 1, hj⟩)).isVerticalCarrier = true →
      EdgeLabel.Compatible
        (match S.role (base i j) with
          | .active | .corner => .north (point i j)
          | .vertical => vertical i j
          | .inactive | .horizontal => .zero)
        (match S.role (base i ⟨j.val + 1, hj⟩) with
          | .active | .corner => .south (point i ⟨j.val + 1, hj⟩)
          | .vertical => vertical i ⟨j.val + 1, hj⟩
          | .inactive | .horizontal => .zero)

namespace SquarePotential

variable {S : RoutedScaffold} {N n r : Nat}

/-- Restrict a carrier-potential square to its southwest `n × n` subsquare. -/
def crop (potential : SquarePotential S N) (h : n ≤ N) : SquarePotential S n where
  base := Rectangle.crop potential.base h h
  base_valid := validRectangle_crop potential.base_valid h h
  point := fun i j => potential.point ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩
  horizontal := fun i j => potential.horizontal
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩
  vertical := fun i j => potential.vertical
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩
  corner_zero := by
    intro i j hcorner
    exact potential.corner_zero
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩ hcorner
  hcompatible := by
    intro i j hi hleft hright
    exact potential.hcompatible
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩
      (Nat.lt_of_lt_of_le hi h) hleft hright
  vcompatible := by
    intro i j hj hlower hupper
    exact potential.vcompatible
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩
      (Nat.lt_of_lt_of_le hj h) hlower hupper

/-- Reindex a square of side `2 * r + 1` as the centered box `[-r, r]²`. -/
def toPotential (square : SquarePotential S (boxSide r)) :
    RoutedPointedCarrierLabeling.Potential S r where
  base := fun p =>
    ⟨square.base (boxFinX p) (boxFinY p),
      square.base_valid.1 (boxFinX p) (boxFinY p)⟩
  base_valid := by
    constructor
    · intro p hp
      let q : Box r := ⟨(p.1.1 + 1, p.1.2), hp⟩
      have hsucc : boxCoord r (p.1.1 + 1) = boxCoord r p.1.1 + 1 :=
        boxCoord_succ p.2.1
      have hi : (boxFinX p).val + 1 < boxSide r := by
        simpa [boxFinX, q, hsucc] using (boxFinX q).isLt
      have hxq : boxFinX q = ⟨(boxFinX p).val + 1, hi⟩ := by
        apply Fin.ext
        simp [boxFinX, q, hsucc]
      have hyq : boxFinY q = boxFinY p := by
        apply Fin.ext
        simp [boxFinY, q]
      simpa [q, hxq, hyq] using
        square.base_valid.2.1 (boxFinX p) (boxFinY p) hi
    · intro p hp
      let q : Box r := ⟨(p.1.1, p.1.2 + 1), hp⟩
      have hsucc : boxCoord r (p.1.2 + 1) = boxCoord r p.1.2 + 1 :=
        boxCoord_succ p.2.2.2.1
      have hj : (boxFinY p).val + 1 < boxSide r := by
        simpa [boxFinY, q, hsucc] using (boxFinY q).isLt
      have hxq : boxFinX q = boxFinX p := by
        apply Fin.ext
        simp [boxFinX, q]
      have hyq : boxFinY q = ⟨(boxFinY p).val + 1, hj⟩ := by
        apply Fin.ext
        simp [boxFinY, q, hsucc]
      simpa [q, hxq, hyq] using
        square.base_valid.2.2 (boxFinX p) (boxFinY p) hj
  point := fun p => square.point (boxFinX p) (boxFinY p)
  horizontal := fun p => square.horizontal (boxFinX p) (boxFinY p)
  vertical := fun p => square.vertical (boxFinX p) (boxFinY p)
  corner_zero := by
    intro p hcorner
    exact square.corner_zero (boxFinX p) (boxFinY p) hcorner
  hcompatible := by
    intro p hp hleft hright
    let q : Box r := ⟨(p.1.1 + 1, p.1.2), hp⟩
    have hsucc : boxCoord r (p.1.1 + 1) = boxCoord r p.1.1 + 1 :=
      boxCoord_succ p.2.1
    have hi : (boxFinX p).val + 1 < boxSide r := by
      simpa [boxFinX, q, hsucc] using (boxFinX q).isLt
    have hxq : boxFinX q = ⟨(boxFinX p).val + 1, hi⟩ := by
      apply Fin.ext
      simp [boxFinX, q, hsucc]
    have hyq : boxFinY q = boxFinY p := by
      apply Fin.ext
      simp [boxFinY, q]
    have hright' :
        (S.role (square.base ⟨(boxFinX p).val + 1, hi⟩
          (boxFinY p))).isHorizontalCarrier = true := by
      simpa [q, hxq, hyq] using hright
    convert square.hcompatible (boxFinX p) (boxFinY p) hi hleft hright' using 1 <;>
      simp [q, hxq, hyq] <;> rfl
  vcompatible := by
    intro p hp hlower hupper
    let q : Box r := ⟨(p.1.1, p.1.2 + 1), hp⟩
    have hsucc : boxCoord r (p.1.2 + 1) = boxCoord r p.1.2 + 1 :=
      boxCoord_succ p.2.2.2.1
    have hj : (boxFinY p).val + 1 < boxSide r := by
      simpa [boxFinY, q, hsucc] using (boxFinY q).isLt
    have hxq : boxFinX q = boxFinX p := by
      apply Fin.ext
      simp [boxFinX, q]
    have hyq : boxFinY q = ⟨(boxFinY p).val + 1, hj⟩ := by
      apply Fin.ext
      simp [boxFinY, q, hsucc]
    have hupper' :
        (S.role (square.base (boxFinX p)
          ⟨(boxFinY p).val + 1, hj⟩)).isVerticalCarrier = true := by
      simpa [q, hxq, hyq] using hupper
    convert square.vcompatible (boxFinX p) (boxFinY p) hj hlower hupper' using 1 <;>
      simp [q, hxq, hyq] <;> rfl

end SquarePotential

/-- Pure carrier-potential geometry on squares of every finite side length. -/
def HasRoutedPointedCarrierSquares (S : RoutedScaffold) : Prop :=
  ∀ n : Nat, Nonempty (SquarePotential S n)

/-- Cofinal carrier-potential squares suffice for squares of every size. -/
theorem hasRoutedPointedCarrierSquares_of_cofinal
    {S : RoutedScaffold}
    (potentials : ∀ n : Nat,
      ∃ N : Nat, n ≤ N ∧ Nonempty (SquarePotential S N)) :
    HasRoutedPointedCarrierSquares S := by
  intro n
  rcases potentials n with ⟨N, hnN, ⟨potential⟩⟩
  exact ⟨potential.crop hnN⟩

/-- Square carrier potentials imply the centered-box carrier potentials used
by the routed compactness construction. -/
theorem hasRoutedPointedCarrierPotentials_of_squares
    {S : RoutedScaffold}
    (squares : HasRoutedPointedCarrierSquares S) :
    HasRoutedPointedCarrierPotentials S := by
  intro r
  rcases squares (boxSide r) with ⟨square⟩
  exact ⟨square.toPotential⟩

/-- Cofinal finite square carrier potentials realize all pointed payload
planes through the routed scaffold. -/
theorem realizesRoutedPointedPlanes_of_cofinalSquares
    {S : RoutedScaffold}
    (potentials : ∀ n : Nat,
      ∃ N : Nat, n ≤ N ∧ Nonempty (SquarePotential S N)) :
    RealizesRoutedPointedPlanes S :=
  RoutedPointedCarrierLabeling.realizesRoutedPointedPlanes_of_carrierPotentials
    (hasRoutedPointedCarrierPotentials_of_squares
      (hasRoutedPointedCarrierSquares_of_cofinal potentials))

end RoutedPointedCarrierSquareLabeling
end LeanWang
