/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.GlobalSourceSemantics
import LeanWang.Kari.Hooper.MarkerNavigation
import LeanWang.Kari.Hooper.NestingMachine
import LeanWang.Kari.Hooper.StackEncodingComputable

/-!
# Geometry of the code-dependent canonical initializer

Every failed bounded search launches the same designated source computation.
The source program is fixed, but its two-stack input contains the code being
reduced.  This file chooses an effective bounded-search radius large enough
to place that code's complete five-boundary register layout between the
relocated return tag and the exhausted end of the bounded prefix.

The relocated tag is at coordinate `0`; boundary `0` is placed at coordinate
`1`, and the remaining boundaries follow in the positive direction.  The
chosen radius leaves one blank cell after boundary `4`.  Later modules will
realize this finite geometry by explicit initializer rules in both directions.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CanonicalInitializer

open CounterMachine

noncomputable section

/-- Registers of the designated nested computation. -/
def registers (c : Nat.Partrec.Code) : Registers :=
  (GlobalSourceSemantics.canonicalCounterCfg c).registers

@[simp]
theorem registers_left (c : Nat.Partrec.Code) : (registers c).left = 0 :=
  rfl

@[simp]
theorem registers_right (c : Nat.Partrec.Code) :
    (registers c).right =
      (StackEncoding.sourceInitialRegisters c).right :=
  rfl

@[simp]
theorem registers_temp (c : Nat.Partrec.Code) : (registers c).temp = 0 :=
  rfl

@[simp]
theorem registers_clock (c : Nat.Partrec.Code) : (registers c).clock = 0 :=
  rfl

/-- Distance from the relocated tag to the rightmost canonical boundary.
Boundary `0` is one cell after the tag, so this is one more than the ordinary
boundary-`4` coordinate. -/
def span (c : Nat.Partrec.Code) : Nat :=
  (StackEncoding.sourceInitialRegisters c).right + 5

/-- Code-dependent bounded-search radius.  Since `NestingMachine.bound`
adds one, the exhausted endpoint is one blank cell beyond the initialized
rightmost boundary. -/
def radius (c : Nat.Partrec.Code) : Nat := span c

theorem radius_primrec : Primrec radius := by
  exact Primrec.nat_add.comp
    StackEncoding.sourceInitialRegisters_right_primrec
    (Primrec.const 5)

theorem radius_computable : Computable radius :=
  radius_primrec.to_comp

@[simp]
theorem clockBoundary_registers (c : Nat.Partrec.Code) :
    RegisterLayout.clockBoundary (registers c) + 1 = span c := by
  simp only [RegisterLayout.clockBoundary_eq, registers_left,
    registers_right, registers_temp, registers_clock, span]
  omega

/-- Coordinate of boundary `j` after shifting the canonical layout one cell
to the right of the relocated tag. -/
def boundaryCoordinate (c : Nat.Partrec.Code) (j : Fin 5) : Nat :=
  1 + CounterLayout.boundaryPos (RegisterLayout.values (registers c)) j

theorem boundaryPosition_nonnegative (c : Nat.Partrec.Code) (j : Fin 5) :
    0 ≤ MarkerTape.boundaryPosition (registers c) j := by
  simp [MarkerTape.boundaryPosition]

theorem boundaryCoordinate_eq (c : Nat.Partrec.Code) (j : Fin 5) :
    (boundaryCoordinate c j : Int) =
      1 + MarkerTape.boundaryPosition (registers c) j := by
  simp [boundaryCoordinate, MarkerTape.boundaryPosition]

/-- Every initialized boundary lies no farther than the chosen span. -/
theorem boundaryCoordinate_le_span (c : Nat.Partrec.Code) (j : Fin 5) :
    boundaryCoordinate c j ≤ span c := by
  have hj : (j : Nat) ≤ 4 := by omega
  have hmono := CounterLayout.boundaryPos_mono
    (RegisterLayout.values (registers c)) hj
  rw [← clockBoundary_registers]
  simp only [boundaryCoordinate]
  change 1 + CounterLayout.boundaryPos
      (RegisterLayout.values (registers c)) j ≤
    RegisterLayout.clockBoundary (registers c) + 1
  rw [Nat.add_comm (RegisterLayout.clockBoundary (registers c)) 1]
  exact Nat.add_le_add_left hmono 1

/-- In particular, every initialized boundary is strictly before the
exhausted endpoint at `NestingMachine.bound radius`. -/
theorem boundaryCoordinate_lt_bound (c : Nat.Partrec.Code) (j : Fin 5) :
    boundaryCoordinate c j < NestingMachine.bound (radius c) := by
  have hle := boundaryCoordinate_le_span c j
  simp only [radius, NestingMachine.bound]
  omega

/-- Boundary `4` is exactly at the end of the initialized span. -/
theorem boundaryFourCoordinate (c : Nat.Partrec.Code) :
    boundaryCoordinate c 4 = span c := by
  simp only [boundaryCoordinate]
  change 1 + RegisterLayout.clockBoundary (registers c) = span c
  rw [Nat.add_comm]
  exact clockBoundary_registers c

/-- The first cell after boundary `4` is the exhausted bounded-prefix
endpoint, and is therefore available as an initial blank growth cell. -/
theorem boundaryFour_succ_eq_bound (c : Nat.Partrec.Code) :
    boundaryCoordinate c 4 + 1 = NestingMachine.bound (radius c) := by
  rw [boundaryFourCoordinate]
  rfl

end

end CanonicalInitializer
end Hooper
end Kari
end LeanWang
