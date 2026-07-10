/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104QuarterPlaneDecode

/-!
Red-path geometry in the quarter-tile presentation.

The thick red atoms use two lanes in each direction.  Subdivision turns those
lanes into literal tile quarters: `R0`/`R2` occupy the east/west vertical lane,
and `R1`/`R3` occupy the north/south horizontal lane.  The four corner
components similarly occupy one inward-facing quarter of their red board.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace QuarterGeometry

open Figure16 RedCycles

set_option maxRecDepth 20000

/-- Whether a thick component contains the specified straight-line atom. -/
def containsLine (component : Thick) (line : ThickLine) : Bool :=
  match component.lineSum? with
  | none => false
  | some sum => decide (sum.first = line || sum.second = line)

/-- Red vertical path in the west (`false`) or east (`true`) half of a tile. -/
def redVerticalAt (component : Thick) (east : Bool) : Bool :=
  if east then containsLine component .r0 else containsLine component .r2

/-- Red horizontal path in the south (`false`) or north (`true`) half of a tile. -/
def redHorizontalAt (component : Thick) (north : Bool) : Bool :=
  if north then containsLine component .r1 else containsLine component .r3

/-- The quarter occupied by the red turn of a thick corner component. -/
def redCorner? : Thick → Option Quadrant
  | .a => some .southeast
  | .b => some .northeast
  | .c => some .northwest
  | .d => some .southwest
  | _ => none

/-- Whether the thick red path occupies a given tile quarter. -/
def redAt (component : Thick) (quadrant : Quadrant) : Bool :=
  decide (redCorner? component = some quadrant) ||
    redVerticalAt component quadrant.xBit ||
    redHorizontalAt component quadrant.yBit

@[simp] theorem redCorner_a : redCorner? .a = some .southeast := rfl
@[simp] theorem redCorner_b : redCorner? .b = some .northeast := rfl
@[simp] theorem redCorner_c : redCorner? .c = some .northwest := rfl
@[simp] theorem redCorner_d : redCorner? .d = some .southwest := rfl

@[simp] theorem redAt_a (quadrant : Quadrant) :
    redAt .a quadrant = decide (quadrant = .southeast) := by
  cases quadrant <;> decide

@[simp] theorem redAt_b (quadrant : Quadrant) :
    redAt .b quadrant = decide (quadrant = .northeast) := by
  cases quadrant <;> decide

@[simp] theorem redAt_c (quadrant : Quadrant) :
    redAt .c quadrant = decide (quadrant = .northwest) := by
  cases quadrant <;> decide

@[simp] theorem redAt_d (quadrant : Quadrant) :
    redAt .d quadrant = decide (quadrant = .southwest) := by
  cases quadrant <;> decide

/- Exact quarter-level orientation of the uniform depth-two red board. -/
set_option linter.style.nativeDecide false in
theorem fixedBoard_oriented (parent : Index) :
    let grid := supertile 2 parent
    thickAt grid 1 1 = .b ∧
    thickAt grid 3 1 = .c ∧
    thickAt grid 1 3 = .a ∧
    thickAt grid 3 3 = .d ∧
    containsLine (thickAt grid 2 1) .r1 = true ∧
    containsLine (thickAt grid 2 3) .r3 = true ∧
    containsLine (thickAt grid 1 2) .r0 = true ∧
    containsLine (thickAt grid 3 2) .r2 = true := by
  revert parent
  native_decide

end QuarterGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
