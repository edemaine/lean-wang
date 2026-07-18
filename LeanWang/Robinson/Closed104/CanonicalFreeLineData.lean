/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSignals
import LeanWang.Robinson.Closed104.ShadedSubstitutionData

/-!
# Local canonical free-line checks

The selected shade substitution gives one explicit parity potential on every
two-level Robinson macrocell.  This file records the small executable checks
needed to propagate free rows and columns in that canonical potential.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalFreeLine

open Signals.FreeCellLocal ShadedSubstitution

def flipShade (state : RedShades.State) : RedShades.State :=
  { west := state.west.map RedShades.Shade.opposite
    east := state.east.map RedShades.Shade.opposite
    south := state.south.map RedShades.Shade.opposite
    north := state.north.map RedShades.Shade.opposite }

def selectedVertical? (node x y : Nat) :
    Option Signals.HorizontalInterior :=
  match modelData node with
  | none => none
  | some data =>
      ShadedSignals.selectedVerticalFor (components data.parent).2.1
        (quadrantAt x y) (flipShade (data.block.at (x % 2) (y % 2)))

def selectedHorizontal? (node x y : Nat) :
    Option Signals.VerticalInterior :=
  match modelData node with
  | none => none
  | some data =>
      ShadedSignals.selectedHorizontalFor (components data.parent).2.1
        (quadrantAt x y) (flipShade (data.block.at (x % 2) (y % 2)))

def clearVertical (node x y : Nat) : Bool :=
  (modelData node).isSome && selectedVertical? node x y == none

def clearHorizontal (node x y : Nat) : Bool :=
  (modelData node).isSome && selectedHorizontal? node x y == none

def fineNode? (node x y : Nat) : Option Nat :=
  childNode node ((x / 2) % 4 + 4 * ((y / 2) % 4))

def fineClearVertical (node x y : Nat) : Bool :=
  match fineNode? node x y with
  | none => false
  | some child => clearVertical child x y

def fineClearHorizontal (node x y : Nat) : Bool :=
  match fineNode? node x y with
  | none => false
  | some child => clearHorizontal child x y

def rowClear (node y : Nat) : Bool :=
  (List.range 2).all fun x => clearVertical node x y

def columnClear (node x : Nat) : Bool :=
  (List.range 2).all fun y => clearHorizontal node x y

def fineRowClear (node y : Nat) : Bool :=
  (List.range 8).all fun x => fineClearVertical node x y

def fineColumnClear (node x : Nat) : Bool :=
  (List.range 8).all fun y => fineClearHorizontal node x y

/-- The part of a refined row that enters the strict board from its westmost
parent cell. -/
def westStripClear (node y : Nat) : Bool :=
  (List.range 6).all fun dx => fineClearVertical node (dx + 2) y

/-- The part of a refined column that enters the strict board from its
southmost parent cell. -/
def southStripClear (node x : Nat) : Bool :=
  (List.range 6).all fun dy => fineClearHorizontal node x (dy + 2)

def cycleSourceShade? (node : Nat) : Option RedShades.Shade :=
  match fineNode? node 4 3 with
  | none => none
  | some child =>
      match modelData child with
      | none => none
      | some data => (data.block.at 0 1).west

/-- All local implications used by the even-phase semantic recurrence. -/
def evenLocalChecks (node : Nat) : List Bool :=
  [!rowClear node 0 || fineRowClear node 0,
    !rowClear node 1 || (fineRowClear node 1 && fineRowClear node 2),
    !columnClear node 0 || fineColumnClear node 0,
    !columnClear node 1 ||
      (fineColumnClear node 1 && fineColumnClear node 2),
    westStripClear node 0,
    westStripClear node 1,
    westStripClear node 2,
    southStripClear node 0,
    southStripClear node 1,
    southStripClear node 2,
    decide (cycleSourceShade? node = some .dark)]

def evenLocalValid (node : Nat) : Bool :=
  (evenLocalChecks node).all id

def evenLocalComplete : Bool :=
  reachable.all evenLocalValid

def evenBaseNode? (node : Nat) : Option Nat :=
  childNode node 10

def evenBaseValid (node : Nat) : Bool :=
  match evenBaseNode? node with
  | none => false
  | some child => rowClear child 1 && columnClear child 1

def evenBaseComplete : Bool :=
  reachable.all evenBaseValid

end CanonicalFreeLine
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
