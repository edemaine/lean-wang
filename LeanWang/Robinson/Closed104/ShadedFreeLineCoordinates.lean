/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeCycles

/-!
# Coordinates for the two Robinson free-line phases

The hierarchy coordinates are separated from the semantic recurrence so
finite coordinate checkers can depend on them without importing proof-heavy
native audits.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineRecurrence

open RedCycles RedShadeCycles Signals.FreeCellLocal

inductive Phase where
  | even
  | odd
deriving DecidableEq, Repr

def Phase.factor : Phase → Nat
  | .even => 1
  | .odd => 2

def Phase.extra : Phase → Nat
  | .even => 0
  | .odd => 1

def scale (phase : Phase) (depth : Nat) : Nat :=
  phase.factor * 4 ^ depth

def refinementDepth (phase : Phase) (depth : Nat) : Nat :=
  2 * depth + phase.extra + 2

def localGrid (phase : Phase) (depth : Nat) (parent : Index) : Nat → Nat → Index :=
  iterateRefine (refinementDepth phase depth) (fun _ _ => parent)

def west (phase : Phase) (depth : Nat) : Nat := scale phase depth

def east (phase : Phase) (depth : Nat) : Nat := 3 * scale phase depth

def quarterStart (phase : Phase) (depth : Nat) : Nat :=
  quarterWest (west phase depth)

end ShadedFreeLineRecurrence
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
