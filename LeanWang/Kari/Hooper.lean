/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FullTM0
import LeanWang.Kari.Hooper.FiniteControl
import LeanWang.Kari.Hooper.FiniteTM0
import LeanWang.Kari.Hooper.CounterMachine
import LeanWang.Kari.Hooper.SourceMachine
import LeanWang.Kari.Hooper.SearchGeometry
import LeanWang.Kari.Hooper.CounterLayout
import LeanWang.Kari.Hooper.RegisterLayout
import LeanWang.Kari.Hooper.MarkerTape
import LeanWang.Kari.Hooper.BasicLemma

/-!
# Hooper's immortality construction

This namespace formalizes the bridge used before Kari's affine encoding:
starting from one designated nonhalting computation, construct a finite Turing
machine that has an immortal arbitrary configuration exactly when that
computation is nonhalting.

The current modules provide unrestricted full-tape semantics, explicit finite
transition tables, a four-register counter-program layer, its exact finite
five-boundary marker tape, and the abstract strong-induction core of Hooper's
nested bounded-search construction.  The remaining files will compile the
proved suffix shifts to a guarded finite-control machine and instantiate the
nesting laws.
-/
