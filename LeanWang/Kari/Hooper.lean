/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FullTM0
import LeanWang.Kari.Hooper.FiniteControl
import LeanWang.Kari.Hooper.SourceMachine
import LeanWang.Kari.Hooper.SearchGeometry
import LeanWang.Kari.Hooper.BasicLemma

/-!
# Hooper's immortality construction

This namespace formalizes the bridge used before Kari's affine encoding:
starting from one designated nonhalting computation, construct a finite Turing
machine that has an immortal arbitrary configuration exactly when that
computation is nonhalting.

The current modules provide unrestricted full-tape semantics and the abstract
strong-induction core of Hooper's nested bounded-search construction.  The
remaining files will instantiate those laws with a typed finite-control
machine and connect its canonical computation to the fixed universal machine.
-/
