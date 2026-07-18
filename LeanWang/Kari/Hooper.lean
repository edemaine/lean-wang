/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FullTM0
import LeanWang.Kari.Hooper.FiniteControl
import LeanWang.Kari.Hooper.FiniteTM0
import LeanWang.Kari.Hooper.CounterMachine
import LeanWang.Kari.Hooper.CounterProgram
import LeanWang.Kari.Hooper.CounterArithmetic
import LeanWang.Kari.Hooper.SourceMachine
import LeanWang.Kari.Hooper.StackEncoding
import LeanWang.Kari.Hooper.SourceControl
import LeanWang.Kari.Hooper.SourceProgram
import LeanWang.Kari.Hooper.SearchGeometry
import LeanWang.Kari.Hooper.CounterLayout
import LeanWang.Kari.Hooper.RegisterLayout
import LeanWang.Kari.Hooper.MarkerTape
import LeanWang.Kari.Hooper.MarkerShift
import LeanWang.Kari.Hooper.MarkerMachine
import LeanWang.Kari.Hooper.FiniteTM0Program
import LeanWang.Kari.Hooper.MarkerProgram
import LeanWang.Kari.Hooper.BasicLemma
import LeanWang.Kari.Hooper.NestingMachine

/-!
# Hooper's immortality construction

This namespace formalizes the bridge used before Kari's affine encoding:
starting from one designated nonhalting computation, construct a finite Turing
machine that has an immortal arbitrary configuration exactly when that
computation is nonhalting.

The current modules provide unrestricted full-tape semantics, explicit finite
transition tables, arithmetic stack encodings and an explicit finite-control
compiler for the fixed source tape, a four-register counter-program layer, its
exact finite five-boundary marker tape, collision-free suffix shifts for every
counter operation, concrete finite-table marker programs with independently
directed searches and shifts, relocatable fixed arithmetic blocks, a verified
finite-table linker, and the abstract strong-induction core of Hooper's nested
bounded-search construction.  The remaining files will compile the whole
source program and instantiate the nesting laws.
-/
