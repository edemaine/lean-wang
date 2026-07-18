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
import LeanWang.Kari.Hooper.CounterArithmeticLiveness
import LeanWang.Kari.Hooper.SourceMachine
import LeanWang.Kari.Hooper.StackEncoding
import LeanWang.Kari.Hooper.StackEncodingComputable
import LeanWang.Kari.Hooper.SourceControl
import LeanWang.Kari.Hooper.SourceProgram
import LeanWang.Kari.Hooper.SourceRegisterSemantics
import LeanWang.Kari.Hooper.GlobalSourceProgram
import LeanWang.Kari.Hooper.GlobalSourceSemantics
import LeanWang.Kari.Hooper.CounterLiveness
import LeanWang.Kari.Hooper.GlobalSourceLiveness
import LeanWang.Kari.Hooper.SearchGeometry
import LeanWang.Kari.Hooper.CounterLayout
import LeanWang.Kari.Hooper.RegisterLayout
import LeanWang.Kari.Hooper.MarkerTape
import LeanWang.Kari.Hooper.MarkerShift
import LeanWang.Kari.Hooper.MarkerMachine
import LeanWang.Kari.Hooper.FiniteTM0Program
import LeanWang.Kari.Hooper.FiniteTM0Mirror
import LeanWang.Kari.Hooper.MarkerProgram
import LeanWang.Kari.Hooper.MarkerChain
import LeanWang.Kari.Hooper.MarkerSchedule
import LeanWang.Kari.Hooper.MarkerNavigation
import LeanWang.Kari.Hooper.BasicLemma
import LeanWang.Kari.Hooper.BasicLemmaConverse
import LeanWang.Kari.Hooper.NestingMachine
import LeanWang.Kari.Hooper.BoundedMarkerProgram
import LeanWang.Kari.Hooper.CanonicalInitializerFrame
import LeanWang.Kari.Hooper.CanonicalInitializerProgramComputable

/-!
# Hooper's immortality construction

This namespace formalizes the bridge used before Kari's affine encoding:
starting from one designated nonhalting computation, construct a finite Turing
machine that has an immortal arbitrary configuration exactly when that
computation is nonhalting.

The current modules provide unrestricted full-tape semantics, explicit finite
transition tables, arithmetic stack encodings and an explicit finite-control
compiler for the fixed source tape, one finite deterministic counter program
covering every source transition together with its exact designated-start
semantics, a four-register counter-program layer, its
exact finite five-boundary marker tape, collision-free suffix shifts for every
counter operation together with exact chained increment and
positive-decrement schedules, exact navigation between their common boundary
anchors, concrete finite-table marker programs with
independently directed searches and shifts,
relocatable and reflectable finite tables, a verified finite-table linker,
concrete arbitrary-entry liveness laws for the complete fixed source program,
a deterministic tagged controller for a finite family of bounded searches,
an executable uniformly computable tag-sensitive canonical initializer with
exact framed semantics,
and both directions of the abstract strong-induction core of Hooper's nested
construction.  The remaining files will compile the counter instructions to
those searches and implement the shared canonical core that discharges the
nesting laws.
-/
