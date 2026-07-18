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
import LeanWang.Kari.Hooper.BoundedMarkerProgramComputable
import LeanWang.Kari.Hooper.BoundedMarkerContinuation
import LeanWang.Kari.Hooper.CanonicalInitializerFrame
import LeanWang.Kari.Hooper.CanonicalInitializerProgramComputable
import LeanWang.Kari.Hooper.FramedCounterGeometry
import LeanWang.Kari.Hooper.CounterControlPlan
import LeanWang.Kari.Hooper.CounterControlPlanComputable
import LeanWang.Kari.Hooper.CounterControlWellFormed
import LeanWang.Kari.Hooper.CounterControlCommandAt
import LeanWang.Kari.Hooper.CounterControlDeterministic
import LeanWang.Kari.Hooper.CounterControlDirectSemantics
import LeanWang.Kari.Hooper.CounterControlBridge
import LeanWang.Kari.Hooper.CounterControlNestingBridge
import LeanWang.Kari.Hooper.CounterControlNavigationSemantics
import LeanWang.Kari.Hooper.CounterControlShiftSemantics
import LeanWang.Kari.Hooper.CounterControlRouteSemantics
import LeanWang.Kari.Hooper.CounterControlCleanupSemantics

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
a deterministic, uniformly primitive-recursive tagged controller for a finite
family of bounded searches,
an executable uniformly computable tag-sensitive canonical initializer with
exact framed semantics, framed increment/decrement and collision-cleanup
geometry, an executable two-orientation counter-control plan with
tag-selected initialization, structurally verified search indexing and table
determinism whose complete table is primitive recursive in the source code,
command-oriented access to compiled controller blocks, reusable
execution bridges from bounded commands to framed tape endpoints, and an
exact nearby-or-nested execution dichotomy, together with exact near-branch
semantics for direct glue, navigation, erasure, and both marker-shift
orientations, plus a generic nearby-or-nested semantics theorem for compiled
boundary routes and the complete collision-cleanup chain back to the saved
command (or its first deeper nested frame),
and both directions of the abstract strong-induction core of Hooper's nested
construction.  The remaining files prove the compiled plan's operational
semantics and use its shared canonical core to discharge the nesting laws.
-/
