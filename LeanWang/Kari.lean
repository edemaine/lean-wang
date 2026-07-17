/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Transducer
import LeanWang.Kari.Dynamics
import LeanWang.Kari.HalfPlane
import LeanWang.Kari.Affine
import LeanWang.Kari.Beatty
import LeanWang.Kari.TransducerHalfPlane
import LeanWang.Kari.Hooper

/-!
# Kari's proof of Wang domino undecidability

This namespace contains an independent formalization of Kari's construction.
It is intentionally isolated from `LeanWang.Robinson`; both constructions will
eventually provide the shared `LeanWang.DominoProblem.Reduction` interface.
-/
