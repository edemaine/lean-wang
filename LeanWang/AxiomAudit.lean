/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanWang.Abstract
import LeanWang.Final
import LeanWang.Kari.Final
import Lean.Util.CollectAxioms

/-!
# Axiom regression checks for both Wang domino-problem constructions

Finite certificates use kernel reduction. Reject assumptions beyond Lean's
three standard axioms, including native evaluation and unfinished proofs.
-/

open Lean Elab Command in
run_cmd do
  for name in [``LeanWang.Abstract.coRE_complete,
      ``LeanWang.Abstract.undecidable,
      ``LeanWang.domino_problem_coRE_complete,
      ``LeanWang.encoded_domino_problem_coRE_complete,
      ``LeanWang.domino_problem_undecidable,
      ``LeanWang.encoded_domino_problem_undecidable,
      ``LeanWang.Kari.domino_problem_coRE_complete,
      ``LeanWang.Kari.encoded_domino_problem_coRE_complete,
      ``LeanWang.Kari.domino_problem_undecidable,
      ``LeanWang.Kari.encoded_domino_problem_undecidable] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do
      throwError "{name} depends on unexpected axioms: {extra}"
