/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.SourceCore.SearchCode

/-!
Fixed-code primitive-recursion facts for bounded-search source decoders.

The final reduction needs the corresponding fact uniformly in
`Nat.Partrec.Code`.  This module records the already-available fixed-code
computability supplied by the folded compiler, keeping the remaining
uniformization target explicit.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

set_option linter.style.longLine false in
/--
For each fixed source code, the bounded-search offset descriptor decoder is
primitive recursive in the fuel, statement offset, and variable-list offset.

The stronger source theorem must make the same construction primitive recursive
while the source code varies.
-/
theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode c p.1 p.2.1 p.2.2) := by
  exact (TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode_primrec_fixed
    (NatPartrecToToPartrec.translate c)).of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexFromWithSearchCode
      rfl

end TM0FoldedReduction

end LeanWang
