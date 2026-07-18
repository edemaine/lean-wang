/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.DominoProblem
import LeanWang.Kari.Final
import LeanWang.Robinson.Final

/-!
# Main Wang domino problem results

The statements in this module mention only the proof-neutral domino problem
interface.  The repository supplies independent Robinson and Kari--Hooper
reduction certificates; this public theorem surface chooses the Robinson
certificate while importing and checking both constructions.
-/

noncomputable section

namespace LeanWang

/-- Fixed nonhalting many-one reduces to the Wang domino problem. -/
theorem fixedNonhalting_manyOneReducible_dominoProblem :
    DominoProblem.FixedNonhalting ≤₀ DominoProblem.Holds :=
  Robinson.fixedNonhalting_manyOneReducible

/-- Fixed nonhalting many-one reduces to the encoded Wang domino problem. -/
theorem fixedNonhalting_manyOneReducible_encodedDominoProblem :
    DominoProblem.FixedNonhalting ≤₀ DominoProblem.EncodedHolds :=
  Robinson.fixedNonhalting_manyOneReducible_encodedDominoProblem

/-- Plane Wang tilability is co-r.e. by finite obstruction search. -/
theorem domino_problem_coRE : CoREPred DominoProblem.Holds :=
  DominoProblem.coRE

/-- The encoded Wang domino problem is likewise co-r.e. -/
theorem encoded_domino_problem_coRE : CoREPred DominoProblem.EncodedHolds :=
  DominoProblem.encodedCoRE

/-- The Wang domino problem is co-r.e.-hard. -/
theorem domino_problem_coRE_hard : DominoProblem.CoREHard :=
  Robinson.reduction.coREHard

/-- The encoded Wang domino problem is co-r.e.-hard. -/
theorem encoded_domino_problem_coRE_hard : DominoProblem.EncodedCoREHard :=
  Robinson.reduction.encodedCoREHard

/-- The Wang domino problem is co-r.e.-complete. -/
theorem domino_problem_coRE_complete : DominoProblem.CoREComplete :=
  Robinson.reduction.coREComplete

/-- The encoded Wang domino problem is co-r.e.-complete. -/
theorem encoded_domino_problem_coRE_complete : DominoProblem.EncodedCoREComplete :=
  Robinson.reduction.encodedCoREComplete

/-- The encoded Wang domino problem is undecidable. -/
theorem encoded_domino_problem_undecidable :
    DominoProblem.EncodedUndecidable :=
  Robinson.encoded_domino_problem_undecidable

/-- The Wang domino problem is undecidable. -/
theorem domino_problem_undecidable : DominoProblem.Undecidable :=
  Robinson.domino_problem_undecidable

/-- Compatibility name recording the concrete construction currently used. -/
theorem closed104_encoded_domino_problem_undecidable :
    DominoProblem.EncodedUndecidable :=
  encoded_domino_problem_undecidable

/-- Compatibility name recording the concrete construction currently used. -/
theorem closed104_domino_problem_undecidable : DominoProblem.Undecidable :=
  domino_problem_undecidable

end LeanWang

end
