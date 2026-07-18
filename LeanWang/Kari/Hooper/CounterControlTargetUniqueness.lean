/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BoundedMarkerProgram

/-!
# Uniqueness of bounded-marker target recognition

Boundary symbols and return-tag symbols occupy disjoint parts of the
controller alphabet.  Consequently one concrete nonblank symbol determines
the abstract `Target` that recognizes it.  This small inverse fact is useful
when an arbitrary first obstruction is later recognized by a real generated
command.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlTargetUniqueness

open BoundedMarkerProgram

/-- Two bounded-marker targets matching the same physical symbol are equal. -/
theorem target_eq_of_matches {numTags : Nat}
    {first second : Target numTags} {symbol : Symbol numTags}
    (hfirst : first.Matches symbol) (hsecond : second.Matches symbol) :
    first = second := by
  cases first with
  | boundary firstLabel =>
      cases second with
      | boundary secondLabel =>
          congr 1
          apply (boundarySymbol_injective firstLabel secondLabel).mp
          exact hfirst.symm.trans hsecond
      | anyTag =>
          rcases hsecond with ⟨tag, htag⟩
          exact False.elim
            (boundarySymbol_ne_tagSymbol firstLabel tag
              (hfirst.symm.trans htag))
  | anyTag =>
      cases second with
      | boundary secondLabel =>
          rcases hfirst with ⟨tag, htag⟩
          exact False.elim
            (boundarySymbol_ne_tagSymbol secondLabel tag
              (hsecond.symm.trans htag))
      | anyTag => rfl

end CounterControlTargetUniqueness
end Hooper
end Kari
end LeanWang
