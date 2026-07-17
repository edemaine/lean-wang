# lean-wang

Lean formalization of the undecidability of tiling the plane with Wang tiles.

The main statements and reduction interface are proof-neutral. The completed
proof follows the Berger/Robinson fixed-corner reduction described in
[`cirm.pdf`](cirm.pdf), using Robinson's scaffold argument from
[`robinson.pdf`](robinson.pdf), and lives in the `LeanWang.Robinson` module tree.
Source provenance is recorded in [`cirm.txt`](cirm.txt) and
[`robinson.txt`](robinson.txt); the current proof plan is in
[`plan.md`](plan.md).

## Proof structure

The Robinson proof uses one fixed universal Mathlib TM0 machine:

```text
Nat.Partrec.Code c
  -> encode c on the initial tape of one fixed universal TM0 machine
  -> simulate it by one fixed folded one-sided machine
  -> apply the generic finite-input Wang history construction
  -> combine with the certified Robinson scaffold
```

Only the finite initial tape depends on `c`; the machine control and simulation
rows are fixed. This avoids the obsolete source-dependent compiler/decoder
route entirely. The generated initializer, position-code compiler, and their
correctness modules have been removed from the repository; the retained proof
uses the generic machine-to-Wang theorem directly.

The shared endpoint is a `LeanWang.DominoProblem.Reduction`, which records the
computable tileset map and its equivalence with fixed-input nonhalting. The
public theorem surface is [`LeanWang.Final`](LeanWang/Final.lean):

```lean
LeanWang.fixedNonhalting_manyOneReducible_dominoProblem
LeanWang.fixedNonhalting_manyOneReducible_encodedDominoProblem
LeanWang.encoded_domino_problem_undecidable
LeanWang.domino_problem_undecidable
```

All four results have proof-technique-independent statements. The former
`closed104_*` theorem names remain as compatibility aliases. Mathlib currently
provides `REPred` and many-one reducibility but no co-r.e.-completeness
abstraction. The exposed reductions are the construction-specific ingredient
for the hardness direction; a future completeness theorem must also formalize
co-r.e.-completeness of fixed nonhalting. Membership can use the already-proved
finite-square compactness theorem, but still needs correctness and computability
of the finite-square search and an r.e. packaging of finite obstructions.

## Main modules

- `LeanWang.Basic` defines Wang tiles, finite tilesets, tilings, rectangles,
  and natural-number encodings.
- `LeanWang.Compactness` proves compactness for centered boxes, squares, and
  seeded quarter-plane tilings.
- `LeanWang.DominoProblem` defines the proof-neutral predicates, reduction
  certificate, many-one reductions, and generic undecidability corollaries.
- `LeanWang.UniversalCode` defines the common universal partial function.
- `LeanWang.Robinson.Machine.InputTiles` supplies the position and row colors
  used to force a finite bottom row.
- `LeanWang.Robinson.Machine.History` is the small input-independent kernel of
  finite local history blocks. The obsolete table-program and blank-input
  backends have been removed.
- `LeanWang.Robinson.Machine.UniversalTM0.Semantic` uses Mathlib's completeness
  theorem to choose one evaluator code directly, carries its finite supports
  through TM2, TM1, and TM0, and places the source code on its initial tape.
- `LeanWang.Robinson.Machine.UniversalTM0.Folded` defines the paired coordinates
  for the two-sided TM0 tape. `LeanWang.Robinson.Machine.UniversalTM0.Machine`
  simulates each TM0 move in one target step and each write in two, and proves
  exact halting equivalence.
- `LeanWang.Robinson.Machine.UniversalTM0.MachineData` computes the
  input-dependent bottom-row tiles and seed; all normal history tiles are fixed
  constants.
- `LeanWang.Robinson.Reduction` proves the fixed-corner and plane-tiling
  reductions and packages them into the shared certificate.
- `LeanWang.Robinson.Scaffold` defines the abstract scaffold certificate.
- `LeanWang.Robinson.Closed104.*` contains the corrected 104-component Figure
  13/Figure 16 transcription, substitution boundary certificates, and the
  successful finite Proposition 8 recognizability check. In particular,
  `PairCoverSeamRequiredForward` proves forward square forcing, while
  `ShadedCarrierCornerAddressing` constructs cofinally large addressed squares
  and proves pointed-plane realization.

The original exhaustive base-search route is retained as optional provenance in
[`PairCoverSeamPathSearch`](LeanWang/Robinson/Closed104/PairCoverSeamPathSearch.lean),
[`PairCoverSeamPathBaseAudit`](LeanWang/Robinson/Closed104/PairCoverSeamPathBaseAudit.lean),
and [`PairCoverSeamPathBoundedBase`](LeanWang/Robinson/Closed104/PairCoverSeamPathBoundedBase.lean).
The two base-audit modules are not imported by the main `LeanWang` library;
they provide an executable reference for the exhaustive searches that led to
the committed roots in
[`PairCoverSeamPathComponentCertificate`](LeanWang/Robinson/Closed104/PairCoverSeamPathComponentCertificate.lean).
The generic search engine remains mainline because independent local-coordinate
certificates reuse it.

## Build

```bash
lake build
```

All Lean source files are nonexecutable (`100644`). The source contains no
`sorry`, `admit`, or explicit `axiom` declarations. The large finite
certificates intentionally use `native_decide`, so Lean's axiom report includes
the corresponding generated code-evaluation axioms in addition to `propext`,
`Classical.choice`, and `Quot.sound`; it contains no `sorryAx` or other custom
project axiom.
