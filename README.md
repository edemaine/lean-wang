# lean-wang

Lean formalization of the undecidability of tiling the plane with Wang tiles.

**Status:** two independent proofs are complete: the Berger/Robinson
construction and the Kari--Hooper affine construction. Each supplies the same
proof-neutral reduction certificate and therefore proves co-r.e. completeness
and undecidability of both the direct and natural-number-encoded Wang domino
problems.

The main statements and reduction interface are proof-neutral. The Robinson
proof follows [`cirm.pdf`](cirm.pdf) and [`robinson.pdf`](robinson.pdf); the
Kari--Hooper development follows [`hooper.pdf`](hooper.pdf). Source-provenance
text files are stored beside the papers, and the historical Robinson proof plan
is in [`plan.md`](plan.md).

## Where to start

- [`LeanWang/Final.lean`](LeanWang/Final.lean) contains the main public theorem
  statements. It uses the Robinson certificate while keeping the statements
  independent of the proof technique, so downstream projects can import the
  theorem surface without also building the Kari--Hooper proof.
- [`LeanWang.lean`](LeanWang.lean) is the complete aggregate entry point. It
  imports the public theorem surface and independently checks the Kari--Hooper
  certificate, and is the default `lake build` target.
- [`LeanWang/DominoProblem.lean`](LeanWang/DominoProblem.lean) defines the
  proof-neutral domino predicates, the shared reduction certificate, and the
  generic co-r.e.-completeness and undecidability consequences.
- [`LeanWang/Robinson/Final.lean`](LeanWang/Robinson/Final.lean) is the short
  construction-specific endpoint: it combines the machine simulation and the
  concrete scaffold into a `DominoProblem.Reduction`.
- [`LeanWang/Robinson/Reduction.lean`](LeanWang/Robinson/Reduction.lean) is the
  main place to read how fixed-corner machine tilings are converted to plane
  tilings.
- [`LeanWang/Kari/Final.lean`](LeanWang/Kari/Final.lean) is the corresponding
  Kari--Hooper endpoint: it combines the effective counter controller, Kari's
  affine compiler, and the Wang encoding into a second `DominoProblem.Reduction`.
- [`LeanWang/Kari.lean`](LeanWang/Kari.lean) is the aggregate entry point for
  the completed Kari--Hooper formalization.

## Proof structure

### Robinson

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

### Kari--Hooper

The second proof formalizes an effective version of Hooper's nested
bounded-search construction:

```text
Nat.Partrec.Code c
  -> compile a deterministic finite counter-control TM0 table
  -> prove arbitrary-configuration immortality iff c runs forever
  -> compile the finite table to Kari's piecewise-affine system
  -> encode its bi-infinite affine diagrams by Wang tiles
```

The difficult arbitrary-configuration converse is organized around guarded
generated searches. The completed modules prove the finite counter-control
compiler and its designated forward simulation, rule out every immortal
off-path controller configuration, and feed the resulting immortality
equivalence through Kari's affine and Wang-tile encodings.

Both completed constructions produce a `LeanWang.DominoProblem.Reduction`,
which records the computable tileset map and its equivalence with fixed-input
nonhalting. The proof-neutral public theorem surface is
[`LeanWang.Final`](LeanWang/Final.lean):

```lean
LeanWang.fixedNonhalting_manyOneReducible_dominoProblem
LeanWang.fixedNonhalting_manyOneReducible_encodedDominoProblem
LeanWang.domino_problem_coRE
LeanWang.encoded_domino_problem_coRE
LeanWang.domino_problem_coRE_hard
LeanWang.encoded_domino_problem_coRE_hard
LeanWang.domino_problem_coRE_complete
LeanWang.encoded_domino_problem_coRE_complete
LeanWang.encoded_domino_problem_undecidable
LeanWang.domino_problem_undecidable
```

These results have proof-technique-independent statements.  The former
`closed104_*` theorem names remain as compatibility aliases.  Co-r.e.
membership is proved by enumerating finite square obstructions, while hardness
is a generic corollary of any such reduction from fixed nonhalting.

## Directory structure

```text
LeanWang/
  Basic.lean, Compactness.lean, FiniteSearch.lean
  CoRE.lean, DominoProblem.lean, Final.lean
  UniversalCode.lean
  UniversalTM0/
  Robinson/
    Machine/
      UniversalTM0/
    Scaffold/
      Routed/
    Closed104/
    Reduction.lean, Final.lean
  Kari/
    Final.lean
    Hooper/
```

The top-level modules are shared by all proof techniques:

- `Basic`, `Compactness`, and `FiniteSearch` define Wang tiles, finite
  rectangles, compactness, and computable finite obstruction search.
- `CoRE` and `DominoProblem` define the proof-neutral computability statements
  and derive the generic consequences of any `DominoProblem.Reduction`.
- `UniversalCode` and `UniversalTM0/` select a universal Mathlib evaluator and
  transport its finite machine support through Mathlib's TM2, TM1, and TM0
  models.
- `Final` is the public theorem module backed by the Robinson certificate.
  The root `LeanWang` module additionally imports `Kari.Final`, so the default
  `lake build` checks both completed proof certificates.

The completed Robinson proof is split by responsibility:

- `Robinson/Machine/` contains the finite-input Wang history construction.
  Its `UniversalTM0/` subdirectory folds the two-sided universal TM0 tape into
  one side, proves exact halting equivalence, and computes the input-dependent
  bottom row and seed. The ordinary history tiles remain fixed.
- `Robinson/Scaffold/` defines the abstract fixed-corner scaffold interface;
  `Scaffold/Routed/` adds the routed carrier and pointed-plane machinery used
  by the concrete construction.
- `Robinson/Closed104/` contains the corrected 104-component Figure 13/Figure
  16 transcription, substitution and shade certificates, free-square forcing,
  and addressed-square realization. The active Figure 16 definitions are in
  `Figure16.lean`; exhaustive transcription checks are retained separately in
  the unimported `Figure16Audit.lean`.
- `Robinson/Reduction.lean` connects machine histories to the scaffold, and
  `Robinson/Final.lean` supplies the completed reduction certificate.

The independent second proof is isolated under `Kari/`:

- The files directly in `Kari/` formalize transducers, piecewise-affine
  dynamics, Beatty encodings, affine Turing-machine diagrams, and their Wang
  encodings.
- `Kari/Hooper/` formalizes Hooper's nested counter and bounded-search
  construction, including finite control, marker geometry, forward simulation,
  and the arbitrary-configuration mortality converse.
- `Kari/Final.lean` exports the second reduction certificate and its generic
  complexity consequences. `Kari.lean` imports the full development for
  separate checking, and the root `LeanWang` aggregate imports the completed
  endpoint.

The superseded exhaustive PairCover seam proof remains available as provenance
in the [last pre-cleanup commit](https://github.com/edemaine/lean-wang/tree/a8bcfd206a9816868d0a77bda96c46227313dad3).
Its main executable entry point was
[`PairCoverSeamPathSearch`](https://github.com/edemaine/lean-wang/blob/a8bcfd206a9816868d0a77bda96c46227313dad3/LeanWang/Robinson/Closed104/PairCoverSeamPathSearch.lean),
with finite audits in
[`PairCoverSeamPathBaseAudit`](https://github.com/edemaine/lean-wang/blob/a8bcfd206a9816868d0a77bda96c46227313dad3/LeanWang/Robinson/Closed104/PairCoverSeamPathBaseAudit.lean)
and committed component roots in
[`PairCoverSeamPathComponentCertificate`](https://github.com/edemaine/lean-wang/blob/a8bcfd206a9816868d0a77bda96c46227313dad3/LeanWang/Robinson/Closed104/PairCoverSeamPathComponentCertificate.lean).

## Build

```bash
lake build LeanWang.Final  # public theorems and the selected Robinson proof
lake build                 # root aggregate: check both completed proofs
lake build LeanWang.Kari   # complete Kari--Hooper aggregate only
```

Downstream projects should normally `import LeanWang.Final`. Use
`import LeanWang` only when the goal is to check both independent reduction
certificates.

All Lean source files are nonexecutable (`100644`). The source contains no
`sorry`, `admit`, or explicit `axiom` declarations. The large finite
certificates intentionally use `native_decide`, so Lean's axiom report includes
the corresponding generated code-evaluation axioms in addition to `propext`,
`Classical.choice`, and `Quot.sound`; it contains no `sorryAx` or other custom
project axiom.
