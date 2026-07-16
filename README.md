# lean-wang

Lean formalization of the undecidability of tiling the plane with Wang tiles.

The proof follows the Berger/Robinson fixed-corner reduction described in
[`cirm.pdf`](cirm.pdf), using Robinson's scaffold argument from
[`robinson.pdf`](robinson.pdf). Source provenance is recorded in
[`cirm.txt`](cirm.txt) and [`robinson.txt`](robinson.txt); the current proof
plan is in [`plan.md`](plan.md).

## Proof structure

The machine side is complete. It uses one fixed universal Mathlib TM0 machine:

```text
Nat.Partrec.Code c
  -> encode c on the initial tape of one fixed universal TM0 machine
  -> simulate it by one fixed folded one-sided machine
  -> apply the generic finite-input Wang history construction
  -> combine with any certified Robinson scaffold
```

Only the finite initial tape depends on `c`; the machine control and simulation
rows are fixed. This avoids the obsolete source-dependent compiler/decoder
route entirely. The generated initializer, position-code compiler, and their
correctness modules have been removed from the repository; the retained proof
uses the generic machine-to-Wang theorem directly.

The public theorem surface is [`LeanWang.Final`](LeanWang/Final.lean):

```lean
LeanWang.encoded_domino_problem_undecidable
LeanWang.domino_problem_undecidable
```

Both theorems take a `Scaffold` and a proof of `IsScaffold`. Instantiating this
last hypothesis with the concrete Ollinger/Robinson tiles is the remaining
proof task.

## Main modules

- `LeanWang.Basic` defines Wang tiles, finite tilesets, tilings, rectangles,
  and natural-number encodings.
- `LeanWang.Compactness` proves compactness for centered boxes, squares, and
  seeded quarter-plane tilings.
- `LeanWang.MachineInputTiles` supplies the reusable position and row colors
  used to force a finite bottom row.
- `LeanWang.UniversalCode` defines the universal partial function, and
  `LeanWang.UniversalTM0Semantic` uses Mathlib's completeness theorem to choose
  one evaluator code directly, carries its finite supports through TM2, TM1,
  and TM0, and places the source code on its initial tape.
- `LeanWang.UniversalTM0Folded` defines the paired coordinates for the
  two-sided TM0 tape. `LeanWang.UniversalTM0Machine` simulates each TM0 move in
  one target step and each write in two, and proves exact halting equivalence.
- `LeanWang.UniversalTM0MachineData` computes the input-dependent bottom-row
  tiles and seed; all normal history tiles are fixed constants.
- `LeanWang.UniversalTM0Reduction` proves the fixed-corner and plane-tiling
  reductions and derives undecidability from Mathlib's halting problem.
- `LeanWang.OllingerRobinsonScaffold` defines the abstract scaffold certificate.
- `LeanWang.OllingerRobinson104*` contains the corrected 104-component
  Figure 13/Figure 16 transcription, substitution boundary certificates, and
  the successful finite Proposition 8 recognizability check.

## Build

```bash
lake build
```

All Lean source files are nonexecutable (`100644`). The checked proof contains
no `sorry`, `admit`, or declared axioms.
