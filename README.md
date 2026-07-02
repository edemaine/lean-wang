# lean-wang

Lean formalization project for the undecidability of plane tiling by Wang tiles.

The proof plan is in [`plan.md`](plan.md). The current implementation starts with
the concrete definitions needed for the Berger/Robinson route:

Primary source PDFs used by the proof plan are checked in as [`cirm.pdf`](cirm.pdf)
and [`robinson.pdf`](robinson.pdf), with provenance notes in [`cirm.txt`](cirm.txt)
and [`robinson.txt`](robinson.txt).

- `LeanWang.Basic`: Wang tiles, plane and quarter-plane tilings, finite rectangle
  tilings, executable finite rectangle search, canonical natural-number
  encoding/decoding for finite tilesets, and the easy compactness restriction
  directions.
- `LeanWang.Compactness`: the proved centered-box compactness theorem
  `tilesPlane_iff_all_tileableBoxes`, plus the square compactness theorem
  `tilesPlane_iff_all_tileableSquares` and seeded quarter-plane compactness
  `tilesQuarterWithSeed_iff_all_fixedCornerSquares`.
- `LeanWang.Machine`: a small deterministic one-sided tape machine model with
  well-formed finite supports for the Wang-tile simulation layer.
- `LeanWang.MachineTiles`: finite local-history Wang-tile data generated from a
  concrete machine.
- `LeanWang.PostMachine`: the finite one-sided TM0 program model. The original
  Post-style names are still present, but the preferred public terminology is
  `FiniteTM0Program`: transitions either move or write, matching Mathlib TM0
  more closely than the older table model. The file also contains the temporary
  finite-TM0-to-`TableProgram` bridge used only to feed the existing Wang-tile
  layer.
- `LeanWang.ToPartrecEncoding`: natural-number encoding support for Mathlib's
  `Turing.ToPartrec.Code`.
- `LeanWang.NatPartrecToToPartrec`: a primitive-recursive translation from
  Mathlib unary `Nat.Partrec.Code` to Mathlib list-based
  `Turing.ToPartrec.Code`, with correctness for the TM2 evaluator.
- `LeanWang.PartrecToTM2Support`: finite reachable-label support facts for
  Mathlib's concrete `PartrecToTM2` evaluator.
- `LeanWang.PartrecToTM2SupportList`: executable list mirrors of Mathlib's
  `PartrecToTM2` support finsets, with membership equivalence to the current
  finite support sets. The TM0 route uses this executable list for its concrete
  downstream label and state enumeration.
- `LeanWang.TM0Route`: a Mathlib TM0 route that wraps the code-dependent
  `PartrecToTM2` start label as the default TM2 label, composes Mathlib's
  TM2-to-TM1 and TM1-to-TM0 translations, and proves the composed TM0 evaluator
  has the same domain as the corresponding started TM2 evaluator. It also
  packages finite state support for the started TM2, translated TM1, and
  translated TM0 machines, plus an explicit finite alphabet list for the
  translated TM0 tape symbols and injective numeric codes for those symbols.
- `LeanWang.TM0FiniteCompiler`: shared helper lemmas for the folded TM0
  reduction, including numeric state codes and label-closure facts for
  supported Mathlib TM0 transitions.
- `LeanWang.TM0FoldedProgram` and `LeanWang.TM0FoldedCompiler`: the current
  finite one-sided TM0 reduction. The folded program stores the two sides of
  Mathlib's TM0 tape in one local tape cell and proves the semantic halting
  equivalence.
- `LeanWang.Theorems`: generic scaffold and machine-tiling theorem surfaces.
- `LeanWang.Final`: the current top-level undecidability theorem surface,
  conditional on the two remaining construction interfaces bundled as
  `FinalReductionInputs`.

Current build:

```bash
lake build
```

The build succeeds.

The main theorem surface in `LeanWang.Final` is currently conditional on two
construction interfaces:

- `TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec`: the
  source-uniform generated position-code row primitive-recursion proof for the
  folded TM0 reduction.
- `TM0FoldedReduction.L2C1OriginZeroCheckedStacks`: the checked finite
  origin-zero stack certificate for the first audited L2 candidate.
- `TM0FoldedReduction.Figure13PositiveBoardLevelChecked`: exact positive
  Robinson board-level raw Figure 13 finite checks. This is the proof-facing
  scaffold surface; the over-strong Figure 16 source/raw-boundary diagnostic has
  no adjacent two-cell witnesses in the current transcription.

There is no direct `PartrecToTM2`/TM2-to-table reduction in the current route.
TM2 remains only as Mathlib's intermediate evaluator on the way to TM0. The
`TableProgram` model is still live because the current Wang-tile construction is
typed against it.

The fixed-domino, fixed-corner, scaffold, final domino, and encoded domino
undecidability reductions are now proved from the TM0 construction interfaces.
