# lean-wang

Lean formalization project for the undecidability of plane tiling by Wang tiles.

The proof plan is in [`plan.md`](plan.md). The current implementation starts with
the concrete definitions needed for the Berger/Robinson route:

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
  more closely than the older table model. The file also contains the legacy
  data-level compiler to `TableProgram` used by the temporary bridge to the
  existing Wang-tile layer.
- `LeanWang.ToPartrecEncoding`: natural-number encoding support for Mathlib's
  `Turing.ToPartrec.Code`.
- `LeanWang.NatPartrecToToPartrec`: a primitive-recursive translation from
  Mathlib unary `Nat.Partrec.Code` to Mathlib list-based
  `Turing.ToPartrec.Code`, with correctness for the TM2 evaluator.
- `LeanWang.PartrecToTM2Support`: finite reachable-label support facts for
  Mathlib's concrete `PartrecToTM2` evaluator.
- `LeanWang.PartrecToTM2Table`: finite `TableProgram` header data and the
  one-tape configuration representation for the eventual `PartrecToTM2`
  table-machine reduction, including intermediate statement substates and
  stationary row families and preservation lemmas for `load`, `branch`,
  `goto`, and `halt` microsteps, plus representation lemmas for stack
  push/pop updates, an explicit boundary symbol, reserved auxiliary states for
  `peek`, and complete bounded `peek` row families with symbol/state
  well-formedness lemmas. It now assembles the implemented statement-row
  fragment for all supported substates; finite auxiliary states are also
  reserved for the remaining unbounded stack-shifting rows for `push` and
  `pop`, with bounded travel rows to the selected stack column, generic
  carry-write rows, and stride rows for the shift loop.
- `LeanWang.TM0Route`: a Mathlib TM0 route that wraps the code-dependent
  `PartrecToTM2` start label as the default TM2 label, composes Mathlib's
  TM2-to-TM1 and TM1-to-TM0 translations, and proves the composed TM0 evaluator
  has the same domain as the corresponding started TM2 evaluator. It also
  packages finite state support for the started TM2, translated TM1, and
  translated TM0 machines, plus an explicit finite alphabet list for the
  translated TM0 tape symbols and injective numeric codes for those symbols.
- `LeanWang.TM0FiniteCompiler`: finite one-sided TM0 program data extracted
  from `TM0Route`, currently including numeric symbol/state headers and support
  lemmas for the blank and start fields.
- `LeanWang.Theorems`: the main theorem surface and remaining proof obligations.

Current build:

```bash
lake build
```

The build succeeds.

The main theorem surface is currently conditional on two construction
interfaces:

- `TM0FiniteCompiler`: the preferred machine-side route. It reduces Mathlib's
  code-specific started TM0 evaluator to finite one-sided TM0 program data.
- `FiniteTM0TableReduction`: a legacy bridge from finite one-sided TM0 programs
  to the existing table-machine Wang-tile layer. This should be replaced by
  direct finite-TM0 tiles later.
- `startedTM2ToPartrecReduction`: the proved semantic bridge between the
  code-specific started TM2 evaluator used by `TM0Route` and Mathlib's original
  `PartrecToTM2.init` evaluator.
- `TM2TableCompiler`: the older direct TM2-to-table reduction interface remains
  available, and `TM0FiniteCompiler` can feed it through `toTM2TableCompiler`
  using a `FiniteTM0TableReduction`.
- `IsScaffold`: prove a concrete scaffold converts fixed-corner finite-square
  instances to ordinary plane tiling.

The fixed-domino, fixed-corner, scaffold, final domino, and encoded domino
undecidability reductions are now proved from those construction interfaces.
There are also more general theorem variants from `TableCompiler`,
`FuelTableCompiler`, `PrimrecSearchTableCompiler`, and `TM0FiniteCompiler`.
