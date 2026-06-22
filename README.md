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
- `LeanWang.TM0FiniteCompiler`: finite one-sided TM0 program data extracted
  from `TM0Route`, currently including numeric symbol/state headers and support
  lemmas for the blank and start fields, plus enumeration of supported Mathlib
  TM0 transitions into finite-TM0 rows.
- `LeanWang.Theorems`: the main theorem surface and remaining proof obligations.

Current build:

```bash
lake build
```

The build succeeds.

The main theorem surface is currently conditional on two construction
interfaces, plus the scaffold construction:

- `TM0FiniteCompiler`: the preferred machine-side route. It reduces Mathlib's
  code-specific started TM0 evaluator to finite one-sided TM0 program data.
- `FiniteTM0TableReduction`: a legacy bridge from finite one-sided TM0 programs
  to the existing table-machine Wang-tile layer. This should be replaced by
  direct finite-TM0 tiles later.
- `IsScaffold`: prove a concrete scaffold converts fixed-corner finite-square
  instances to ordinary plane tiling.

The abandoned direct `PartrecToTM2`/TM2-to-table reduction has been removed.
TM2 remains only as Mathlib's intermediate evaluator on the way to TM0.

The fixed-domino, fixed-corner, scaffold, final domino, and encoded domino
undecidability reductions are now proved from those construction interfaces.
There are also more general theorem variants from `TableCompiler`,
`FuelTableCompiler`, `PrimrecSearchTableCompiler`, and `TM0FiniteCompiler`.
