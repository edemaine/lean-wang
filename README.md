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
- `LeanWang.ToPartrecEncoding`: natural-number encoding support for Mathlib's
  `Turing.ToPartrec.Code`.
- `LeanWang.NatPartrecToToPartrec`: a primitive-recursive translation from
  Mathlib unary `Nat.Partrec.Code` to Mathlib list-based
  `Turing.ToPartrec.Code`, with correctness for the TM2 evaluator.
- `LeanWang.Theorems`: the main theorem surface and remaining proof obligations.

Current build:

```bash
lake build
```

The build succeeds.

The main theorem surface is currently conditional on two construction
interfaces:

- `TM2TableCompiler`: reduce Mathlib's concrete `PartrecToTM2` evaluator
  configurations to finite table-machine data with the right halting behavior.
  The Mathlib-code-to-TM2 reduction is already proved. The identifier names
  emphasize the produced program data; their role in the theorem is the
  computable reduction, implemented by compilation to finite machine
  descriptions.
- `IsScaffold`: prove a concrete scaffold converts fixed-corner finite-square
  instances to ordinary plane tiling.

The fixed-domino, fixed-corner, scaffold, final domino, and encoded domino
undecidability reductions are now proved from those construction interfaces.
There are also more general theorem variants from `TableCompiler`,
`FuelTableCompiler`, and `PrimrecSearchTableCompiler`.
