# lean-wang

Lean formalization project for the undecidability of plane tiling by Wang tiles.

The proof plan is in [`plan.md`](plan.md). The current implementation starts with
the concrete definitions needed for the Berger/Robinson route:

- `LeanWang.Basic`: Wang tiles, plane and quarter-plane tilings, finite rectangle
  tilings, executable finite rectangle search, and the easy compactness
  restriction directions.
- `LeanWang.Compactness`: the proved centered-box compactness theorem
  `tilesPlane_iff_all_tileableBoxes`, plus the square compactness theorem
  `tilesPlane_iff_all_tileableSquares`.
- `LeanWang.Machine`: a small deterministic one-tape machine model for the
  Wang-tile simulation layer.
- `LeanWang.Theorems`: the main theorem surface and remaining proof obligations.

Current build:

```bash
lake build
```

The build succeeds. The remaining compactness `sorry` is:

- `tilesQuarterWithSeed_iff_all_fixedCornerSquares`

Additional `sorry`s in `LeanWang.Theorems` are roadmap placeholders for the
machine simulation, scaffold construction, and final undecidability reductions.
