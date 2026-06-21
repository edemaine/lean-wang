# lean-wang

Lean formalization project for the undecidability of plane tiling by Wang tiles.

The proof plan is in [`plan.md`](plan.md). The current implementation starts with
the concrete definitions needed for the Berger/Robinson route:

- `LeanWang.Basic`: Wang tiles, plane and quarter-plane tilings, finite rectangle
  tilings, executable finite rectangle search, and the easy compactness
  restriction directions.
- `LeanWang.Machine`: a small deterministic one-tape machine model for the
  Wang-tile simulation layer.

Current build:

```bash
lake build
```

The build succeeds with two intentional `sorry`s, both for the hard compactness
directions:

- `tilesPlane_iff_all_tileableSquares`
- `tilesQuarterWithSeed_iff_all_fixedCornerSquares`
