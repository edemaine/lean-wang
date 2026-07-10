# Wang Tiling Undecidability Formalization Plan

## Goal

Prove in Lean, using Mathlib's computability library, that both the encoded and
unencoded plane-tiling predicates for finite Wang tilesets are undecidable:

```lean
¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n))
¬ ComputablePred (fun T : TileSet => TilesPlane T)
```

The public conditional versions are already proved in `LeanWang.Final`. The
only remaining hypothesis is a concrete proof of `IsScaffold`.

## Chosen reduction

Use the Berger/Robinson fixed-corner construction from `cirm.pdf`, with the
intrinsically substitutive Ollinger/Robinson scaffold and Robinson's Section 7
free-line argument from `robinson.pdf`.

The reduction has three independent parts:

1. Undecidability of a seeded quarter-plane tiling problem by simulating one
   fixed universal machine.
2. Compactness, converting the infinite seeded quarter-plane tiling into
   finite fixed-corner squares of every size.
3. A scaffold that forces and realizes arbitrarily large fixed-corner payload
   squares inside a plane tiling.

## Completed machine side

The source-dependent machine compiler has been replaced by a fixed universal
argument.

1. `UniversalCode.universalCode` evaluates a supplied encoded
   `Nat.Partrec.Code` and input.
2. `UniversalTM0.code` translates this universal evaluator once through
   Mathlib's `ToPartrec`, TM2, TM1, and TM0 route.
3. `UniversalTM0.input c` writes `Nat.pair (encode c) 0` as the varying initial
   tape. Its construction is computable.
4. `TM0FoldedInput` proves that the parameterized initializer writes that word,
   rewinds to the origin, and enters the fixed TM0 simulation.
5. `UniversalFoldedReduction.program_haltsEmpty_iff` proves that the folded
   finite program halts exactly when `Nat.Partrec.Code.eval c 0` is defined.
6. `MachineTiles` and the scaffold reduction turn nonhalting into plane tiling.
7. Mathlib's `ComputablePred.halting_problem` yields both undecidability
   theorems.

There is no remaining source-uniform compiler, descriptor decoder, or generated
position-row obligation in the final theorem.

## Completed general tiling infrastructure

- Wang-tile and tileset encodings, finite rectangle search, and matching rules.
- Centered-box and square compactness for plane tilings.
- Fixed-corner square compactness for seeded quarter-plane tilings.
- Machine-history Wang tiles and the fixed-domino correctness theorem.
- The abstract `Scaffold` / `IsScaffold` reduction.
- A finite transcription of Figure 13 and Figure 16, including the corrected
  104 component triples in `figures/fig13-human.tsv`.
- Substitution-generated plane tilings for the corrected 104-symbol alphabet.
- Finite diagnostics showing that the old 92-tile edge transcription and the
  synthetic stable-edge relation cannot be the final scaffold relation.

## Remaining scaffold proof

The remaining theorem must construct a concrete `S : Scaffold` and prove
`IsScaffold S`. Keep this work independent of the machine reduction.

### 1. Recover the intended local matching relation

Use the corrected Figure 13 component table and Figure 16 substitution. Verify:

- every substituted `2 x 2` block is locally valid;
- substitution preserves and reflects horizontal and vertical compatibility;
- the concrete relation admits the intended 104 tile types and no spurious
  local configurations needed by the recognizability argument.

The current synthetic least closure is diagnostic only: its finite `4 x 4`
test admits well-behaved central blocks that are not substitution images.

### 2. Prove finite recognizability

Formalize Proposition 8 of `cirm.pdf` as a checked finite theorem:

- define the well-behaved central `2 x 2` predicate;
- enumerate legal `4 x 4` neighborhoods;
- prove each well-behaved center is the image of a unique parent tile and phase;
- lift the Boolean certificate to a proposition-level desubstitution theorem.

### 3. Obtain arbitrarily large free squares

Iterate desubstitution to recover the hierarchical square structure. Then use
Robinson's board/free-line argument to show that every plane scaffold tiling
contains arbitrarily large recognizable active squares with a distinguished
lower-left corner.

### 4. Prove backward realization

Construct scaffold tilings containing active-corner boxes of every finite size,
or equivalently finite layer patches that compactness assembles into the
required plane tiling. Show arbitrary payload tiles can be routed through the
active square and obstruction channels.

### 5. Package and finish

Bundle the forward and backward results as `IsScaffold S`, apply
`LeanWang.encoded_domino_problem_undecidable` and
`LeanWang.domino_problem_undecidable`, then run:

```bash
lake build
rg -n "sorry|admit|axiom" LeanWang
git diff --check
```

The final theorem should have no hypotheses and no source-dependent machine
infrastructure.
