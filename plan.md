# Plan for Formalizing Wang Tile Undecidability in Lean

## Recommendation

Use the Berger/Robinson proof route as presented in [Jeandel and Vanier's notes](cirm.pdf), via the Ollinger/Robinson intrinsically substitutive scaffold.

The proposed proof pipeline is:

1. Prove the fixed domino problem undecidable by encoding computation in a quarter-plane.
2. Prove a general scaffold reduction: if a finite Wang tileset produces arbitrarily large locally recognizable free squares, then fixed-corner square tiling reduces to ordinary plane tiling.
3. Instantiate the scaffold with the Ollinger/Robinson substitutive tileset from the paper.

This looks easiest to formalize because it separates the computability content from the geometric forcing construction. The other proof families have larger hidden dependencies:

- Kari's proof is short in the paper only after assuming Hooper's immortality theorem, whose formalization would likely dominate the project.
- The Aanderaa-Lewis proof needs sofic shifts, distance shifts, and p-adic/Toeplitz machinery.
- The Durand-Romashchenko-Shen fixed-point proof aligns philosophically with Mathlib computability, but self-simulating macrotiles and runtime bookkeeping look significantly heavier.

## Mathlib Starting Point

Use Mathlib's computability layer for the undecidability source:

- `Mathlib.Computability.Halting` provides the noncomputability of the halting predicate for `Nat.Partrec.Code.eval`.
- `Mathlib.Computability.Partrec` provides `Partrec`, `Computable`, and `ComputablePred` over `Primcodable` types.
- `Mathlib.Computability.Encoding` provides finite encodings useful for computability-facing syntax and data.

The final theorem should be stated algorithmically, for example as a noncomputability result:

```lean
theorem domino_not_computable :
  ¬ ComputablePred (fun T : TileSet => TilesPlane T)
```

or an equivalent encoded-list statement over `Nat`.

## Implementation Plan

## Current Lean State

The repository now has a build-clean conditional proof skeleton with no `sorry`
or `axiom` in `LeanWang`.

Completed proof layers:

- concrete Wang tiles, finite rectangles, plane and quarter-plane tiling notions;
- compactness and fixed-corner square compactness variants;
- the concrete one-tape `Machine` and finite `TableProgram` models;
- the machine-to-Wang fixed-domino construction;
- computable table-tile data decoding, including the initial-row and normal-row
  tile membership bridges;
- the fixed-domino reduction from any verified `TableCompiler`;
- the abstract scaffold reduction from any verified `IsScaffold S`;
- the encoded domino undecidability theorem from a verified reduction to finite
  machine data and verified scaffold.
- a primitive-recursive finite Boolean search `TableProgram` generator, with
  a recursive transition-table view, full list-level correctness
  (`HaltsEmpty` iff the input list contains `true`), a primitive-recursive
  bounded fuel-prefix generator, and code-indexed bounded evaluator prefix
  programs whose existential bounded-halting family is equivalent to Mathlib
  code evaluation being defined.
- the same bounded evaluator prefix family has been pushed through the
  fixed-domino machine-to-Wang construction: for a code `c`, all bounded prefix
  fixed-domino instances tile exactly when `Nat.Partrec.Code.eval c 0` is
  undefined, and this quantified fixed-domino family is undecidable.
- via compactness, the bounded prefix fixed-domino family has also been pushed
  to quantified fixed-corner square tilings: for all bounds and all positive
  square sizes, tileability is equivalent to the same Mathlib nonhalting
  predicate, and this quantified square-family predicate is undecidable.
- assuming any verified `IsScaffold S`, the bounded prefix family has also been
  pushed through the abstract scaffold to ordinary plane tiling: all scaffolded
  bounded-prefix plane instances tile exactly when the Mathlib code does not
  halt, and this quantified plane-tiling family is undecidable.
- the scaffolded bounded-prefix family also has a canonical natural-number
  encoding, with correctness and undecidability for the corresponding quantified
  encoded plane-tiling predicate.
- a primitive-recursive translation from Mathlib unary `Nat.Partrec.Code` to
  Mathlib list-based `Turing.ToPartrec.Code`, with a concrete
  `ToPartrecTM2Reduction` witness connecting Mathlib code evaluation to
  `PartrecToTM2` halting. The TM2 theorem surfaces now have variants using this
  concrete reduction, so they no longer require passing the code-to-TM2
  reduction as an explicit parameter.
- finite-control support wrappers for Mathlib's `PartrecToTM2` evaluator:
  the start label, finite reachable label set, stack names, stack alphabet, and
  finite statement-substate set, with list views and numeric codes for the
  stack names/symbols, plus an injective blank-or-stack-symbol tape alphabet
  code into `List.range 5`. The statement-substate list now also has finite
  `Nat`-valued control-state indices for the start, halt, and supported label
  statements, plus one-step/reachable label-closure lemmas for runs starting
  from `PartrecToTM2.init tc [0]`.

The remaining construction obligations are explicit Lean interfaces:

```lean
structure TableCompiler where
  compile : Code -> TableProgram
  compile_computable : Computable compile
  correct : forall c : Code,
    Machine.HaltsEmpty (compile c).toMachine <-> (Nat.Partrec.Code.eval c 0).Dom

structure FuelTableCompiler where
  compile : Code -> TableProgram
  compile_computable : Computable compile
  correct : forall c : Code,
    Machine.HaltsEmpty (compile c).toMachine <-> FuelMachine.Halts (codeEvalnHalts c 0)

structure PrimrecSearchTableCompiler where
  compile : {α : Type} -> [Primcodable α] -> (α -> Nat -> Bool) -> α -> TableProgram
  compile_computable : ...
  correct : forall {α : Type} [Primcodable α] (P : α -> Nat -> Bool) (a : α),
    Machine.HaltsEmpty (compile P a).toMachine <-> FuelMachine.Halts (P a)

def IsScaffold (S : Scaffold) : Prop :=
  forall (T : TileSet) (seed : WangTile),
    TilesPlane (combineWithScaffold S T seed) <->
      forall n : Nat, 0 < n -> TileableFixedCornerSquare T seed n
```

The names below keep `Compiler` because the maps produce finite program data,
but the mathematical notion they package is a computable reduction. The prose
therefore says reduction first, and mentions compilation when discussing the
implementation as finite machine data.

`FuelTableCompiler.toTableCompiler` already turns the smaller fuel-search
reduction obligation into a `TableCompiler`, using the proved
equivalence between `codeEvalnHalts` and `Nat.Partrec.Code.eval`.
`PrimrecSearchTableCompiler.toFuelTableCompiler` further factors this obligation
through a generic unbounded search reduction for primitive-recursive Boolean
predicate families, implemented by compilation to finite machine data. The
fixed-domino, fixed-corner, encoded scaffolded domino, and unencoded scaffolded
domino theorem surfaces now have direct corollaries from
`PrimrecSearchTableCompiler`.

There is also a TM2 factoring of the same obligation. The repository now
provides a local natural-number encoding, `Denumerable` instance, and hence
`Primcodable` instance for Mathlib's `Turing.ToPartrec.Code`.
`ToPartrecTM2Reduction` records a computable translation from unary
`Nat.Partrec.Code` to the corresponding Mathlib TM2 evaluator code, and
this translation is now concretely proved in `NatPartrecToToPartrec`.
`TM2TableCompiler` remains the finite-machine reduction obligation: it reduces
those TM2 evaluator configurations to `TableProgram`. Together they produce a
`TableCompiler`, and the fixed-domino, fixed-corner, encoded scaffolded domino,
and unencoded scaffolded domino theorem surfaces now have direct corollaries
from this TM2 factorization using the concrete code-to-TM2 reduction.

Next implementation targets:

1. Build a concrete `TM2TableCompiler`, by reducing Mathlib's
   `PartrecToTM2` stack-machine evaluator configurations to `TableProgram`.
   Mathlib already provides the finite statement support
   `Turing.PartrecToTM2.codeSupp` and correctness theorem
   `Turing.PartrecToTM2.tr_eval`; the remaining reduction work is representing
   the TM2 stacks, labels, and step relation in the project's one-tape
   `TableProgram` model.
2. Add the actual Ollinger/Robinson scaffold tileset and prove `IsScaffold`.
3. Specialize
   `encoded_domino_problem_undecidable_of_scaffold_tm2Reduction` to those two
   concrete instances to recover the unconditional encoded domino theorem.

### 1. Define Wang Tiles

Use a concrete computable representation:

```lean
structure WangTile where
  n s e w : Nat

abbrev TileSet := List WangTile
```

Then define:

- `ValidPlaneTiling T`
- `TilesPlane T`
- finite square tilings
- fixed-corner square tilings
- quarter-plane tilings with a fixed seed tile

Keep the first version concrete and computability-friendly. Generalizing to finite color types can wait.

### 2. Prove Finite Checking Is Computable

Show that validity of an `m x n` rectangle assignment is decidable and computable. This gives the infrastructure needed for reductions and compactness statements.

Useful finite predicates:

- a tile belongs to a `TileSet`
- adjacent tiles match horizontally
- adjacent tiles match vertically
- an array/list/function on `Fin m x Fin n` is a valid rectangle tiling
- the lower-left tile is a prescribed tile

### 3. Formalize Compactness

Prove the finite-to-infinite compactness principle:

```lean
TilesPlane T ↔ ∀ n, TileableSquare T n
```

Also prove the variants needed later:

- quarter-plane compactness
- fixed-corner square compactness
- arbitrary-large fixed-corner square tilings iff fixed-corner quarter-plane tiling

This should be finite-alphabet diagonal compactness. A tree of finite square tilings plus an infinite path argument is likely the cleanest route.

### 4. Fixed Domino Problem

Formalize the paper's Figure 10 construction:

- rows are instantaneous descriptions,
- vertical adjacency enforces one computation step,
- horizontal adjacency enforces row well-formedness,
- the seed tile initializes the empty input computation at the quarter-plane corner,
- halting-state tiles are omitted.

Target theorem:

```lean
TilesQuarterWithSeed (tmTiles M) seed ↔ ¬ Halts M
```

This should reduce Mathlib's halting theorem to fixed domino undecidability.

The machine-to-Wang-tile correspondence is expected to be straightforward. If Mathlib's Turing-machine API is awkward for row encodings, define a small one-tape or register-machine model tailored to the tiling construction, and connect it to `Nat.Partrec.Code` by a computable simulation. The user can help with this bridge as needed.

### 5. Abstract Scaffold Reduction

Before formalizing the concrete Ollinger tileset, prove an abstract theorem parameterized by a scaffold tileset `S`.

Assume `S` has:

- arbitrarily large locally recognizable squares in every global tiling,
- a locally recognizable free subsquare inside each scaffold square,
- local signals identifying the usable rows and columns,
- a recognizable lower-left corner where the fixed tile is forced.

Then define `combine S T t`, the superimposed tileset that places a copy of `T` into each free subsquare and forces `t` at the lower-left corner.

Prove:

```lean
TilesPlane (combine S T t) ↔
  ∀ n, TileableFixedCornerSquare T t n
```

This is the formal core of Theorem 10 in the paper.

### 6. Instantiate the Scaffold

Instantiate the abstract scaffold theorem using the Ollinger/Robinson tileset from the paper.

For finite local verification, avoid hand-proving hundreds of color matches. Instead:

- encode the finite tileset as Lean data,
- define the finite local predicates,
- use `native_decide` or reflection-style lemmas for exhaustive checks,
- keep a small number of human-readable lemmas explaining what the verified checks imply.

The goal is to make the large finite verification auditable without turning the proof into manual casework.

### 7. Final Undecidability Theorem

Compose:

1. Mathlib halting undecidability.
2. Computable reduction from halting/nonhalting to fixed domino.
3. Compactness equivalence for fixed-corner square tilings.
4. Abstract scaffold reduction.
5. Concrete scaffold instantiation.

Final target:

```lean
theorem domino_problem_undecidable :
  ¬ ComputablePred (fun T : TileSet => TilesPlane T)
```

or the corresponding version over encoded natural-number inputs.

## Milestones

1. Basic Wang tile definitions and finite rectangle checking.
2. Plane/quarter-plane compactness.
3. Fixed domino theorem from halting.
4. Abstract scaffold reduction.
5. Concrete Ollinger/Robinson scaffold data and finite verification.
6. Final noncomputability theorem.

## Main Risks

The largest risk is not the machine-to-Wang-tile encoding itself, which should be manageable, but choosing the right reduction bridge from Mathlib's computability theorem to the machine model used in the tiling construction. That bridge is implemented by compiling codes to finite machine data, so both terms remain useful.

The second largest risk is the concrete scaffold verification. This can be controlled by isolating it behind an abstract scaffold interface and using mechanical finite checks.
