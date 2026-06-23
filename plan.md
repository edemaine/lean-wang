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
- the fixed-domino reduction from the source-level folded finite-TM0 route plus
  the temporary finite-TM0-to-table backend bridge;
- the abstract scaffold reduction from any verified `IsScaffold S`;
- the encoded domino undecidability theorem from source-level folded-route
  obligations and a verified scaffold.
- a primitive-recursive finite Boolean search `TableProgram` generator remains
  available as supporting code, but the old bounded-fuel theorem route has been
  removed from the main theorem surface.
- a primitive-recursive translation from Mathlib unary `Nat.Partrec.Code` to
  Mathlib list-based `Turing.ToPartrec.Code`, with a concrete correctness
  theorem connecting Mathlib code evaluation to `PartrecToTM2` halting. This
  remains only the semantic entry point into Mathlib's machine translations;
  the obsolete direct TM2-to-table reduction surface has been removed.
- finite-control support wrappers for Mathlib's `PartrecToTM2` evaluator:
  the start label, finite reachable label set, stack names, stack alphabet, and
  finite statement-substate set, with list views and numeric codes for the
  stack names/symbols, plus an injective blank-or-stack-symbol tape alphabet
  code into `List.range 5`. The statement-substate list now also has finite
  `Nat`-valued control-state indices for the start, halt, and supported label
  statements, plus one-step/reachable label-closure lemmas for runs starting
  from `PartrecToTM2.init tc [0]`.
- the abandoned direct `PartrecToTM2` table-machine construction has been
  removed. The preferred machine-side proof now has one semantic route:
  Mathlib code, to `ToPartrec.Code`, through Mathlib's TM2-to-TM1-to-TM0
  translations, then into the local folded finite one-sided TM0 model.

The remaining construction obligations are explicit Lean interfaces:

```lean
structure TM0FoldedReduction.SourceObligations where
  program_computable :
    Computable (fun c : Nat.Partrec.Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c))
  correct : forall c : Nat.Partrec.Code,
    (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)).HaltsEmpty <->
      (Nat.Partrec.Code.eval c 0).Dom

def IsScaffold (S : Scaffold) : Prop :=
  forall (T : TileSet) (seed : WangTile),
    TilesPlane (combineWithScaffold S T seed) <->
      forall n : Nat, 0 < n -> TileableFixedCornerSquare T seed n
```

Mathematically, these obligations package computable reductions; the
implementation side may still use "compiler"/"compilation" when describing the
concrete construction of finite program data. In prose, "reduction" should be
the default word for the mathematical notion.

There is also a TM2/TM0 factoring of the same obligation. The repository now
provides a local natural-number encoding, `Denumerable` instance, and hence
`Primcodable` instance for Mathlib's `Turing.ToPartrec.Code`.
`NatPartrecToToPartrec.translate` is the computable translation from unary
`Nat.Partrec.Code` to the corresponding Mathlib TM2 evaluator code, and its
correctness is proved directly in `NatPartrecToToPartrec`.
The live route now factors through a finite one-sided TM0 reduction: first use
`TM0Route` to compose Mathlib's TM2-to-TM1 and TM1-to-TM0 reductions, then
reduce the resulting two-sided Mathlib TM0 machine/input to the local finite
one-sided TM0 model by folding the two tape directions into one tape. This is
implemented in the current code as concrete program construction, but the proof
should treat it as the mathematical reduction. The direct TM2-to-table
reduction surface should stay removed. The table-machine definitions remain
only because the current Wang-tile layer consumes `TableProgram`; they are fed
by the concrete compatibility bridge `PostProgram.toTableProgram` until that
layer is replaced by direct finite-TM0 tiles. This bridge starts only after the
source machine has already been reduced to finite one-sided TM0 data; it is not
a direct TM2-to-table reduction.
Together these pieces feed the fixed-domino, fixed-corner, encoded scaffolded
domino, and unencoded scaffolded domino theorem surfaces from the source-level
folded finite-TM0 factorization using the concrete source-code translation into
Mathlib's `PartrecToTM2` evaluator. The old code-to-table `TableCompiler`
surface and the generic theorem-level `TM0FiniteCompiler` interface have been
removed so the theorem statements do not look like a direct TM2-to-table route.
The started-TM2 bridge is a theorem in `TM0Route` rather than a separate
reduction structure.

The data-level compiler `PostProgram.toTableProgram` is now in place for the
current table-machine tile backend. A finite-TM0 `move` compiles to one
table row. A finite-TM0 `write` compiles to a write-and-move-right row followed
by finite return-left rows. Generated row targets and written symbols are proved
to lie in the compiled table supports. The table simulation is now proved both
ways at the halting level:

```lean
PostProgram.toTableProgram_toMachine_haltsEmpty_iff :
  P.toTableProgram.toMachine.HaltsEmpty <-> P.HaltsEmpty
```

`TM0Route` now also packages finite state support for the code-specific started
TM2 evaluator and for the translated TM1 and TM0 machines. It also has an
explicit finite alphabet list for the translated TM0 tape symbols, built from
the concrete four `PartrecToTM2` stacks and their finite stack alphabet rather
than relying on a global `Fintype` instance. The translated TM0 tape symbols now
also have injective numeric codes and a numeric symbol list for the eventual
`FiniteTM0Program`.

`PartrecToTM2SupportList` now provides executable list mirrors of Mathlib's
`trStmts₁`, `codeSupp'`, `contSupp`, and `codeSupp` finsets, with membership
equivalence to the current support sets. The TM0 route now has an executable
started-TM2 label list and uses this explicit recursive support list instead
of `Finset.toList` for downstream label enumeration; the resulting translated
TM0 label list, support list, numeric state list, and state code are
executable. This isolates the next computability step: prove or package
computability of the folded program compiler itself.

The old direct finite-program construction from this route data has been
removed because it was not the right semantic bridge: Mathlib TM0 has a
two-sided tape while the local finite TM0 model is one-sided. The remaining
`TM0FiniteCompiler` module now only keeps state-code and label-closure helpers
used by `TM0FoldedCompiler`. The preferred bridge is the folded construction:
one local tape cell stores the pair of Mathlib symbols at positions `-i-1` and
`i`, plus an origin marker, and the finite control stores which folded side is
active. This makes the two-sided-to-one-sided reduction explicit instead of
hiding it inside a table-machine construction. The semantic halting equivalence
for this folded program is now proved:

```lean
TM0FoldedCompiler.program_haltsEmpty_iff_tm0_eval_dom :
  (TM0FoldedCompiler.program tc).HaltsEmpty <->
    (Turing.TM0.eval
      (TM0Route.partrecStartedTM0Machine tc)
      TM0Route.partrecStartedTM0Input).Dom
```

The remaining blocker for the source-level folded route is computability of
`TM0FoldedCompiler.programData ∘ NatPartrecToToPartrec.translate`. The
support-list and numeric state-code path is now executable; the next step is to
remove or localize the file-wide noncomputable section in `TM0FoldedCompiler`
and prove the resulting source program-data map computable.
`TM0FoldedCompiler.programData` is a normalized form of `program` where the
constant initial rows are exposed definitionally, with
`TM0FoldedCompiler.programData_eq_program` relating it back to the semantic
`program`. The later TM0 count wrappers are also isolated:
`TM0Route.partrecStartedTM0StateCount_primrec_of_statementCount` reduces state
count computability to the remaining `partrecStartedTM0StatementCount`
computability target. `TM0Route` now also has a local `List Nat` sum
primitive-recursion helper for that statement-count proof. The next obstacle is
to add finite `Primcodable` encodings for the concrete TM2-to-TM1 labels and
their finite function payloads, so `partrecTM1LabelList` and the per-label
statement-length function can be treated as primitive recursive. The finite
function payloads and `TM2to1.StAct` are now encoded. The recursive concrete
started `TM2.Stmt` type is now encoded by valid preorder node lists: validity
is primitive recursive, valid lists parse completely, and the resulting
`Primcodable (PartrecStartedTM2StmtNode.Stmt tc)` instance is available. The
remaining encoding work on this branch is `TM2to1.Λ'`.
Separately, `TM0Route.tm2to1TrNormalSupportLength` is now the numeric mirror
of `tm1StmtSupportLength (Turing.TM2to1.trNormal stmt)`, avoiding a direct
dependency on encoded TM1 statements for this part of the count proof.
`TM0Route.partrecTM2SupportLength` now also mirrors
`tm2to1StmtSupportLength (partrecTM2 q)` directly on concrete
`PartrecToTM2` evaluator labels, and
`partrecStartedTM1LabelCount_eq_data` rewrites the started-TM1 label count to
this statement-free form. The label-level summand is now proved primitive
recursive by a small code-level classifier,
`TM0Route.partrecTM2SupportLength_primrec`. The next count step is to prove the
executable evaluator label list primitive recursive. Conditional bridges are
now in place:
`partrecStartedTM2LabelCount_primrec_of_labelList`,
`partrecStartedTM1LabelCountData_primrec_of_labelList`, and
`partrecStartedTM1LabelCount_primrec_of_labelList` reduce the started-TM1 label
count to that single remaining list-computability fact.
`PartrecToTM2SupportList` now imports the concrete evaluator encodings and has
top-level bridges `codeSuppList_primrec_of_parts` and
`labelList_primrec_of_codeSuppList`; the remaining support-list work is the
mutual primitive-recursion proof for `codeSuppList'` and `contSuppList`.
It also has weighted numeric mirrors
`trStmtsWeight`, `codeSuppWeight'`, `contSuppWeight`, `codeSuppWeight`, and
`labelWeight`, each proved equal to summing a weight over the corresponding
executable support list. `TM0Route.partrecStartedTM1LabelCountWeightData` now
rewrites the started-TM1 label count through `labelCount` plus
`labelWeight partrecTM2SupportLength`, so the count path can proceed through
numeric support mirrors without first proving the full support list primitive
recursive.

There is now also a lighter source-level folded route in
`TM0FoldedReduction`. It records the exact obligations needed for the final
undecidability reduction from `Nat.Partrec.Code`:

```lean
structure TM0FoldedReduction.SourceObligations where
  program_computable :
    Computable (fun c : Nat.Partrec.Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c))
  correct : forall c : Nat.Partrec.Code,
    (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)).HaltsEmpty <->
      (Nat.Partrec.Code.eval c 0).Dom
```

The semantic half follows from the already-proved folded correctness theorem in
`TM0FoldedCompiler` together with the `NatPartrecToToPartrec.translate`
correctness chain. Keeping it as an explicit source-level obligation avoids
forcing the lightweight reduction file to import the very large folded semantic
proof.  The remaining computational target can therefore be narrowed to
computability of `TM0FoldedCompiler.program ∘ NatPartrecToToPartrec.translate`,
rather than computability on arbitrary `Turing.ToPartrec.Code`.

Next implementation targets:

1. Prove source-level computability of the folded finite-TM0 reduction:

   ```lean
   Computable (fun c : Nat.Partrec.Code =>
     TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c))
   ```

   This can use Mathlib's existing recursion theorem for `Nat.Partrec.Code`
   instead of first proving a general recursion theorem for
   `Turing.ToPartrec.Code`.
2. Optionally strengthen the result to computability on all
   `Turing.ToPartrec.Code` for a reusable folded-route corollary. This should
   still feed the source-level theorem through `Obligations.toSource`, not
   reintroduce a generic table-facing compiler interface.
3. Add the actual Ollinger/Robinson scaffold tileset and prove `IsScaffold`.
4. Specialize the concrete folded-route/scaffold corollaries, in particular
   `encoded_domino_problem_undecidable_of_scaffold_source` and
   `domino_problem_undecidable_of_scaffold_source`, to those concrete
   instances to recover the unconditional encoded and unencoded domino theorems.
5. Optionally replace the current table-machine tiles by direct finite-TM0
   tiles. The TM0 instruction set is already close to the Wang-tile space-time
   simulation, so this should remove both the `PostProgram.toTableProgram`
   detour from the final theorem and the need for `TableProgram` as a live
   backend. Until then, `TableProgram` is still used by the existing tile code,
   while `PostProgram.toTableProgram` is a verified compatibility bridge rather
   than part of the source TM2-to-TM0 reduction.

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
