# Plan for Formalizing Wang Tile Undecidability in Lean

## Recommendation

Use the Berger/Robinson proof route as presented in [Jeandel and Vanier's
notes](cirm.pdf), via the Ollinger/Robinson intrinsically substitutive scaffold.
Robinson's original paper [Undecidability and Nonperiodicity for Tilings of the
Plane](robinson.pdf) is the primary source for the board/free-line Section 7
argument.

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
- the concrete one-tape `Machine` and finite `TableProgram` models, still used
  by the current Wang-tile backend, not by the source-level reduction;
- the machine-to-Wang fixed-domino construction;
- computable table-tile data decoding, including the initial-row and normal-row
  tile membership bridges;
- the fixed-domino reduction from the source-level folded finite-TM0 route plus
  the temporary finite-TM0-to-table backend bridge;
- the abstract scaffold reduction from any verified `IsScaffold S`;
- the encoded domino undecidability theorem from source-level folded-route
  obligations and a verified scaffold.
- the old bounded-fuel theorem route and its primitive-recursive finite Boolean
  search `TableProgram` generator have been removed from the codebase.
- a primitive-recursive translation from Mathlib unary `Nat.Partrec.Code` to
  Mathlib list-based `Turing.ToPartrec.Code`, with a concrete correctness
  theorem connecting Mathlib code evaluation to `PartrecToTM2` halting. This
  remains only the semantic entry point into Mathlib's machine translations;
  it does not feed a table-machine construction directly.
- finite-control support wrappers for Mathlib's `PartrecToTM2` evaluator:
  the start label, finite reachable label set, stack names, stack alphabet, and
  finite statement-substate set, with list views and numeric codes for the
  stack names/symbols, plus an injective blank-or-stack-symbol tape alphabet
  code into `List.range 5`. The statement-substate list now also has finite
  `Nat`-valued control-state indices for the start, halt, and supported label
  statements, plus one-step/reachable label-closure lemmas for runs starting
  from `PartrecToTM2.init tc [0]`.
- any direct `PartrecToTM2` table-machine construction is outside the current
  route and should remain deleted. The preferred machine-side proof now has one
  semantic route:
  Mathlib code, to `ToPartrec.Code`, through Mathlib's TM2-to-TM1-to-TM0
  translations, then into the local folded finite one-sided TM0 model.

The remaining construction obligations are explicit Lean interfaces:

```lean
structure TM0FoldedReduction.PositionSourceObligations where
  program_computable :
    Computable (fun c : Nat.Partrec.Code =>
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c))
  correct : forall c : Nat.Partrec.Code,
    (TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)).HaltsEmpty <->
      (Nat.Partrec.Code.eval c 0).Dom

def IsScaffold (S : Scaffold) : Prop :=
  forall (T : TileSet) (seed : WangTile),
    TilesPlane (combineWithScaffold S T seed) <->
      forall n : Nat, 0 < n -> TileableFixedCornerSquare T seed n
```

Mathematically, these obligations package computable reductions. In prose,
"reduction" should be the default word for the mathematical notion; "program
construction" is only for the concrete finite data generation inside that
reduction.

The only live machine-side source route now factors through Mathlib's TM2,
TM1, and TM0 translations before entering the local folded one-sided TM0 model.
The repository provides a local natural-number encoding, `Denumerable`
instance, and hence `Primcodable` instance for Mathlib's
`Turing.ToPartrec.Code`.
`NatPartrecToToPartrec.translate` is the computable translation from unary
`Nat.Partrec.Code` to the corresponding Mathlib TM2 evaluator code, and its
correctness is proved directly in `NatPartrecToToPartrec`.
The live route now factors through a finite one-sided TM0 reduction: first use
`TM0Route` to compose Mathlib's TM2-to-TM1 and TM1-to-TM0 reductions, then
reduce the resulting two-sided Mathlib TM0 machine/input to the local finite
one-sided TM0 model by folding the two tape directions into one tape. This is
implemented in the current code as concrete program construction, but the proof
should treat it as the mathematical reduction. There is no direct TM2-to-table
reduction in the live route, and one should not be reintroduced. The
table-machine definitions remain live only because the current Wang-tile layer
consumes `TableProgram`; they are fed by the concrete compatibility bridge
`PostProgram.toTableProgram` until that layer is replaced by direct finite-TM0
tiles. This bridge starts only after the source machine has already been
reduced to finite one-sided TM0 data, so it is not a direct TM2-to-table
reduction.
Together these pieces feed the fixed-domino, fixed-corner, encoded scaffolded
domino, and unencoded scaffolded domino theorem surfaces from the source-level
folded finite-TM0 factorization using the concrete source-code translation into
Mathlib's `PartrecToTM2` evaluator. The theorem statements are phrased through
the folded finite-TM0 route; the started-TM2 bridge is a theorem in `TM0Route`
rather than a separate table-facing reduction structure.

The data-level bridge `PostProgram.toTableProgram` is now in place for the
current table-machine tile backend. A finite-TM0 `move` becomes one table row. A
finite-TM0 `write` becomes a write-and-move-right row followed by finite
return-left rows. Generated row targets and written symbols are proved to lie in
the resulting table supports. The table simulation is now proved both ways at
the halting level:

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
computability of the folded finite-TM0 program construction used by the
reduction.

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

The older normalized-program route has been superseded by the generated
position-code route.  The live source-side target is now computability of
`TM0FoldedCompiler.positionProgramData ∘ NatPartrecToToPartrec.translate`, not
the broader normalized `programData` map.  The normalized route remains useful
as a diagnostic comparison path, but the final proof should not spend effort
proving row equality with the canonical folded rows when the generated
position-coded program has its own semantic lookup theorem.
`TM0FoldedCompiler.programData` is a normalized form of `program` where the
constant initial rows are exposed definitionally, with
`TM0FoldedCompiler.programData_eq_program` relating it back to the semantic
`program`.  The generated-position route instead uses
`TM0FoldedCompiler.positionProgramData` and the semantic theorem
`TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom`.

The remaining machine-side blocker is the primitive-recursive construction of
the source-uniform generated descriptor rows.  The current weakest public
source target is:

```lean
TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec
```

and it is implied by any of the row-level targets:

```lean
TM0FoldedReduction.SourcePositionCodeOneRowsPrimrec
TM0FoldedReduction.SourcePositionCodeBoundedInteriorRowsPrimrec
TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec
```

These targets avoid the dependent statement lookup type by exposing ordinary
`List TM0FoldedCompiler.SimStepData` rows over translated
`Nat.Partrec.Code` inputs.

The support-list and numeric state-code path is executable.  The TM0 count
wrappers now have direct primitive-recursive proofs through weighted support
mirrors, including
`partrecStartedTM0StatementCount_primrec`,
`partrecStartedTM0LabelCount_primrec`, and
`partrecStartedTM0StateCount_primrec`. The current obstacle is no longer the
numeric count path but the global descriptor decoder needed for
`TM0FoldedCompiler.simStepDataForLabelIndexFrom`: the fixed-code statement and
label decoders are primitive recursive, but the final proof must package the
code-uniform dependent label lookup into nondependent `SimStepData`. The finite
function payloads and `TM2to1.StAct` are now encoded. The recursive concrete
started `TM2.Stmt` type is now encoded by valid preorder node lists: validity
is primitive recursive, valid lists parse completely, and the resulting
`Primcodable (PartrecStartedTM2StmtNode.Stmt tc)` instance is available. The
started and unstarted concrete `TM2to1.Λ'` label types are now encoded too, by
flattening the four concrete stack-action cases and transporting unstarted
TM2 statements through the started-label wrapper.
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

There is now also a lighter generated-position source-level folded route in
`TM0FoldedReduction`. It records the exact obligations needed for the final
undecidability reduction from `Nat.Partrec.Code`:

```lean
structure TM0FoldedReduction.PositionSourceObligations where
  program_computable :
    Computable (fun c : Nat.Partrec.Code =>
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c))
  correct : forall c : Nat.Partrec.Code,
    (TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)).HaltsEmpty <->
      (Nat.Partrec.Code.eval c 0).Dom
```

The semantic half follows from the already-proved folded correctness theorem in
`TM0FoldedCompiler` together with the `NatPartrecToToPartrec.translate`
correctness chain. Keeping it as an explicit source-level obligation avoids
forcing the lightweight reduction file to import the very large folded semantic
proof.  The remaining computational target can therefore be narrowed to
computability of
`TM0FoldedCompiler.positionProgramData ∘ NatPartrecToToPartrec.translate`,
rather than computability on arbitrary `Turing.ToPartrec.Code`.

The lightweight generated-position source route now also has exact-shape
computability corollaries for the `PositionSourceObligations.program_computable`
field. In particular,
`sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode`
turns the source-level position-coded descriptor decoder proof directly
into

```lean
Computable (fun c : Nat.Partrec.Code =>
  TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c))
```

without going through the broader `Turing.ToPartrec.Code` target.

Do not import `TM0FoldedCompiler` into `TM0FoldedReduction` just to discharge
`PositionSourceObligations.correct`: that pulls the large folded semantic proof into
the lightweight reduction packaging. A direct attempt made the reduction target
impractically slow to rebuild. Keep the correctness field explicit here, or
move any automatically generated source correctness package to a separate
semantic/final module that is expected to import the compiler proof.
`TM0FoldedReduction.sourcePositionProgramData_correct_of_positionProgramData_tm0_correct`
now packages the lightweight part of this semantic bridge: any theorem proving
`positionProgramData` correct for every `Turing.ToPartrec.Code` immediately
composes with the source translation chain. The helper
`positionSourceObligationsOfProgramData` packages that semantic theorem together
with the remaining position-program-data computability proof. A trial build of
a separate final module that imported `TM0FoldedCompiler` was interrupted after
Lake spent 5596 seconds compiling `TM0FoldedCompiler` without producing its
`.olean`, so that final packaging should be treated as a heavyweight target.
The generated-position route is now packaged all the way to the theorem
surface: `positionSourceObligationsOfLabelIndexFromWithPositionCode` combines
the decoder primitive-recursive proof with `positionProgramData` correctness,
and the `*_position_source_positionCode` theorem family instantiates the final
encoded and unencoded undecidability statements from those two facts.
At the public final endpoint, `FinalReductionInputs` now also exposes
one-row, bounded-interior, and interior-row source constructors:
`ofScaffoldAndSourceOneRows`, `ofScaffoldAndSourceBoundedRows`, and
`ofScaffoldAndSourceRows`.  All three route through
`sourcePositionCodeLabelIndexFromPrimrec_of_*` and then the
source-specialized label-index constructor, so the final theorem surface shares
one weakest source-obligation path rather than packaging each row target
separately.
The semantic generated-position packaging in
`TM0FoldedPositionReduction.SourceObligations` follows the same route:
decoder-step, global-label, one-row, bounded-interior, interior-row, and
packaged row constructors now delegate through
`positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect` whenever
possible.  The named bridge
`sourcePositionCodeLabelIndexFromPrimrec_of_decoderStep` records that the
accumulator-step proof already yields the full source-specialized
label-index decoder by iteration.

The next computability proof still needs an explicitly source-indexed decoder.
The available statement and label encoders in `TM0Route` prove many fixed-`tc`
primitive-recursive facts, including the bounded-search decoder components, but
they do not by themselves compose over the dependent family
`tc = NatPartrecToToPartrec.translate c`. In particular, the raw statement
lookup
`TM0Route.partrecStartedTM0StatementAt? (NatPartrecToToPartrec.translate c) k`
has a result type depending on `c`, so it is not the right public `Primrec`
target. The current Lean boundary names the nondependent row-level targets
instead:

```lean
TM0FoldedReduction.SourcePositionCodeOneRowsPrimrec
TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec
TM0FoldedReduction.SourcePositionCodeBoundedInteriorRowsPrimrec
```

These abbreviations package the source-uniform generated descriptor rows after
the statement lookup has been decoded into `List TM0FoldedCompiler.SimStepData`.
The next bridge should therefore construct the source-level statement/support
lookup directly over encoded source codes, prove an extensional correctness
theorem for the generated descriptor rows, and discharge one of these row-level
primitive-recursion targets.
The source route also has package-level computability wrappers
`sourceProgramData_computable_of_positionCodeOneRowsWithStatementNodup`,
`sourceProgramData_computable_of_positionCodeBoundedInteriorRowsWithStatementNodup`,
and `sourceProgramData_computable_of_positionCodeInteriorRowsWithStatementNodup`
plus exact-shape primed variants.  These consume the same row-plus-statement
nodup packages used by the theorem surfaces, so future decoder work should aim
to construct one package rather than separately threading the fields.
The generated position-code accumulator-step target now also bridges back to
the older bounded-search presentation on the valid Partrec-variable index path:
`sourceSearchCodeOneRowsVar_primrec_of_positionCodeDecoderStep`,
`sourceProgramData_computable_of_source_searchCodeOneVarRows_of_positionCodeDecoderStep`,
and `sourceObligationsOfSearchCodeOneVarRowsPositionCodeDecoderStep` show that
the decoder-step proof plus translated statement-list nodup supplies the
variable-branch search-row route.  This does not close
`SourcePositionCodeOneRowsPrimrec`, because that stronger row target keeps the
numeric position slot independent of the variable; it does make precise that
the remaining arbitrary-slot work is the only gap between the generated
position-code step and the older source-row presentation.
The flat label-index arithmetic has now been separated out in
`TM0FoldedReduction.sourceLabelIndexFromSplit?` and the started wrapper
`sourceLabelIndexStartSplit?`, with primitive-recursive proofs. These helpers
decode the non-dependent statement offset and `PartrecVar` slot from the flat
label index, so the remaining source decoder work can focus on turning the
statement offset into executable TM0 statement data and then generating rows.
They now also package the range facts needed by the indexed descriptor list:
successful started splits imply `i < sourceLabelCount c`, every
`i < sourceLabelCount c` has a successful started split, and
`sourceLabelIndexStartSplit?_isSome_iff_lt_labelCount` states the exact
success range.

There is also now a position-coded descriptor path in `TM0FoldedProgram`:
`simStepDataForLabelIndexFromWithPositionCode` uses the explicit rectangular
statement/variable position as the current-state code, and its fixed-code
primitive-recursive proof is in place. `TM0FoldedReduction` exposes the matching
source wrapper
`sourceSimStepDataForLabelIndexFromWithPositionCode` and the usual global-to-
source primitive-recursive bridge. This gives a cleaner possible decoder target
than support-search state codes, but it still needs an equivalence proof showing
that the position code agrees with the state code used by the current folded
state list before it can feed `sourceProgramData_computable_of_source_*`.
The first invariant for that route is now proved: successful statement/variable
position decoding produces a code in `partrecStartedTM0States`, both globally
(`labelAtByStatementFromWithPositionCode?_code_mem_states`) and through the
source wrapper
`sourceLabelAtByStatementFromWithPositionCode_code_mem_states`.
The second invariant is also in place: the produced position code reads back to
the decoded label in `partrecStartedTM0LabelSupportList`, via
`labelAtByStatementFromWithPositionCode?_support_get?` and the source wrapper
`sourceLabelAtByStatementFromWithPositionCode_support_get?`.
This has now been lifted from the label decoder to generated descriptor rows:
every descriptor emitted by `simStepDataForLabelIndexFromWithPositionCode`
carries the decoded position code as its current-state field, and that field
reads back to the decoded label in `partrecStartedTM0LabelSupportList`; the
source-level wrapper is
`sourceMem_simStepDataForLabelIndexFromWithPositionCode_current_support_get?`.
The position-coded route is now also threaded through the indexed descriptor
and program-data interfaces. `simStepDataByLabelIndexWithPositionCode` and
`sourceSimStepDataByLabelIndexWithPositionCode` have primitive-recursive
builders from the corresponding offset decoder, and
`sourceProgramData_computable_of_source_labelIndexFromWithPositionCode` reduces
source program-data computability to two explicit obligations: primitive
recursiveness of the position-coded offset decoder and equality between the
rows generated by the position-coded indexed descriptors and the semantic
folded simulation rows. The position-code itself is now default-aware:
`labelPositionCode` sends Mathlib's forced default/start label
`sourceDefaultLabel` to state code `0`, and uses the shifted rectangular
support-list position for all other decoded labels. This removes the immediate
duplicate introduced by `default :: labelList` while preserving the proved
state-membership and support-readback invariants. The canonical-code bridge is
now factored through an explicit minimality invariant: if the support list reads
back label `q` at code `n`, and no earlier support-list entry reads back `q`,
then `stateCode q = n`. Because the current TM1 statement support list is a raw
recursive enumeration rather than a proven duplicate-free list, the bounded
search-code decoder remains the canonical route for row equality. The
position-code minimality proof should only be used after proving the relevant
no-earlier-duplicate invariant for the raw support enumeration.
The canonical bounded-search path now has the same split bridge as the
position-coded path: `sourceLabelAtByStatementFromWithSearchCode?_of_split`
and `sourceSimStepDataForLabelIndexFromWithSearchCode_of_split` turn the
source arithmetic split plus a statement lookup into the exact
bounded-search-coded label and descriptor rows. The remaining canonical
computability work is therefore concentrated on a source-level executable
statement lookup over encoded source codes, not on the flat label-index
arithmetic.

Next implementation targets:

1. Prove one of the source-level generated position-code row targets, preferably
   `TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec` or directly
   `TM0FoldedReduction.SourcePositionCodeOneRowsPrimrec`. This should be done
   by constructing a source-uniform executable statement/support decoder whose
   output is compared extensionally to the existing dependent fixed-`tc`
   decoder, then generating the folded TM0 descriptor rows.
2. Use that row target to prove source-level computability of the generated
   position-coded folded finite-TM0 reduction:

   ```lean
   Computable (fun c : Nat.Partrec.Code =>
     TM0FoldedCompiler.positionProgramData
       (NatPartrecToToPartrec.translate c))
   ```

   This can use Mathlib's existing recursion theorem for `Nat.Partrec.Code`
   instead of first proving a general recursion theorem for
   `Turing.ToPartrec.Code`.
3. Optionally strengthen the result to computability on all
   `Turing.ToPartrec.Code` for a reusable folded-route corollary, but keep the
   public domino theorem surface on `PositionSourceObligations`.
4. Finish the Robinson Section 7 scaffold proof.  The light reduction module
   now exposes the intended route through
   `LayeredSection7ObstructionRoutingInvariant` and
   `Figure18CanonicalRawBoundaryBoardLevelChecks`, including row-major checked
   board-level wrappers:

   ```lean
   encoded_domino_problem_undecidable_l2c1_section7_geom_tower_board_checks_position_source
   domino_problem_undecidable_l2c1_section7_geom_tower_board_checks_position_source
   encoded_domino_problem_undecidable_l2c1_section7_geom_tower_board_rows_position_source
   domino_problem_undecidable_l2c1_section7_geom_tower_board_rows_position_source
   ```

   and the analogous L2 component-2 wrappers.  The remaining scaffold-side
   work is not another theorem alias: it is to prove the concrete finite
   checked origin-zero layer-stack witnesses for the audited Figure 18 data,
   which now feed `LayeredSection7ObstructionRoutingInvariant` directly via
   `scaffoldDataOfNatSitesSection7ObstructionRoutingOfOriginZeroCheckedStacks`
   and the `l2Component*_Section7ObstructionRoutingOfOriginZeroCheckedStacks`
   wrappers.  The light reduction module names the two concrete checked-stack
   hypotheses as `L2C1OriginZeroCheckedStacks` and
   `L2C2OriginZeroCheckedStacks`, and routes them through both board-level
   checks and row-major board-level theorem surfaces.  The constructors
   `l2c1OriginZeroCheckedStacksOfOriginZeroWindows` and
   `l2c2OriginZeroCheckedStacksOfOriginZeroWindows` show that origin-zero
   active/corner windows plus the audited finite compatibility tables produce
   these checked-stack hypotheses, so the checked-stack route is connected to
   the existing origin-zero scaffold interface.  This checked-stack route is a
   useful bridge, but not the preferred final Section 7 target.
   The remaining scaffold-side task is to construct/prove the field-based
   local signal tower and the shifted board-level raw-boundary/free-line finite
   data, or replace that over-strong raw-boundary diagnostic target with a
   leaner invariant derived directly from the board/free-line proof.
   Robinson's original Section 7 text supports the leaner board route: prove a
   field-based local signal tower whose free rows and columns are exactly the
   unobstructed board lines, and use a raw `TilesPlane fig13Tiles` witness to
   supply the translated board boxes.  The reduction module now exposes this
   shape through
   `encoded_domino_problem_undecidable_l2c1_signal_tower_fig13_plane_position_source`,
   `domino_problem_undecidable_l2c1_signal_tower_fig13_plane_position_source`,
   the corresponding generated `interiorRows` wrappers, and the analogous L2
   component-2 wrappers; the data-layer constructors
   `ofL2C1SignalLocalTowerFig13TilesPlane` and
   `ofL2C2SignalLocalTowerFig13TilesPlane` recenter the translated Robinson
   board boxes into the existing indexed-box scaffold certificate.  The
   current preferred proof-facing package is
   `L2C1SignalTowerTranslatedBoxData` /
   `L2C2SignalTowerTranslatedBoxData`: it stores the local signal tower and
   positive translated active-corner boxes, and the wrappers
   `*_signal_tower_translated_box_data_position_source` and
   `*_signal_tower_translated_box_data_interiorRows` route this package through
   the direct pair-free signal-tower certificate.  This translated-box surface
   is now a compatibility bridge, not the preferred final scaffold target.  The
   older `L2C1SignalTowerBoardData` / `L2C2SignalTowerBoardData` package still
   exists as a bridge through row-major checked board levels, but should not be
   the main target.  The bundled checked-stack/plane and checked-stack/box
   packages still feed the translated-box package through
   `l2c1SignalTowerTranslatedBoxDataOfCheckedFig13PlaneData`,
   `l2c2SignalTowerTranslatedBoxDataOfCheckedFig13PlaneData`,
   `l2c1SignalTowerTranslatedBoxDataOfCheckedFig13BoxData`, and
   `l2c2SignalTowerTranslatedBoxDataOfCheckedFig13BoxData`, but the raw Figure
   13 plane/box premises in these packages are now formally refuted by
   `not_tilesPlane_fig13Tiles`, `not_tileableBoxes_fig13Tiles`, and the
   package-level `not_l2c*Fig13*Data` theorems.  The same diagnostic bridge
   exists one level earlier for origin-zero windows via
   `l2c1SignalTowerTranslatedBoxDataOfOriginZeroFig13TilesPlane`,
   `l2c2SignalTowerTranslatedBoxDataOfOriginZeroFig13TilesPlane`,
   `l2c1SignalTowerTranslatedBoxDataOfOriginZeroFig13TileableBoxes`, and
   `l2c2SignalTowerTranslatedBoxDataOfOriginZeroFig13TileableBoxes`; these are
   diagnostics only.  The remaining scaffold statement should instead be read
   as checked origin-zero stacks plus active-corner layer patches, surfaced by
   `L2C1CheckedStackLayerPatchData`,
   `L2C1OriginZeroCheckedStacks`, and `L2C1ActiveCornerLayerPatches`.  The
   adjacent
   source raw-boundary board target exposed as
   `Figure18CanonicalRawBoundaryBoardLevelChecks` should
   now be treated as a diagnostic, not as the next finite target: finite
   predicates `sourceRawBoundaryHCompatiblePairBool` and
   `sourceRawBoundaryVCompatiblePairBool` find no horizontal or vertical
   two-cell source witnesses when checked layer-stack compatibility is combined
   with raw Figure 13 boundary compatibility.  This matches the Section 7
   reading that payload neighbors are routed through free board lines rather
   than adjacent plane coordinates.  This is now formalized at the all-level
   interface too: `not_hasCanonicalFigure16SourceRawBoundaryCheckedLevelData`,
   `not_hasCanonicalFigure16SourceRawBoundaryLevelChecks`,
   `not_hasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool`, and
   `not_hasCanonicalFigure16SourceRawBoundaryBoardLevelChecks` show that these
   source/raw-boundary surfaces would imply the refuted positive-board raw
   Figure 13 square tilings.  The older
   `NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations` surface remains
   as a compatibility bridge, not as the desired final scaffold target.
5. Add the semantic-final wrappers for the row-major Section 7 geometry route.
   `LeanWang.TM0FoldedPositionReduction` is now an import wrapper split into
   `SourceObligations` and `Theorems` submodules, so the large folded
   correctness proof can be cached below the final theorem-facing wrappers.
   The public wrapper target now builds directly with
   `lake build LeanWang.TM0FoldedPositionReduction`, so this split should remain
   the default way to check theorem-surface edits before attempting a full
   project build.
6. Use the split final bridge
   `encoded_domino_problem_undecidable_of_checkedStacksAndLayerPatches` /
   `domino_problem_undecidable_of_checkedStacksAndLayerPatches` as the main
   scaffold-facing theorem surface.  Its finite scaffold inputs are exactly
   `L2C1OriginZeroCheckedStacks` and `L2C1ActiveCornerLayerPatches`, plus the
   source-side `SourcePositionCodeInteriorRowsPrimrec`.
   This split route now has matching final wrappers for each source-obligation
   granularity: direct `PositionSourceObligations`, packaged
   `SourcePositionCodeInteriorRowsWithStatementNodup`, decoder-step primrec,
   global label-index primrec, and source-specialized label-index primrec.
   Prefer the weakest wrapper whose machine-side obligation has already been
   proved, while keeping the scaffold obligations split until bundling them is
   useful.
   For package-style final assumptions, prefer
   `FinalCheckedStackLayerPatchConstructionObligations`,
   `FinalCheckedStackLayerPatchDecoderStepConstructionObligations`,
   `FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations`, or
   `FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations`.
   These all route through `L2C1CheckedStackLayerPatchData` and avoid the
   refuted Figure 16 level-data interface.
7. Do not use the old Figure 16 compatible-level bridge as a final theorem
   route.  The direct finite-data interface is too strong as stated: the
   checked source-stack compatibility is phrased in terms of adjacent Figure 16
   substitution-block boundaries; the audited Figure 13 black layer has no
   horizontally or vertically matching adjacent `phi_L3` block boundaries at
   all, formalized by `blackBlockAtSite_no_hBoundary` and
   `blackBlockAtSite_no_vBoundary` in
   `LeanWang.OllingerRobinsonFigure13Obstructions`.  The all-level assumption
   is now formally refuted by
   `not_hasCanonicalCheckedFigure16RecognizedCompatibleLevelData`, using the
   level-0 contradiction
   `not_canonicalCheckedFigure16RecognizedCompatibleLevelData_zero`.
   `LeanWang.Final` and
   `LeanWang.OllingerRobinsonFigure18PositionReduction` no longer export theorem
   wrappers whose scaffold input is a compatible Figure 16 macro-square or
   level-check assumption; the public theorem surfaces route through
   `L2C1RobinsonSection7BoardFreeLineLayerPatchData` or the concrete
   `L2C1CheckedStackLayerPatchData` package instead.  Lower-level compatible-level
   definitions may remain as diagnostics, but the concrete scaffold proof should
   route recognized macro-square compatibility through Section 7 free-line
   geometry and active-corner layer patches, not through adjacent black-layer
   source-stack block boundaries.
   The corresponding decoder-step construction package
   `FinalSection7PositiveBoxDecoderStepConstructionObligations` exposes the
   intermediate source-facing theorem surface: its source obligation is
   `SourcePositionCodeDecoderStepPrimrec`, primitive recursiveness of
   `sourcePositionCodeDecoderStep`, rather than the stronger
   `SourcePositionCodeInteriorRowsPrimrec`.
   The preferred source-facing theorem surfaces are now
   `FinalGlobalPositionCodeConstructionObligations`,
   `FinalCheckedGlobalPositionCodeConstructionObligations`, and
   `FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations`.
   They use `GlobalPositionCodeLabelIndexFromPrimrec`, which is bridged to
   `SourcePositionCodeDecoderStepPrimrec` by specializing the global
   position-code label-index decoder to `fuel = 1` on valid variable slots.
   This makes the remaining machine/source target closer to the actual
   generated folded-program decoder.
8. Specialize the concrete generated-position folded-route/scaffold
   corollaries, in particular
   `encoded_domino_problem_undecidable_of_scaffold_position_source_positionCode`
   and `domino_problem_undecidable_of_scaffold_position_source_positionCode`,
   to those concrete instances to recover the unconditional encoded and
   unencoded domino theorems.
9. Optionally replace the current table-machine tiles by direct finite-TM0
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

Robinson's original Section 7 argument is the clean route for the remaining
Figure 18 geometry.  The proof should target a board/free-grid certificate:

- red borders form nested boards of side `4^n - 1`;
- obstruction signals mark exactly the non-free rows and columns of a board;
- the unmarked free rows and columns can be enumerated as a virtual
  `2^n + 1`-by-`2^n + 1` grid;
- crossings of those free rows and columns provide the payload cells, with the
  lower-left crossing the distinguished corner site;
- payload edge matches are routed through the intervening board cells, so the
  proof should not require adjacent plane coordinates for consecutive virtual
  rows or columns.

Robinson's original paper [`robinson.pdf`](robinson.pdf) supports this route
more directly than Figure 18 alone.  In Section 7,
after defining red borders and boards, Robinson states that no obstruction
signals run along the free rows; a tile is in a free row iff no horizontal
obstruction signal passes through it, and similarly for free columns.  He then
superposes the Turing-machine signals on board tiles free in both directions,
lets one-direction-free tiles transmit unchanged in their free direction, and
observes that the board acts as though the free rows and columns were a
contiguous square.  In Lean terms, prioritize the field-based
`HasFigure18RobinsonBoardLevelSignalLocalTowerForTable` /
`HasNatSiteSignalLocalTower` route over the stronger shifted raw-boundary
diagnostic `Figure18CanonicalRawBoundaryBoardLevelChecks`.

In Lean, this is represented by the
`Figure18RobinsonBoardRoutedFreeGrid` target, which converts to the existing
indexed-routed Figure 18 witness and then to `ForcesFixedCornerSquares`.
The older adjacent/listed-active window targets remain useful only if a local
Figure 18 extraction really produces adjacent plane coordinates.

The current scaffold-facing route is the origin-zero active/corner window
target, paired with generated finite stack compatibility and translated
positive-radius boxes.  This now converts directly to the cleaner
`NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations` surface, so the
Figure 13/Figure 16 finite transcription can feed Robinson's Section 7 signal
tower target without morally depending on canonical row equality.

Current proof frontier: two tempting standalone tileability routes are now
diagnostics, not proof-facing assumptions.

- The raw Figure 13 macro-tile route is false: the raw tile list does not tile
  even a `2 x 2` square (`not_tileableSquare_fig13Tiles_two`), so
  `HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares` is only a legacy
  diagnostic surface.
- The standalone subdivided Figure 18 site route is also false: the Figure 18
  site graph has no compatible `3 x 3` square
  (`Figure18Site.hasRectangleStackBool_three_three_eq_false`), so
  `HasCompatibleFigure18ScaffoldSquares` / `TilesPlane figure18ScaffoldTiles`
  should not be used as the scaffold-instantiation target.

The proof-facing route is therefore the Section 7 active-corner/translated-box
route.  The board/free-line construction should produce the active/corner boxes
needed by `L2C1SignalTowerTranslatedBoxData` / `L2C2SignalTowerTranslatedBoxData`
(or the underlying
`NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations`) directly:
obstruction signals identify free rows and columns, routed board cells carry
payload matches between neighboring virtual free-grid crossings, and the finite
Figure 13/Figure 16 layer checks certify the local stack data at those routed
crossings.

The theorem surface now also has the more Robinson-shaped
`L2C1RobinsonSection7BoardFreeLineTranslatedBoxData` /
`L2C2RobinsonSection7BoardFreeLineTranslatedBoxData` packages.  These replace
the refuted raw macro-square premise with two direct Section 7 obligations:
board/free-line active-corner recognition, and positive translated active-corner
indexed boxes for the backward scaffold realization.  The next concrete proof
work should instantiate those two fields, rather than revive any standalone
Figure 13 or Figure 18 square-tiling target.  The existing origin-zero
translated-box obligations now coerce into this board/free-line package, so the
remaining scaffold work can be phrased either as origin-zero recognition plus
translated boxes, or directly as the board/free-line active-corner/translated-box
fields.

There is now an even more finite-check-facing theorem surface:
`L2C1RobinsonSection7BoardFreeLineLayerPatchData` /
`L2C2RobinsonSection7BoardFreeLineLayerPatchData`.  It uses the same
board/free-line active-corner recognition field, but replaces the
positive-translated-box field by `HasActiveCornerLayerBoxPatches`, matching the
kind of certificate produced by the Figure 13/Figure 16 layer transcription.
This should be the preferred target while finishing the concrete finite
scaffold instantiation.  There is also a centered positive-box package,
`L2C1RobinsonSection7BoardFreeLinePositiveBoxData` /
`L2C2RobinsonSection7BoardFreeLinePositiveBoxData`, which records exactly the
remaining backward geometry before the generic layer-patch conversion.  The
existing translated-box surface, and the origin-zero translated obligation
surface, now both expose the centered positive-box package explicitly before
coercing into the layer-patch package, so older Section 7 routes remain usable
while the finite layer-patch checks are being finished.  The reusable Nat-site
constructors
`scaffoldDataOfNatSitesLayerPatchesOfPositiveActiveCornerIndexedBoxes` and
`scaffoldDataOfNatSitesLayerPatchesOfPositiveTranslatedIndexedBoxes` isolate
the exact remaining backward-realization task: produce positive active-corner
indexed boxes, either centered or translated, for the concrete L2 scaffold.
The generic origin-zero translated obligation namespace also exposes
`positiveActiveCornerIndexedBoxes` and `toActiveCornerLayerBoxPatches`, so
future concrete certificates can stay on the origin-zero surface while still
feeding the layer-patch realization theorem directly.
It now also exposes `toBoardFreeLineActiveCorner` and
`toCompatibleLevelObligationsOfLayerPatches`, making the finite-check-facing
route explicit: origin-zero windows provide Robinson's board/free-line
active-corner invariant, and the centered layer patches provide the backward
scaffold realization.  The default generic
`NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations.toCompatibleLevelObligations`
projection now uses this layer-patch route, so the origin-zero theorem wrappers
no longer silently detour through the older canonical/free-site translated-box
constructor.
The generic finite-check-facing surface is now named
`NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations`: it records
Robinson board/free-line active-corner recognition, generated Figure 13/Figure
16 pair compatibility, and finite active-corner layer patches, then converts
directly to `NatSiteRobinsonCompatibleLevelObligations`.  Origin-zero
obligations project through this named surface before reaching the compatible
level-grid theorem.  The L2-specific layer-patch data packages now also project
to this named surface directly, using the audited generated pair-compatibility
checks for the two blank candidates; the L2 layer-patch theorem wrappers route
through the generic Section 7 board/free-line layer-patch theorem family rather
than through an unnamed compatible-level detour.  The same is now exposed for
origin-zero translated obligations via the
`*_origin_zero_section7_layer_patches_*` theorem family, which should be the
preferred origin-zero theorem surface over the older signal-tower detour.  The
light reduction module also exposes packaged
`SourcePositionCodeInteriorRowsWithStatementNodup` wrappers for the L2
board/free-line layer-patch data packages and for the origin-zero Section 7
layer-patch obligation family, so downstream code can use the preferred finite
surface without manually rebuilding `PositionSourceObligations`.
The L2-specific checked finite scaffold target is now also packaged as
`L2C1CheckedStackLayerPatchData` / `L2C2CheckedStackLayerPatchData`, with
constructors from origin-zero windows and theorem wrappers for both direct
`PositionSourceObligations` and the packaged source-uniform interior decoder.
It also has wrappers for the lighter generated `SourcePositionCodeInteriorRowsPrimrec`
route.
The existing checked signal-tower Figure 13 plane/box packages still convert
into this target via
`l2c1CheckedStackLayerPatchDataOfCheckedFig13PlaneData`,
`l2c2CheckedStackLayerPatchDataOfCheckedFig13PlaneData`,
`l2c1CheckedStackLayerPatchDataOfCheckedFig13BoxData`, and
`l2c2CheckedStackLayerPatchDataOfCheckedFig13BoxData`, but these are now
diagnostic compatibility bridges rather than proof-facing obligations.  The
finite raw Figure 13 box hypothesis is itself refuted in Lean by
`not_tileableBoxes_fig13Tiles`, reducing it to the already known positive-board
raw Figure 13 obstruction.  Accordingly, the origin-zero Figure 13 box package
is diagnostic only, and `LeanWang.Final` no longer exports the
`FinalOriginZeroFig13BoxData`, `FinalCheckedSignalTowerFig13BoxData`, or
checked-recognized-Figure-13 theorem routes as public final routes.  Future
concrete scaffold work should not try to prove a checked-stack/box package
containing `Figure13TileableBoxes`.
The checked signal-tower board packages now also feed this route directly via
`l2c1CheckedStackLayerPatchDataOfCheckedBoardData`,
`l2c2CheckedStackLayerPatchDataOfCheckedBoardData`, and origin-zero
checked-board-level/check wrappers, so raw-boundary board-level finite checks
are enough once origin-zero recognizability is available.
The old over-strong source/raw-boundary diagnostic route is now explicitly
closed off by the reflected finite checks
`noSourceRawBoundaryHCompatiblePairsBool_eq_true` and
`noSourceRawBoundaryVCompatiblePairsBool_eq_true`: there are no horizontal or
vertical two-cell witnesses satisfying both source-stack compatibility and raw
Figure 13 boundary compatibility.  It is also closed at the theorem-surface
level by `not_hasCanonicalFigure16SourceRawBoundaryCheckedLevelData`,
`not_hasCanonicalFigure16SourceRawBoundaryLevelChecks`,
`not_hasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool`, and
`not_hasCanonicalFigure16SourceRawBoundaryBoardLevelChecks`, which reduce these
all-level raw-boundary surfaces to the already refuted positive-board raw
Figure 13 square tilings.  The remaining scaffold proof should
therefore use compatible Figure 18 macro-squares / board-free-line data, not
the source raw-boundary diagnostic as a final target.
This is the clean target for the concrete Figure 13/Figure 16 transcription:
prove checked origin-zero stacks plus active-corner layer patches, then feed
that single package to the final Section 7 reduction.
The purely finite rectangle-stack half of the checked-stack target is now
proved and named for both audited candidates:
`l2c1CheckedStacksForListedActiveSiteRectangles` and
`l2c2CheckedStacksForListedActiveSiteRectangles`.  These package the reflected
Figure 13/Figure 16 generated pair-compatibility checks for every locally
compatible listed active-site rectangle.  Thus the remaining bridge to
`L2C*OriginZeroCheckedStacks` is the Robinson geometry selecting origin-zero
active/corner windows, not the finite layer-stack decoding.
The Section 7 layer now also composes this with the canonical Robinson
free-site bridge:
`l2c1OriginZeroCheckedStacksOfCanonicalFreeSiteRectActiveCorner` and
`l2c2OriginZeroCheckedStacksOfCanonicalFreeSiteRectActiveCorner` turn canonical
free-site active/corner recognition into finite checked stacks.  The matching
`*_CanonicalFreeSiteCanonicalCheckedCompatibleFig16*` constructors combine
that geometry with the audited Figure 16 compatibility data to produce the
checked-stack/valid-translated-box and checked-stack/layer-patch packages.
Thus the scaffold-side finite decoding is connected below the canonical
Robinson recognition target.

The current public final surface follows the proof-facing board/free-line
route: `FinalReductionInputs` asks for
`L2C1RobinsonSection7BoardFreeLineLayerPatchData` and
`PositionSourceObligations`.  The preferred higher-level theorem packages ask
for the same scaffold data plus `GlobalPositionCodeLabelIndexFromPrimrec`,
which derives those source obligations through the generated position-code
decoder-step bridge.  The Section 7 layer-patch package is the proof-facing
scaffold target.  `LeanWang.Final` also exposes wrappers from the more concrete
finite transcription target
`L2C1CheckedStackLayerPatchData`, which packages checked origin-zero stacks
with active-corner layer patches and constructs the Section 7 input.  The raw
positive-board Figure 13 checks and the direct
`Figure18CanonicalRawBoundaryCheckedLevelData` /
`Figure18CanonicalRawBoundaryBoardLevelChecks` source/raw-boundary targets are
kept only as lower-level diagnostic surfaces; `LeanWang.Final` no longer
exports them, the raw Figure 13 box routes, or the checked-recognized raw
Figure 13 routes as final theorem routes.
The generic concrete Figure 18 scaffold layer now also has
`RoutedCertificate.ofRobinsonSection7BoardFreeLineLayerPatches`, and the two
L2 candidates expose
`l2c1Figure18RoutedCertificateOfRobinsonSection7BoardFreeLineLayerPatchData`
and
`l2c2Figure18RoutedCertificateOfRobinsonSection7BoardFreeLineLayerPatchData`.
Thus the finite layer-patch package is not just a compatible-level shortcut:
it also feeds the concrete routed Figure 18 certificate route directly.
The same routed-certificate bridge is now exposed at the checked finite target
via `l2c1Figure18RoutedCertificateOfCheckedStackLayerPatchData`,
`l2c2Figure18RoutedCertificateOfCheckedStackLayerPatchData`, and split-field
checked-stack/layer-patch variants.  This keeps the proof frontier aligned with
the concrete transcription target: prove checked origin-zero stacks plus active
corner layer patches, and both the final reduction route and the concrete
Figure 18 certificate route are available.
The current layer-patch target now has one more concrete finite-check surface:
`L2C1CheckedStackValidTranslatedBoxData` /
`L2C2CheckedStackValidTranslatedBoxData` package checked origin-zero stacks with
valid translated scaffold boxes.  The existing finite no-neighbor active-site
checks turn those valid translated boxes into active-corner layer patches via
`l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData` and
`l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData`.  The final
module exposes the first-candidate route as
`FinalCheckedStackValidTranslatedBoxConstructionObligations`, with encoded and
unencoded endpoint theorems, and now also has decoder-step, global-label, and
source-label variants
`FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations`,
`FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations`,
and
`FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations`.
These first-candidate wrappers now project to the matching
`FinalOriginZeroTranslatedBox*ConstructionObligations` wrappers through
`l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData`.
Their exported endpoint path therefore exposes the origin-zero
translated-positive-box reduction surface before falling back to older
layer-patch compatibility helpers.
The checked-stack plus compatible Figure 16 macro-square route now has matching
decoder-step, global-label, and source-label packages that project through this
valid-translated-box target.
Those Figure 16 compatible wrappers now also project to the matching
`FinalOriginZeroTranslatedBox*ConstructionObligations` wrappers, and the
source-label endpoint routes through the checked-stack/valid-box source
endpoint.
The generated-position integration layer now mirrors this newer target with
semantic-correctness-discharged wrappers for Section 7 translated boxes and
checked-stack/valid-translated-box data, so callers can use the current
scaffold surfaces without manually rebuilding `PositionSourceObligations`.
This gives the concrete scaffold work a
lower-level target than `L2C1ActiveCornerLayerPatches` without falling back to
the refuted raw Figure 13 box assumptions.  The compatible Figure 16 route now
also exposes this intermediate target directly:
`l2c1ValidTranslatedBoxesOfCanonicalCheckedCompatibleFig16` and
`l2c2ValidTranslatedBoxesOfCanonicalCheckedCompatibleFig16` derive valid
translated scaffold boxes from compatible checked macro-squares, and the
checked-stack/origin-zero-window constructors package those boxes before
passing through the existing finite no-neighbor active-site checks.  The public
final module now also exposes the corresponding second-candidate checked-stack
and checked-stack/valid-translated-box routes via
`FinalL2C2CheckedStackLayerPatchConstructionObligations` and
`FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations`; the default
`FinalReductionInputs` route remains the first-candidate theorem surface.
The second candidate also has decoder-step, global-label, and source-label
variants for both layer patches and valid translated boxes, so both audited
scaffold candidates can be driven from the current generated-source targets.
The L2C2 checked-stack/valid-translated-box row-source, global-label, and
source-label routes now project to the origin-zero translated-positive-box
final surface through
`l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData`.
This makes the preferred label-index-carrying final theorem surfaces depend on
checked origin-zero stacks plus valid translated boxes directly, not only on
the layer patches derived from them.  The decoder-step route remains a
layer-patch endpoint until a source-label decoder is available.
The final module also exposes a concrete nat-site indexed-window route via
`FinalFigure13NatSitesIndexedWindowConstructionObligations`.  This is the
public endpoint closest to the human-audited Figure 13 layer table: it asks for
raw checked active-site specs, a checked corner, indexed active/corner windows,
and a realization certificate, then applies the existing concrete Figure 13
scaffold theorem with the generated interior-row source target.
It also now exposes the more proof-facing Robinson indexed-box route via
`FinalFigure13RobinsonIndexedBoxConstructionObligations`: a concrete
`NatSiteRobinsonIndexedBoxScaffoldCertificate` bundles the checked routed
free-grid stacks and active-corner indexed boxes, then forgets to the existing
Figure 18 flexible instance endpoint with generated interior position-code
rows.  This is the cleaner final API for the current scaffold work because it
matches the certificate produced by the Figure 13/Figure 16 transcription
rather than restating its lower-level indexed-window and realization fields.
The same final route is now exposed one and two levels lower via
`FinalFigure13RobinsonTowerIndexedBoxConstructionObligations` and
`FinalFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations`.
Thus the current Section 7 target can be stated directly as a local Robinson
signal tower plus translated positive active-corner boxes; the existing
constructors package those facts into tower/indexed-box obligations, then into
the Robinson indexed-box scaffold certificate.
For the first audited L2 candidate, the final module now also exposes the
specialized `FinalL2C1SignalTowerTranslatedPositiveBoxData` and
`FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations` surfaces.
`FinalOriginZeroTranslatedBoxConstructionObligations` projects to this
specialized signal-tower route, so origin-zero data, signal-tower data, and the
generic Robinson indexed-box final route are connected without restating the
active-site list and corner-site parameters.
The proof-facing Section 7 package
`TM0FoldedReduction.L2C1SignalTowerTranslatedBoxData` now also feeds this final
surface directly via
`FinalL2C1SignalTowerTranslatedBoxDataConstructionObligations`, avoiding a
manual reconstruction of the Nat-site signal-tower obligation fields in the
final module.
The board/free-line translated-box package
`TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineTranslatedBoxData` now
also has a direct final route through
`FinalSection7TranslatedBoxConstructionObligations`.  This is the cleaner
non-diagnostic upstream Section 7 surface: it asks for board/free-line
active/corner recognition and translated active-corner boxes, then converts to
the centered positive-box final route.
The origin-zero translated-box obligations project to this Section 7 route via
`FinalOriginZeroTranslatedBoxConstructionObligations.toSection7TranslatedBoxConstructionObligations`,
using the existing Section 7 conversion from origin-zero windows and translated
boxes to board/free-line translated-box data.
The same translated-box route is now exposed at the narrower generated-source
levels through
`FinalSection7TranslatedBoxDecoderStepConstructionObligations`,
`FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations`, and
`FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations`, with
origin-zero decoder/global/source wrappers projecting to those proof-facing
Section 7 surfaces.
On the scaffold side,
`l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData`
now converts checked origin-zero stacks plus valid translated finite boxes
directly into the preferred board/free-line translated-box package; the final
checked-stack/valid-translated-box wrapper exposes this projection.
The finite Figure 16 compatible macro-square and level-data constructors now
also feed that preferred package directly through
`l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksCanonicalCheckedCompatibleFig16`
and the corresponding origin-zero-window/level-data variants, instead of
detouring through the older layer-patch surface.
The public final layer now exposes this first-candidate finite target as
`FinalFigure16CompatibleConstructionObligations`: checked origin-zero stacks,
compatible Figure 16 macro-squares, and generated interior source rows imply
the final domino-undecidability endpoints via the preferred Section 7
translated-box route.
The canonical Robinson free-site variant is now exposed as
`FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations` and the
decoder-step/global-label/source-label variants.  The top-level aliases
`encoded_domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecks`
and
`domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecks`
are now diagnostic surfaces rather than live scaffold targets:
`Figure18CanonicalCheckedRecognizedCompatibleLevelChecks` is definitionally the
canonical compatible macro-square target, and it is refuted by
`not_figure18CanonicalCheckedRecognizedCompatibleLevelChecks`.  Do not target
the row-major `Figure18CanonicalCheckedRecognizedCompatibleLevelData` surface
either; it is intentionally refuted by
`not_figure18CanonicalCheckedRecognizedCompatibleLevelData`.
The first-candidate canonical-free-site Figure 16 wrappers now project to the
matching `FinalOriginZeroTranslatedBox*ConstructionObligations` wrappers
through the checked-stack/valid-translated-box bridge; the source-label endpoint
also routes through the checked-stack/valid-box source endpoint.
The generated-position integration layer now exposes the same canonical
free-site/compatible-Figure-16 source-label route directly, for both audited
L2 candidates, through
`encoded_domino_problem_undecidable_l2c1_canonical_free_site_compatible_fig16_sourceCodeCorrect`
and its L2C2/unencoded analogues.  These theorems take exactly the three live
assumptions of the diagnostic route: canonical free-site active/corner
recognition, finite compatible Figure 16 level checks, and
`SourcePositionCodeLabelIndexFromPrimrec`.  Because the level-check assumption
is refuted, the live scaffold path remains the Section 7
translated-positive-box/layer-patch interface.
`LeanWang.Final` now exposes the same preferred source-label package for the
second audited candidate as
`FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations`,
with top-level aliases under
`*_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksSourcePositionCodeLabelIndexFrom`.
It also exposes the generated-interior-row version
`FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations`, with
top-level aliases under
`*_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksSourcePositionCodeInteriorRows`;
this route uses the existing source-side bridge from interior rows to the
source-specialized label-index decoder.
Both L2C2 canonical-free-site Figure 16 row-source and source-label packages
now project to
`FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations`
through the checked-stack/valid-translated-box bridge, so this upstream route
also exposes the origin-zero translated-positive-box scaffold surface.
The same L2C2 canonical-free-site route is now exposed with a direct
`TilesPlane figure18ScaffoldTiles` input as
`FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations`
and the decoder-step/global-label/source-label variants
`FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations`,
`FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations`,
and
`FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations`.
The direct aliases ending in
`l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneDecoderStep`,
`l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneGlobalPositionCodeLabelIndexFrom`,
and
`l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneSourcePositionCodeLabelIndexFrom`
now expose the existing source bridge without going through the arbitrary-slot
interior-row target.
The L2C2 compatible-Figure-16 final surface also has direct decoder-step and
global-label aliases,
`*_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksDecoderStep` and
`*_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksGlobalPositionCodeLabelIndexFrom`.
They use
`tilesPlane_figure18ScaffoldTiles_of_canonicalCheckedFigure16RecognizedCompatible`
to derive the scaffold-plane assumption from the finite compatible Figure 16
checks, so the public theorem surface no longer morally depends on providing a
raw plane tiling for those generated source routes.
The concrete second-candidate Figure 13 route is now exposed in
`LeanWang.Final` as
`FinalFigure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations`.
Its scaffold assumptions are exactly compatible routed Robinson free grids and
realization for `FinalFigure13L2C2CompatibleLevelScaffoldData`, the human-audited
L2C2 Nat-site scaffold.  Thus future scaffold work can target the concrete
Figure 13 compatible-level obligations directly, while the source side only
needs the source-specialized position-code label-index decoder.
The finite-patch sibling
`FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations`
is now exposed as well; it asks for compatible routed Robinson free grids plus
`HasActiveCornerLayerBoxPatches` for the same concrete scaffold data, avoiding
the need to state the full realization certificate at this final surface.
The next lower routing surface is also exposed:
`FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations`.
It asks for canonical product-witness routing and finite active-corner layer
patches for the concrete L2C2 scaffold, then derives the compatible routed
free-grid field through
`NatSiteRobinsonCompatibleLevelObligations.ofL2C2CanonicalProductRoutingLayerPatches`.
The positive-box variant
`FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations`
is now exposed too.  It asks for canonical product-witness routing and
positive-radius `ActiveCornerIndexedBox` witnesses for the same concrete L2C2
scaffold, then derives finite layer patches via
`scaffoldDataOfNatSitesLayerPatchesOfPositiveActiveCornerIndexedBoxes`.
The translated-positive-box variant
`FinalFigure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations`
is exposed as the more geometry-facing sibling: the positive-radius
active-corner indexed boxes may be centered at arbitrary origins and are
recentered to finite layer patches by
`scaffoldDataOfNatSitesLayerPatchesOfPositiveTranslatedIndexedBoxes`.
The currently preferred L2C2 Figure 13 route is now the ordinary-canonical
surface
`FinalFigure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations`.
It uses the existing
`NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations` package directly,
so the scaffold side needs canonical Robinson-board routing and translated
positive-radius active-corner indexed boxes, not the stronger product-witness
routing field.
The still more Section-7-shaped sibling
`FinalFigure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations`
is now exposed too.  It uses
`NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations`, whose
routing field is the selected free/free site rectangle; this should be the
natural public target for the obstruction/free-line scaffold argument before
forgetting back to ordinary canonical routing.
The L2C2 origin-zero sibling
`FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations`
is now exposed as the lower finite-check-facing route: origin-zero active/corner
windows imply the free-site-rectangle routing, and the translated positive boxes
carry the backward scaffold realization.
The L2C2 canonical-free-site scaffold-plane route now also projects into this
origin-zero translated-positive-box surface: canonical free-site recognition
gives origin-zero windows, `TilesPlane figure18ScaffoldTiles` gives translated
positive boxes via
`l2c2OriginZeroTranslatedObligationsOfOriginZeroWindowsFigure18ScaffoldTilesPlane`,
and the public row/decoder/global/source endpoints use the origin-zero
translated-obligation reduction route directly.
The L2C2 row-source, global-label, and source-label endpoint proofs now share
the named origin-zero translated source-label projection instead of rebuilding
the same position-source obligations inline.
It also exposes
`FinalFigure16CompatibleOriginZeroConstructionObligations`, where the first
field is the origin-zero active/corner window certificate; checked origin-zero
stacks are derived by
`l2c1OriginZeroCheckedStacksOfOriginZeroWindows`.
The same origin-zero Figure 16 surface now has decoder-step, global-label, and
source-label variants:
`FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations`,
`FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations`,
and
`FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations`.
These origin-zero-window wrappers now also project to the corresponding
`FinalOriginZeroTranslatedBox*ConstructionObligations` wrappers by first
recovering checked stacks from origin-zero active/corner windows and then using
the checked-stack/valid-box bridge.
The source-label final-input wrapper now uses that origin-zero translated-box
source-label projection directly instead of rebuilding the decoder-step route.
The global-label Figure 16 wrappers now use the same source-label translated-box
route after applying the global-to-source label-index bridge.
The reduction layer now also has direct source-specialized label-index
endpoints for Section 7 translated-box data:
`encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect`
and the L2C2/unencoded analogues.
The public Section 7 translated-box wrappers now use the translated-box
reduction endpoints directly for row-source, decoder-step, global-label, and
source-label variants. The older centered positive-box projections are still
available as compatibility conversions, but the theorem surface no longer
detours through them.
Their `toFinalReductionInputs` conversions now also use
`l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData` directly,
so the default final-input route matches the translated-box endpoint route.
Global-label final-input constructors for the checked-stack/layer-patch,
origin-zero translated-box, and Section 7 positive/translated-box routes now
lower through the source-specialized label-index target, keeping these wrappers
on the weakest generated-source assumption once the global primitive-recursive
proof is supplied.
There is also a more direct scaffold-facing final route:
`FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations` and its
decoder-step/global-label/source-label variants. These replace the compatible
Figure 16 macro-square field by the core assumption
`TilesPlane figure18ScaffoldTiles`; origin-zero active/corner windows still
supply the Section 7 board/free-line recognition, while the plane tiling
supplies translated active-corner boxes.
This has been split one step further:
`FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations` and its
source variants expose the actual Section 7 recognition premise directly,
namely `Section7BoardFreeLineActiveCornerInvariant` for the first audited L2
candidate. The origin-zero-window route is now just a specialization of this
board/free-line surface.
The indexed-active scaffold route has now been partially connected to this
interface: `L2C1IndexedActiveWindows` and `L2C2IndexedActiveWindows` imply the
corresponding local free-square window invariants. This proves the local
recognizability/free-square part of the Figure 18 scaffold route. The remaining
canonical board/free-line step is to upgrade local indexed-active recognition
plus Robinson's board geometry to the canonical free-site active/corner
invariant, or otherwise show that the indexed-active windows can be chosen on
Robinson's canonical free crossings.
The origin-zero target is now explicitly connected back to the indexed-active
route: generic origin-zero Figure 18 windows imply ordinary indexed-active
windows, and the two audited L2 candidates have named wrappers from
`L2C1OriginZeroWindows`/`L2C2OriginZeroWindows` to both indexed-active windows
and local free-square windows. Thus the current strong scaffold obligation
simultaneously feeds the canonical board/free-line surface and the local
recognizability surface.
The same origin-zero/scaffold-plane assumptions now also produce ordinary
`Figure18ScaffoldData.Certificate`s, hence `IsScaffold`, for both audited L2
candidates. This ties the last local-free-square window route to the existing
translated-box realization route: origin-zero windows supply recognizability,
while `TilesPlane figure18ScaffoldTiles` supplies the positive translated
active-corner boxes.
The origin-zero recognizability target has been factored once more into the
actual semantic obligation needed from Robinson geometry:
`L2C1OriginZeroCombinedActiveCornerWindows` and
`L2C2OriginZeroCombinedActiveCornerWindows`. These ask only that the decoded
Figure 18 scaffold site `table.combinedSite` is active throughout each
origin-zero square and that the lower-left decoded site is the corner. The
generic bridge reconstructs the indexed Figure 13 coordinates and payload
product witnesses automatically, yielding the existing `L2C*OriginZeroWindows`
interfaces.
The canonical Robinson-free-site target is now connected back to this same
origin-zero surface in the small module
`LeanWang.OllingerRobinsonCanonicalOriginZero`: canonical free-site
active/corner recognition implies decoded-site origin-zero active/corner
windows by choosing a Robinson level whose free-grid side is at least the
requested window size.  Section 7 exposes this as
`L2C1CanonicalFreeSiteRectActiveCorner`/`L2C2CanonicalFreeSiteRectActiveCorner`
and wrappers to both decoded-site and indexed origin-zero windows.  This keeps
the concrete scaffold proof focused on canonical Robinson crossings while
preserving the existing origin-zero reduction route.
The public final layer now exposes this canonical surface directly via
`FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations` and
the decoder-step/global-label/source-label variants.  These project through the
origin-zero scaffold-plane route, so the final theorem statement can now assume
canonical Robinson free-site active/corner recognition instead of the stronger
origin-zero window certificate.
The origin-zero scaffold-plane route now also projects directly to the
corresponding `FinalOriginZeroTranslatedBox*ConstructionObligations` wrappers:
Section 7 constructs
`l2c1OriginZeroTranslatedObligationsOfOriginZeroWindowsFigure18ScaffoldTilesPlane`
from origin-zero active/corner windows plus
`TilesPlane figure18ScaffoldTiles`, and the final row/decoder/global/source
wrappers route their endpoints through the origin-zero translated-obligation
surface.
The L2C1 canonical-free-site scaffold-plane global-label and source-label
wrappers now reuse the origin-zero source-label route instead of detouring
through the decoder-step or direct canonical-free-site source-code endpoints.
The checked-stack scaffold-plane global-label wrapper now follows that same
source-specialized origin-zero route after forgetting the global label-index
target.
The Section 7 reduction layer now has the same direct route:
canonical free-site active/corner recognition plus `TilesPlane
figure18ScaffoldTiles` constructs `L2C*RobinsonSection7BoardFreeLineTranslatedBoxData`,
ordinary `Figure18ScaffoldData.Certificate`s/`IsScaffold`, and both encoded and
unencoded position-source undecidability endpoints for the two audited L2
candidates.
The public final layer now also exposes checked-stack versions of the Figure 18
scaffold-plane route:
`FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations` and the
decoder-step/global-label/source-label variants.  These packages take finite
`L2C1OriginZeroCheckedStacks` directly, derive canonical free-site
active/corner recognition via
`l2c1ActiveCornerOfOriginZeroCheckedStacks`, and route the endpoints through
the existing origin-zero scaffold-plane wrappers.  This removes the need for
callers who already have checked stacks to restate the canonical recognition
obligation separately.
The same route is now named below `Final` as well: Section 7 has direct
checked-stack/scaffold-plane translated-box constructors, ordinary Figure 18
certificates, `IsScaffold` wrappers, and position-source undecidability
endpoints for both audited L2 candidates.  The generated-position wrapper layer
also exposes the source-specialized label-index versions with folded semantic
correctness already discharged.
The direct cofinal-square replacement for `TilesPlane figure18ScaffoldTiles`
has been removed from the public final surface because the standalone Figure 18
site-square problem is a diagnostic target, not the scaffold instantiation
route.  The proof-facing finite target remains Section 7 checked stacks plus
valid translated boxes or active-corner layer patches.

For build locality, the concrete Figure 18 reduction implementation is now
split at the Section 7 boundary: `LeanWang.OllingerRobinsonFigure18Reduction`
is a public import wrapper, `LeanWang.OllingerRobinsonFigure18Reduction.Core`
contains the generic Figure 18/folded-reduction adapters, and
`LeanWang.OllingerRobinsonFigure18Reduction.Section7` contains the scaffold
packages and proof-facing Section 7 routes.  Future concrete scaffold work
should prefer editing the Section 7 module so the earlier generic wrapper layer
stays cached.
The canonical/origin-zero bridge is also kept out of the giant Figure 13
transcription file for the same reason: changing this theorem surface should
rebuild only the small bridge module and downstream Section 7 wrappers, not the
audited raw Figure 13 data.

The split folded-compiler correctness modules and the split
`TM0FoldedPositionReduction` source/theorem wrapper modules are now free of
broad `noncomputable section` markers.  They rebuild successfully without those
markers, so future edits should keep these files executable/theorem-only unless
a specific declaration genuinely requires noncomputable data.

For finite local verification, avoid hand-proving hundreds of color matches. Instead:

- encode the finite tileset as Lean data,
- define the finite local predicates,
- use `native_decide` or reflection-style lemmas for exhaustive checks,
- keep a small number of human-readable lemmas explaining what the verified checks imply.

The goal is to make the large finite verification auditable without turning the proof into manual casework.

### Current Frontier

As of the current Lean surface, the final proof is still conditional, but the
conditions have been narrowed to two proof-facing fronts:

1. **Source reduction.**  Prove one generated position-code row target, ideally
   `TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec` or the weaker
   `TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec`.  The semantic
   part of `TM0FoldedReduction.PositionSourceObligations` is already discharged
   in `TM0FoldedPositionReduction.SourceObligations` by importing the folded
   compiler correctness theorem.  The remaining source work is the
   primitive-recursive, source-uniform descriptor-row construction.
   The source-specialized label-index target is now also exposed as equivalent
   to the generated position-code accumulator-step target, so either proof can
   feed the decoder-step theorem surfaces without an extra ad hoc bridge.
   The auxiliary `SourceStatementListNodup` gap is no longer a completely
   opaque list fact: `TM0Route.partrecStartedTM0StatementList_nodup_of_pairwise_disjoint`
   and
   `TM0FoldedReduction.sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint`
   reduce it to duplicate-free local TM1 statement supports plus pairwise
   disjointness of the support lists for distinct started TM1 labels.
   `TM0Route` now also exposes relabeling equalities for TM1 support lists:
   `tm1StmtSupportList_relabel`, `tm2to1TrNormal_relabel`,
   `partrecStartedTM1Machine_relabel`, and
   `partrecStartedTM1Machine_supportList_relabel`.  However the direct local
   raw-support `Nodup` route is not viable for the current enumeration:
   `TM0Route.tm2to1GoPopStmtSupportList_not_nodup` shows that the TM2-to-TM1
   `go pop` support list duplicates its return continuation.  The active
   generated-position source route should therefore avoid the older
   statement-list uniqueness package and target the row/label-index primrec
   surfaces directly.
2. **Scaffold instantiation.**  Prove the concrete Figure 13/Figure 16 Section
   7 scaffold package on the live route.  The preferred concrete surface is
   now
   `FinalFigure13L2C2BoardFreeLineLayerPatchSourcePositionCodeConstructionObligations`
   (or its row-source variant).  This asks for Robinson Section 7
   board/free-line active/corner recognition and finite active-corner layer
   patches for the audited L2C2 Figure 13 scaffold.  The board/free-line
   hypothesis supplies compatible routed free grids, while the layer patches
   supply the active-corner realization; together they project to
   `FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations`.
   The neighboring tileable-box route remains available as
   `FinalFigure13L2C2BoardFreeLineTileableBoxSourcePositionCodeConstructionObligations`:
   tileable Figure 18 scaffold boxes imply valid translated boxes for L2C2,
   and board/free-line active/corner recognition implies the canonical
   active/corner recognition used by the valid-box endpoint.  The older
   `FinalL2C2CheckedStackValidTranslatedBox*` wrappers now pass through this
   canonical-active-corner/valid-box surface: checked stacks provide canonical
   active/corner recognition directly, while their existing valid-box field is
   already above the tileable-box target.

   The tileable-box route now also projects back to the board/free-line
   layer-patch frontier, for both source-label and row-source wrappers.  This
   keeps the finite tileable-box diagnostic path connected to the same
   Section 7 layer-patch endpoint as the decoded-window/valid-box path.

   The preferred board/free-line/layer-patch frontier now also has direct
   one-row, bounded-interior, decoder-step, and global-label source wrappers,
   all projecting through the source-label package.  Thus any live source-side
   target can feed the paper-facing Section 7 scaffold surface without
   detouring through checked-stack-specific packages.

   The L2C2 checked-stack/layer-patch packages now project directly to this
   same Figure 13 board/free-line/layer-patch surface, again for row-source,
   decoder-step, global-label, and source-label wrappers.  Thus the current
   finite checked-stack target no longer has to detour through valid translated
   boxes to reach the preferred scaffold-facing endpoint.

   The remaining first-candidate and L2C2 Figure 16 compatible final-package
   structures are now explicitly proved uninhabited in `LeanWang.Final`, via
   the refutations of `Figure18CanonicalCheckedRecognizedCompatibleMacroSquares`
   and `Figure18CanonicalCheckedRecognizedCompatibleLevelChecks`.  They remain
   useful historical diagnostics, but they should not be treated as live final
   theorem frontiers.
   Their positive public `domino_problem_undecidable` aliases have been
   removed, leaving only the explicit `not_*` diagnostics for these refuted
   routes.

   The same L2C2 checked-stack/layer-patch public endpoint now also exposes
   generated one-row and bounded-interior source-row wrappers, matching the
   weaker source targets already available for the first L2 route.
   The split finite-scaffold entry point now exposes the same weaker source
   targets directly as
   `encoded_domino_problem_undecidable_of_l2c2CheckedStacksAndLayerPatchesOneRows`,
   `domino_problem_undecidable_of_l2c2CheckedStacksAndLayerPatchesOneRows`,
   `encoded_domino_problem_undecidable_of_l2c2CheckedStacksAndLayerPatchesBoundedRows`,
   and
   `domino_problem_undecidable_of_l2c2CheckedStacksAndLayerPatchesBoundedRows`.
   Thus the finite Figure 13/Figure 16 target can keep checked origin-zero
   stacks and active-corner layer patches as separate fields while using the
   currently most accessible source-row obligations.
   The lower position-reduction layer now also has matching first-candidate
   Section 7 board/free-line layer-patch one-row and bounded-row correctness
   wrappers, so the L2C1 and L2C2 finite-check-facing scaffold routes expose
   the same source-row frontier.
   The lower `TM0FoldedPositionReduction.Theorems` layer now exposes the
   matching L2C2 decoder-step, one-row, and bounded-interior checked-stack
   wrappers with `positionProgramData` correctness discharged; the older
   Figure 18 position module continues to own the global/source/interior
   wrappers.

Do not spend more effort on the diagnostic raw-boundary or canonical checked
Figure 16 level-check routes.  The shifted raw-boundary board-level interfaces,
the raw Figure 13 plane/box routes, and
`Figure18CanonicalCheckedRecognizedCompatibleLevelChecks` are formally refuted
in Lean.  The live scaffold work should stay on the Section 7 translated
positive-box/layer-patch interfaces.

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
