# Wang Tiling Undecidability Formalization Plan

## Goal

Prove in Lean, using Mathlib's computability library, that both the encoded and
unencoded plane-tiling predicates for finite Wang tilesets are undecidable:

```lean
¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n))
¬ ComputablePred (fun T : TileSet => TilesPlane T)
```

The public conditional versions are already proved in `LeanWang.Final`. The
only remaining hypothesis for the final channel-aware construction is a
concrete proof of `IsRoutedScaffold`.

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

The reduction now consumes a four-field `UniversalMachineCertificate`: one
constant finite table program, a computable source-dependent input word, a
support proof, and the halting equivalence. All machine-to-Wang and scaffold
reasoning depends only on this certificate. The existing folded construction
is confined to one witness and can be replaced independently by a smaller
fixed-TM0 simulation.

`TM0FixedDirectProgram` begins that replacement. It emits semantic folded rows
directly over the finite reachable-label support and proves their transition
lookup without position codes or generated descriptor decoding. The remaining
work is the generic folded configuration simulation, after which this direct
program replaces the legacy certificate witness. Both the matching-row and
no-matching-row lookup theorems are complete.

1. `UniversalCode.universalCode` evaluates a supplied encoded
   `Nat.Partrec.Code` and input.
2. `UniversalTM0.code` translates this universal evaluator once through
   Mathlib's `ToPartrec`, TM2, TM1, and TM0 route.
3. `UniversalTM0.input c` writes `Nat.pair (encode c) 0` as the varying initial
   tape. Its construction is computable.
4. `TM0DirectInput` folds that finite word and starts the fixed simulation
   control directly on it. No machine initializer writes or rewinds the input.
5. `MachineInputTiles` forces the finite word in a position-tagged bottom Wang
   row, followed by one self-looping blank-tail tile. It proves seeded
   quarter-plane tiling equivalent to nonhalting on that input.
6. `MachineInputTilesData` computes the finite tile list and seed, while its
   membership theorems identify them with the semantic history tiles.
7. `UniversalDirectReduction.fixedDominoData_correct` proves that this
   computable Wang instance tiles exactly when
   `Nat.Partrec.Code.eval c 0` is undefined.
8. `UniversalFoldedReduction` exposes that direct construction to the existing
   scaffold reductions; the generated input-specific initializer is no longer
   in this public reduction path.
9. The direct `IsRoutedScaffold` reduction preserves the horizontal and
   vertical channel constraints used by the Robinson board construction.
10. Mathlib's `ComputablePred.halting_problem` yields both undecidability
   theorems.

There is no remaining source-uniform compiler, descriptor decoder, or generated
position-row obligation or input-specific machine control in the final
reduction. The fixed TM0-to-Post simulation remains the only machine compiler.

## Completed general tiling infrastructure

- Wang-tile and tileset encodings, finite rectangle search, and matching rules.
- Centered-box and square compactness for plane tilings.
- Fixed-corner square compactness for seeded quarter-plane tilings.
- Machine-history Wang tiles and the fixed-domino correctness theorem.
- The abstract `Scaffold` / `IsScaffold` reduction.
- A finite transcription of Figure 13 and Figure 16, including the corrected
  104 component triples in `figures/fig13-human.tsv`.
- Substitution-generated plane tilings for the corrected 104-symbol alphabet.
- The corrected Figure 16 `L2b` extension (`R1`, not `R3`) and a 104-tile Wang
  encoding that retains both thick-line boundary lanes.
- Finite certificates that every substituted block is valid and substitution
  preserves and reflects horizontal and vertical compatibility.
- Proposition 8's finite `4 x 4` test: all 328 extendable well-behaved central
  blocks are substitution images.
- A proposition-level local recognizability theorem: every valid typed `4 x 4`
  neighborhood with the distinguished central phase has a unique `Fin 104`
  parent whose four children are its central `2 x 2` block.
- Global desubstitution: every valid corrected-Ollinger plane is, up to one of
  four parity choices, the Figure 16 substitution of another valid plane.
- An infinite typed desubstitution tower, retaining the parity origin and four
  exact child equations between every pair of consecutive valid planes.
- A native-checked primitivity certificate: every corrected tile type occurs
  below every parent after five substitutions, so board patterns recur
  uniformly in every hierarchy.
- A tower-occurrence theorem turning that finite reachability into actual fine
  plane coordinates; in particular every corrected tile type occurs in every
  valid plane tiling.
- A lossless decoder from ordinary `TileIn tileSet` plane tilings to typed
  `Fin 104` planes, so the hierarchy applies directly to the public Wang-tiling
  predicate.
- A finite red-port topology and native certificate that every depth-two
  supertile contains a complete red rectangular cycle, providing a uniform
  seed for the nested Robinson boards.
- Finite local red-line expansion certificates and a proposition-level
  iteration theorem proving those red cycles double under every further
  substitution, hence occur at unbounded scales.
- A coordinate embedding theorem identifying each abstract grid refinement
  with the contiguous child block at the corresponding parity origin in an
  actual hierarchy tower.
- An iterated embedding theorem composing those parity origins through any
  tower depth and identifying the resulting fine-plane quadrant with the
  corresponding iterated refinement.
- A concrete-plane red-board theorem: every valid corrected-Ollinger plane has
  red rectangular cycles at explicit origins and unbounded `2^level` scales.
- The red-board seed is uniform for all 104 parents: its depth-two corners are
  `(1,1)` and `(3,3)`, yielding canonical scaled corners at `2^level` and
  `3 * 2^level` in every plane.
- A corrected 416-tile quarter subdivision with certified distinctness,
  decoding, and checkerboard phase transitions, replacing all old `Fin 92`
  Figure 18 site types.
- A global quarter-regrouping theorem: every valid typed quarter plane has a
  southwest parity origin and decomposes exactly into four quadrants of one
  corrected parent index at every selected `2 x 2` macrocell.
- An ordinary-Wang decoder for quarter planes, including reflected macro-boundary
  matching, so every valid 416-tile plane recovers a valid 104-index hierarchy
  together with exact block equations.
- A quarter-level red-path geometry: the two thick-line lanes are identified
  with literal tile quarters, and a finite certificate fixes every depth-two
  board's oriented boundary as `R1` south, `R3` north, `R0` west, and `R2`
  east, with all four corner turns facing inward.
- A finite directed obstruction-signal layer over the 416 quarter tiles,
  implementing Robinson's outer-edge emit-or-absorb and inner-edge
  absorb-only rules. Every tiling of this layer provably projects to a valid
  corrected quarter plane and a matching plane of locally allowed signals.
- A one-dimensional corridor calculus for the concrete signal layer: signal
  flow is constant between consecutive red boundaries, two inner-facing
  endpoints force a clear corridor, and either outer-facing endpoint forces
  an obstructed corridor.
- A concrete `Scaffold` over the corrected signal tiles. Its active predicate
  reads the paired edge colors and is primitive recursive; the distinguished
  all-clear corner is a certified member of the scaffold tileset.
- A combined-plane decoder retaining both scaffold and payload layers. It
  recovers a valid signal tiling, regroups its quarter layer into a valid
  corrected index plane and hierarchy, and records that clear sites carry
  payload tiles while the distinguished clear corner carries the seed.
- An oriented red-cycle invariant strengthening every board side to its exact
  thick lane (`R1`, `R3`, `R0`, or `R2`), with finite substitution
  preservation certificates and a concrete-plane theorem giving such boards
  at every unbounded hierarchy scale.
- An exact embedding from parent coordinates and quadrants into the decorated
  quarter plane. Oriented board-side facts now specialize directly to the
  concrete inner/outer signal endpoint rules at those quarter coordinates.
- A finite `104 x 4` free-cell certificate: below every parent child, an
  `8 x 8` quarter gadget has inward-facing boundaries at local coordinates
  `3` and `6` and boundary-free lanes `4` and `5`, with child parity selecting
  a canonical clear crossing.
- A scale-independent embedding of that gadget through arbitrary refinements.
  At every depth `d >= 5`, any coarse index grid contains a Cartesian family
  of `2^(d-3)` selected coordinates in each direction, each with the certified
  inward boundaries and clear interior lanes.
- A signal-theoretic free-crossing theorem: local allowance and edge matching
  force every selected crossing in that Cartesian family to carry the exact
  all-clear state, independently of all emit/absorb choices elsewhere.
- A role-sensitive routed-scaffold combination replacing the insufficient
  Boolean active/inactive payload interface. Horizontal and vertical channel
  roles restrict the complete payload palette to the corresponding wire
  equality, active crossings carry source tiles, and corner crossings carry
  the seed. The resulting finite tileset construction is primitive recursive.
- A concrete local role decoder for Robinson signal tiles. The two clear-edge
  direction bits classify every tile as a horizontal channel, vertical
  channel, active crossing, or inactive site; this decoder is primitive
  recursive, agrees exactly with the all-clear crossing predicate, and leaves
  the corner role reserved for a later finite marker decoration.
- A generic decoder for planes over any routed scaffold product. It recovers
  valid matching scaffold and payload layers and exposes complete-palette,
  horizontal-wire, vertical-wire, source-tile, and fixed-seed facts according
  to the decoded role at each site.
- A concrete routed-product decoder for Robinson signal planes, recovering the
  corrected quarter regrouping, parent index plane, and infinite hierarchy
  while retaining source-tile membership and directional payload-wire facts.
  This is the forward decoder that supersedes the older Boolean combined-plane
  route.
- An actual-plane instantiation of the free-crossing theorem. Exact quarter
  coordinates below every hierarchy tower origin form the abstract valid
  signal grid, so every selected crossing at every depth `d >= 5` has the
  active route role and therefore carries a tile of the source tileset.
- A finite diagnostic showed that the preceding obstruction layer cannot yet
  be the final scaffold: it decorates every red wire, leaving only a
  constant-width free set in canonical growing boards. The CIRM construction
  first splits red wires into light and dark shades and allows light wires to
  cross only dark wires. Thus the unshaded signal/free-crossing modules are
  retained local lemmas, not the final square-routing argument.
- The missing finite light/dark red-wire layer is now defined over corrected
  quarter tiles. It records exact red-path edge incidence, propagates a shade
  through straight paths and corners, requires crossing paths to have opposite
  shades, and decodes every valid shaded tiling back to a valid quarter plane
  with matching shade edges. A finite `416 x 81` audit proves that every local
  quarter site has an admissible shade state. Proof-facing lemmas expose shade
  equality on straight paths and all corner turns, opposite shades at
  crossings, and literal shade equality across neighboring Wang edges. An
  abstract valid shade grid and generic finite horizontal/vertical path
  propagation lemmas isolate the forthcoming cycle-color proof from Wang-tile
  product encodings.
- The universal depth-two red board has certified quarter-level shade geometry.
  A symbolic path proof now forces any shade on its southwest edge around its
  straight sides and corner turns to all four board corners, establishing the
  uniform-color seed for the scaled cycle argument.
- The shade geometry and propagation theorem now hold for every oriented red
  cycle, not just the seed: index-board coordinates map to exact inward quarter
  corners and contiguous `R0`/`R1`/`R2`/`R3` paths, and a shade on one corner
  is forced around an arbitrarily large cycle to all four corners. Red-edge
  presence then supplies such a shade, so every oriented board has an actual
  uniform light/dark corner shade. Prefix propagation extends that shade to
  both edge labels of every strict interior quarter on all four board sides.
- In the same `level + 2` refined grid, the canonical scale-`2^level` board and
  a board seeded one refinement later at scale `2^(level-1)` are both
  certified. Their coordinate inequalities prove that their sides cross, while
  their sizes differ by only a factor of two. Shade paths are propagated to
  their concrete intersection, where the local crossing rule forces the two
  uniform board shades to differ. Thus both light and dark boards occur at
  unbounded scales. This is instantiated in every decoded routed product plane:
  at each hierarchy level, one of the two boards is uniformly light and has
  scale at least `2^(level-1)`.
- The shade grid is instantiated at exact coordinates in every final routed
  product plane. Quarter regrouping supplies a valid natural shade grid below
  any parent coordinate, and the hierarchy embedding transports it through
  arbitrary refinement depths.
- The obstruction alphabet is rebuilt over that shade layer. Light red paths
  obey Robinson's outer-edge emit-or-absorb and inner-edge absorb-only rules;
  dark paths are transparent. Every valid tiling projects to both a valid
  shaded quarter tiling and a matching obstruction-signal plane, and hence to
  the corrected quarter hierarchy. Public local lemmas reduce light paths to
  the original oriented-border rule, reduce dark paths to transparent
  transmission, and expose literal matching of decoded signal flows.
- The shaded-border selector is factored by explicit component and quadrant.
  Finite local proofs certify that all four uniformly light board corners are
  recognized with their exact inward horizontal and vertical signal
  directions, without unfolding hierarchy data.
- The final shaded obstruction alphabet is now a concrete `RoutedScaffold`.
  Its primitive-recursive decoder classifies inactive, horizontal, vertical,
  and active payload roles while retaining the shade layer needed for the
  growing free-board proof. An all-clear occurrence of the distinguished
  `cornerQuarter` is promoted to the `corner` role, so its payload is forced to
  the supplied seed; all other all-clear sites remain active.
- A final routed-product plane decoder exposes all layers simultaneously:
  matching payload tiles and directional wires, light/dark red paths,
  obstruction signals, the corrected quarter plane, its regrouped parent
  plane, and an infinite hierarchy tower.
- The shade and obstruction-signal decoders are now exact, not merely
  choice-equivalent at the encoded Wang-tile level: injectivity of both finite
  encodings identifies nested decoder outputs. Consequently every final routed
  plane supplies one natural quarter grid carrying a valid shade assignment,
  locally allowed shaded obstruction signals, and matching signal edges at the
  same coordinates.
- Every strict quarter along all four sides of an arbitrary uniformly light
  oriented board is now recognized as the corresponding inward-facing signal
  endpoint. The local signal rule therefore gives the exact outer-edge
  nonempty and inner-edge nonemission constraints uniformly along each side.
- Free rows and columns are formalized as strict board lines crossed by no
  selected inner light border. Corridor propagation from the two light outer
  sides proves that every obstruction edge on a free line is empty. A free-row
  and free-column crossing therefore has the literal clear signal state, the
  active routing role, and a retained payload tile from the source tileset.
- The universal oriented depth-two board is no longer restricted to the block
  at the origin. A translation theorem embeds it below every coarse-grid
  coordinate, and iterated refinement exposes every such translated board at
  arbitrary scale. This supplies the full family of nested boards needed for
  Robinson's free-line recurrence.
- For every translated scale-`k` board, all four scale-`k-1` corner boards are
  now constructed in the same refined grid. The appropriate north/south child
  side crosses the appropriate west/east parent side at certified strict
  interior coordinates, so shade propagation and the local crossing rule
  force every child shade to be opposite its parent. Two applications give
  the same-shade scale-`k-2` descendants used by the free-line recurrence.
  Uniform board shades are unique, so the opposite-shade result applies
  directly to arbitrary parent and child shade certificates. The two-color
  involution also makes this constructive: any parent certificate produces a
  certificate for every corner child with the literal opposite shade. Applying
  this construction twice produces all sixteen two-level corner descendants
  in the same refined grid with the grandparent's original shade.
- The four two-level descendants that lie strictly inside the parent are
  identified by base-4 block digits `1` and `2`. Each has a certified board
  interval strictly contained in the parent and a constructive uniform-shade
  certificate equal to the parent's shade. These are exactly the recursive
  inner obstructions in Robinson's free-line count. Their two intervals in
  either axis are also certified to be ordered and pairwise disjoint, with
  nonempty gaps to each parent side and between the two inner boards.
- A fresh finite audit refuted the proposed hypothesis-free center-line base
  case: raw center rows and columns can carry perpendicular red paths. The
  corrected theorem assumes a valid shade grid and a light parent board,
  proves every such center segment reaches the south or west parent boundary,
  and uses the crossing rule to force that segment dark. Thus every translated
  scale-2 light board has a certified singleton `FreeGrid`, without assuming
  that the raw center geometry is empty.
- The Figure 18 free-line coordinates are now represented by a strictly
  increasing recursive offset list. Retaining the two enclosing border
  coordinates, every offset `x` expands to `4x, 4x+1` when `x` is even and to
  `4x+2, 4x+3` when `x` is odd. Removing the borders gives `6, 14, 30, ...`
  candidate rows and columns, with the proved recurrence `F(k+1) = 2F(k)+2`.
- These offsets now have a typed index API with proved membership, strict
  monotonicity, interior bounds, and enough cardinality for every requested
  finite square. A generic constructor packages semantic freedom at all
  indexed offsets into an ordered `FreeGrid`. The six audited graph lines
  instantiate this constructor at depth one in every translated parent block,
  so the remaining induction step is precisely a two-refinement lift of the
  row and column graph certificates along `expandOffset`.
- Robinson's Section 7 proof identifies the cleaner induction invariant: the
  whole free-line pattern repeats periodically inside the next board, rather
  than individual quarter-graph ports refining spatially. The exact Lean list
  decomposition is now proved: a successor pattern consists of the new first
  side line, both descendants of every old offset, and the new last side line.
  Consequently every offset is strictly below the removed outer endpoint.
  The semantic step should prove this whole-pattern periodicity directly and
  avoid any retained depth-two exhaustive search.
- The semantic recurrence is now stated for both scale parities. This is
  necessary because the crossing-board theorem guarantees a light board at
  level `L` or `L-1` but does not pin which parity is light. The even depth-one
  base is discharged by the existing finite graph certificates. For either
  parity, a base certificate plus one phase-preserving two-substitution
  periodicity lemma now yields `OffsetsFree` at every depth and packages it as
  an ordered `FreeGrid`. The odd parity now starts at the genuinely minimal
  level-one board: a cached all-parent graph audit proves its two scaled
  depth-zero offsets free and graph-search soundness exposes `holds_odd_zero`.
  Thus the common periodic successor theorem is the only remaining
  board/free-line recurrence obligation.
- Red-wire propagation is factored through a finite port graph. Straight
  segments, matching edges, and corner turns preserve shade; switching wires
  at a crossing reverses it. Every graph path therefore proves shade equality
  or opposition from its accumulated crossing parity, giving the recursive
  geometry proof a compact certificate language. A Boolean move-list checker
  is proved sound for this graph, allowing native finite geometry searches to
  return ordinary proposition-level path proofs. Link and path certificates
  also translate from a refined local block to its exact absolute coordinates
  in an arbitrary refined grid, preserving crossing parity.
- Bounded graph search itself is proved sound: every returned node is reached
  from the requested start by a proposition-level parity path. Finite template
  discovery is therefore outside the trusted boundary, while successful
  results can be consumed directly by the recursive geometry proof. The
  array-backed multi-source flood is sound as well, so all candidate segments
  below one parent can share a single traversal from its board-side ports.
- Strict ports along all four sides of a uniformly shaded oriented board are
  represented explicitly. Path soundness now gives the central semantic rule:
  every odd-parity path from a light board side ends on a dark edge, ready to
  discharge the shaded obstruction selector at candidate free coordinates.
- Row and column graph-certificate predicates isolate the remaining geometry:
  each perpendicular red segment must have an odd path from a board-side port.
  Under a valid shade grid and a light enclosing board, these certificates are
  now proved to imply the original `IsFreeRow` and `IsFreeColumn` predicates,
  including the cases where a corner path exposes only one endpoint edge.
- A native finite audit checks those graph certificates for all six first-level
  Figure 18 offsets and all 104 possible parent tiles. Its result is isolated
  in cached audit modules, then converted by the proved graph-search soundness
  theorem into an ordered size-6 `FreeGrid` for every valid light canonical
  board. Downstream edits rebuild this proof-facing wrapper in seconds without
  rerunning the exhaustive search.
- For every parent tile, the third audited row and column cross at one of
  exactly four distinguished southwest quarters, with indices `0` through `3`.
  No other audited crossing has one of those types. Dropping the first two rows
  and columns therefore gives a checked `4 x 4` free grid whose lower-left
  payload is forced to the seed by the routed corner marker.
- Bounded graph-search soundness now retains bounds for every intermediate
  port. Substitution locality transports those bounded paths from the constant
  finite audit to any actual depth-four refined block with the same parent.
  Thus every light board in an arbitrary hierarchy carries the same
  absolute-coordinate marked `4 x 4` free grid, independently of parent type.
- Iterated refinement is now proved equivariant under arbitrary coarse-grid
  translations, including exact quarter-component and obstruction-selector
  transport.
- Free rows and columns themselves are translation-equivariant. Restricting a
  shade grid to an aligned coarse block and refining locally yields a free line
  exactly when the `2^depth`/quarter-scaled translated line is free in the
  global refinement. This is the induction interface for reinserting recursive
  inner-board free lines into their parent board.
- Aligned restrictions of a valid combined shade/signal grid are again valid,
  and uniform board-shade certificates transport across the same restriction.
  An ordered `FreeGrid` now records finite lower-bound witnesses for free rows
  and columns, and every selected crossing is signal-clear.
- Free rows and columns inside a bounded board now have Boolean tests proved
  equivalent to the proposition-level definitions and exact finite-set
  enumerations. Every ordered `FreeGrid` witness injects into these sets, so a
  size-`n` recursive witness certifies at least `n` actual free rows and columns
  for the later consecutive-channel routing argument.

## Remaining scaffold proof

The final shaded obstruction tiles and their `RoutedScaffold` instance are
complete. The remaining theorem must prove its forward and backward
square-routing properties. Keep this work independent of the machine
reduction. The older unshaded `Scaffold` and routed instances remain useful as
intermediate local decoders, but are not the final reduction interface.

The routed decoder now proves that every clear free crossing carries a tile of
the source set, and that a clear crossing carries the seed exactly when its
decoded quarter is `cornerQuarter`. The forward construction must choose each
large free grid with such a crossing at its lower-left corner.

### 1. Obtain arbitrarily large free squares

The shade decoration already selects a noncrossing family of red borders with
unbounded light members, and Robinson obstruction signals are instantiated on
exactly those borders. Next prove the board/free-line recurrence on the
combined natural grid: a uniformly light board forces sufficiently many clear
rows and columns in its interior. Their crossings must have active routing
role. Use the unbounded light boards to obtain arbitrarily large recognizable
active squares with a distinguished lower-left corner.

### 2. Prove backward realization

Construct scaffold tilings containing active-corner boxes of every finite size,
or equivalently finite layer patches that compactness assembles into the
required plane tiling. Show arbitrary payload tiles can be routed through the
active square and obstruction channels.

### 3. Package and finish

Bundle the forward and backward results as `IsRoutedScaffold S`, apply
`LeanWang.encoded_domino_problem_undecidable_of_routed` and
`LeanWang.domino_problem_undecidable_of_routed`, then run:

```bash
lake build
rg -n "sorry|admit|axiom" LeanWang
git diff --check
```

The final theorem should have no hypotheses and no source-dependent machine
infrastructure.
