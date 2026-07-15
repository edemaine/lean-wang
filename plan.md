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

`UniversalTM0Semantic` applies Mathlib's `ToPartrec.Code.exists_code` directly
to the universal partial function, relabels that one fixed evaluator, carries
Mathlib's native finite supports through TM2, TM1, and TM0, and proves the
varying binary input primitive recursive. The direct tableau folds the
two-sided tape into paired cells and applies the fixed TM0 instruction set as a
radius-one local rule. No extra Post machine, table program, source compiler,
or descriptor decoder occurs in the retained reduction.

1. `UniversalCode.universalEval` evaluates a supplied encoded
   `Nat.Partrec.Code` and input.
2. `UniversalTM0Semantic.code` chooses one `Turing.ToPartrec.Code` for this
   function using Mathlib's completeness theorem, then uses Mathlib's
   finite-support TM2-to-TM1-to-TM0 transformations.
3. `UniversalTM0Semantic.input c` writes `Nat.pair (encode c) 0` as the varying
   initial tape. Its construction is computable.
4. `UniversalTM0TableauCells` and `UniversalTM0TableauDynamics` define the
   finite paired-cell alphabet and its deterministic radius-one update.
5. `UniversalTM0TableauInitial` forces the input in a position-tagged bottom
   Wang row followed by one self-looping blank-tail tile.
6. `UniversalTM0TableauDecode` proves that every seeded tiling is the unique
   nonhalting TM0 history; together with the forward history construction this
   gives the exact seeded quarter-plane equivalence.
7. `UniversalTM0TableauData` computes the finite tile list and seed, so the
   resulting Wang instance tiles exactly when
   `Nat.Partrec.Code.eval c 0` is undefined.
8. `UniversalTM0Reduction` exposes that construction to the existing
   scaffold reductions.
9. The direct `IsRoutedScaffold` reduction preserves the horizontal and
   vertical channel constraints used by the Robinson board construction.
10. Mathlib's `ComputablePred.halting_problem` yields both undecidability
   theorems.

There is no remaining source-uniform compiler, descriptor decoder, generated
position-row obligation, code-parametric support-list construction, or
input-specific machine control in the final reduction. More than one hundred
thousand lines of the obsolete route have been deleted. The retained fixed-TM0
tableau consists only of native finite supports, the folded alphabet and tape
geometry, direct semantic transition rows, and their step/halting simulation.

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
  so the remaining induction step is a weighted two-refinement projection of
  the complete row and column certificate family.
- Robinson's Section 7 proof identifies the cleaner induction invariant: the
  whole free-line pattern repeats periodically inside the next board, rather
  than individual quarter-graph ports refining spatially. The exact Lean list
  decomposition is now proved: a successor pattern consists of the new first
  side line, both descendants of every old offset, and the new last side line.
  Consequently every offset is strictly below the removed outer endpoint.
- The recurrence is now stated for both scale parities. This is
  necessary because the crossing-board theorem guarantees a light board at
  level `L` or `L-1` but does not pin which parity is light. The even depth-one
  base is discharged by the existing finite graph certificates. For either
  parity, a base certificate plus one phase-preserving two-substitution
  periodicity lemma now yields `OffsetsFree` at every depth and packages it as
  an ordered `FreeGrid`. The odd parity now starts at the genuinely minimal
  level-one board: a cached all-parent graph audit proves its two scaled
  depth-zero offsets free and graph-search soundness exposes `holds_odd_zero`.
  Both bases now retain `GraphHolds`, rather than immediately discarding their
  paths into semantic freedom.
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
- The first two-substitution refinement certificates are finite and checked
  for all 104 parents. Every old quarter component is retained in the
  southwest `2 x 2` corner of its refined `8 x 8` macrocell, and every live
  east or north port there has an even-parity path to the matching external
  macrocell port. These local connectors are the basis for lifting recursive
  odd-path certificates without rerunning graph search at every depth.
- A side-sensitive sparse port embedding now composes those connectors across
  neighboring macrocells. Every red-graph `Link` constructor, including
  matching edges and parity-reversing crossings, lifts through two
  substitutions to a path with exactly the same parity. Induction therefore
  lifts arbitrary finite path certificates at every recurrence depth.
- A line-by-line projection was rejected by a finite diagnostic: some new red
  components connect to a different old free line. A full-board depth-two
  audit succeeds, and the correct weighted whole-pattern flood also succeeds:
  outer-cycle sources begin even, old free-line sources begin odd, and every
  new candidate is reached odd. `WeightedSource`, `ProjectsTo`, and
  `PatternProjection` encode exactly this invariant. The generic theorem
  `certificates_of_projection` lifts such a projection through two
  substitutions, while `graphPeriodicStep_of_projectionStep` reduces the
  recurrence to the concrete geometric `ProjectionStep` alone.
- Both finite bases now audit endpoint presence in addition to odd path
  reachability. `LiveRowCertificate` and `LiveColumnCertificate` package the
  actual endpoint as a `WeightedSource`; sparse refinement transports both its
  path and liveness. `GraphHolds` retains these live certificates at every
  depth, and `liveCertificates_of_projection` closes the invariant under a
  concrete projection step.
- `ProjectsTo.ofCyclePath` and `ProjectsTo.ofOddSourcePath` separate the two
  admissible local source cases: an odd tail from the enclosing cycle, or an
  even tail from an old live free-line endpoint. Row and column elimination
  lemmas consume retained certificates without choosing which side endpoint
  the finite geometry reaches.
- `mem_freeOffsets_succ_cases` and `PatternProjection.ofSuccOffsets` reduce
  the concrete recurrence to vertical and horizontal versions of three finite
  quotient cases: the left side line, the two children of each old free
  offset, and the right side line. A disposable weighted graph probe checked
  the representative even `1 -> 2` and odd `0 -> 1` transitions: every live
  target is reached with total odd parity; offsets `30,31` (even phase) and
  `7` (odd phase) have no perpendicular target segments. The per-old-line
  strengthening is false for two degenerate groups, so the retained quotient
  obligation intentionally permits routing through the whole old pattern.
- Robinson's original Section 7 argument (`robinson.pdf`, pp. 203-204) is a
  periodic geometric count: the middle free-line pattern repeats exactly and
  the two half-patterns repeat at the sides. A raw-empty-line probe shows why
  the light/dark decoration cannot be discarded in this formalization: at
  depths one through three the even phase has only two geometrically empty
  candidate offsets and the odd phase only one.
- `RedShadeGraphWeightedSearch` now implements the whole-pattern audit
  faithfully. Each source carries its already-known outer-cycle parity;
  weighted flood soundness cancels that initial weight and returns an ordinary
  proposition-level path. `projectsTo_of_weightedNode` turns any reached node
  of total odd parity directly into `ProjectsTo`. A proof-producing quotient
  audit must still retain the chosen source descriptor (or certify both live
  endpoint sides), because a row/column certificate existentially chooses its
  endpoint.
- `ShadedFreeLineProjectionCandidates` resolves that endpoint choice without
  trusting search. A physically live executable candidate is backed by the
  retained source chosen for the same row or column; if the sides differ, a
  straight even link connects them before refinement. `CandidateFamily`
  packages cycle, row, and column candidate lists with this backing proof, and
  any total-odd weighted node reached from such a family yields `ProjectsTo`.
- `ShadedFreeLineProjectionSourceLists` supplies the executable lists used by
  that package: all strict ports of the enclosing cycle, and exactly the live
  endpoints of perpendicular components on each retained row and column.
  Generic membership proofs turn these lists into backed `Family` values from
  a canonical cycle and the corresponding live certificates.
- The proof-carrying `patternFamily` now has `patternCandidates` as its
  candidate field definitionally. Finite quotient audits can evaluate this raw
  list without constructing certificate proofs, while
  `patternFamily_candidates` reconnects the same data to its backing theorem.
- The border substitution now factors through the `(thin, thick)` component
  pair; a finite theorem proves all 104 child symbols agree with this factor,
  and induction lifts the equality through every refinement depth. There are
  only 56 reachable border states. Canonical representatives preserve the
  thick component, so black-layer variants can be erased from future geometry
  quotients.
- The border quotient now preserves the complete executable red-graph
  observation: local components, live ports, move validity, weighted flood
  results, and raw row/column source candidates. `CoverageStep` factors through
  a proof-free `RawCoverageAt`, and `coverageStep_of_canonicalCoverage` reduces
  its parent cases from 104 tile indices to the 56 canonical border-state
  representatives. The remaining quotient work is the unbounded depth
  parameter, to be discharged by a finite periodic audit or an induction on
  the border substitution.
- Coverage audits now use a lightweight `(port, parity)` flood with a separate
  soundness proof; executable nodes no longer retain unused reverse path lists.
  `BorderCoverageAudit.coverageCheck_sound` converts one accepted finite flood
  into `RawCovers`. Full-board audits remain diagnostic rather than the final
  proof method: even the first all-state board is too large to serve as a
  maintainable certificate, confirming that the next proof must localize the
  successor offset cases to bounded substitution neighborhoods.
- The successor-coordinate arithmetic is now localized: every child of an old
  free-line offset is at signed distance at most six from the sparse copy of
  its parent line, uniformly in the phase and depth. The new left side line is
  one or two cells right of the sparse west boundary, and the new right side
  line is one or three cells left of the sparse east boundary. Thus all local
  path templates need inspect only a fixed-width strip; their geometry does
  not grow with the Robinson board.
- `BorderCoverageLocalStep.LocalProjectionStep` splits the remaining semantic
  recurrence into exactly six template families: left, child, and right in
  each orientation. `graphPeriodicStep_of_localProjectionStep` reconnects
  those bounded cases to the unbounded free-grid induction via the proved
  successor-offset decomposition.
- `BorderCoverageLocalAudit` now supplies sound `8 x 8` route checks for cycle
  and retained sources in either orientation. The first audits confirm that a
  side target may require the intersecting retained column/row source in
  addition to the outer-cycle source. Thus the finite template state must
  record the local row and column source classes together, matching the
  whole-pattern invariant rather than treating lines independently.
- `patternFamily` concatenates the cycle and every retained row/column family
  into one executable source set. `Family.CoversPattern` is now the sole
  concrete weighted-search obligation, and `projectionStep_of_coverageStep`
  proves that its uniform phase/depth instance closes the original
  `ProjectionStep` recurrence.
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
- A finite reachable-state certificate now selects compatible shade blocks
  through every `4 x 4` substitution step. Iterating its total child operation
  constructs valid shaded supertiles of side `2 * 4^level` at every depth.
- Every finite valid shaded rectangle admits a matching obstruction-signal
  decoration: horizontal and vertical signal constraints split into independent
  one-dimensional flow paths, each of which can be extended through every
  selected-border orientation.
- Flattening the shaded supertiles into corrected quarter tiles preserves both
  internal and parent-boundary Wang matches. Combining those matches with the
  shade and signal edges gives genuine `ShadedSignals.tileSet` squares at
  cofinal side lengths; square compactness therefore proves an unconditional
  plane tiling of the concrete scaffold tileset.

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

The pair-cover recurrence is now separated from its final free-grid adapter,
so local seam modules rebuild without elaborating the expensive sparse-line
audits. Fully contained child covers compose into a parent cover once the four
nearest selected-boundary cases are supplied. A clean finite check refuted the
stronger shade-free shortcut: the same component orientation can face either
way at a nonrecursive seam. The remaining seam lemma must therefore use the
actual valid shade grid and the fact that no *selected* boundary lies between
the query and the chosen nearest boundary, exactly as in Robinson's argument.

The seam-path checker now searches for the exact Robinson disjunction: an
even path either reaches a perpendicular interior on the queried free line or
reaches a parallel interior strictly between the query and the selected
boundary. Its breadth-first reachability and adaptive multi-query coverage
algorithms have proved sound path semantics. `PairCoverSeamPathBaseAudit`
packages successful finite checks as `ParentPaths` and `Paths`. An external
eight-process diagnostic verified all 104 odd-base parents; even parent zero
also passed, but the even certificates still need to be split into cached
Lake modules instead of one monolithic native check.

The seam certificate cone is now separated from the older semantic audits.
Phase coordinates, executable child-containment checks, and red-port selectors
live in lightweight modules; graph search and its path soundness no longer
import shade contradictions. As a result, the complete proof-producing seam
base audit builds in seconds without rerunning unrelated native certificates.
The parent obligation is invariant under the border-state quotient, so checking
the 56 canonical `(thin, thick)` representatives proves `Paths` for all 104
tile indices. The next finite certificates should therefore be split over
those 56 representatives for each of the odd and even parity bases.
The canonical list is now partitioned into 14 checked chunks of four states,
and `ChunkChecks.paths` assembles their Boolean results into the semantic
all-parent theorem. The first isolated odd chunk passes `native_decide` and
builds in 949 seconds; the remaining chunks can therefore be generated and
built independently or in bounded parallel batches.
All 14 odd chunks now pass. Lake checked the 13 uncached chunks in one parallel
batch in 1,584 seconds, after which the proof-only aggregator established
`Paths .odd 0` in 6.9 seconds. The even depth-one base remains to be certified
through the same 14-chunk interface.

The finite search soundness now also retains a `BoundedPath` for every node
returned by the shared multi-query flood. This strengthening is deliberately
separate from the executable checker and its cached Boolean certificates. It
allows each constant-parent certificate to be transported into the matching
block of an arbitrary coarse grid without assuming component equality outside
the searched parent block.
The cached chunk equalities now lift through a second, proof-only soundness
layer to `BoundedPaths phase depth` for all 104 parent indices. Canonical
border-state quotient transport preserves both path endpoints and every
intermediate search-box bound, so this strengthening does not require any new
native certificate.
Bounded constant-parent paths now translate into the corresponding block of an
arbitrary coarse grid at total refinement depth `refinementDepth + 2`. The
translation theorem computes the exact phase-dependent quarter-coordinate
offset and returns an ordinary global red-graph path, ready for the seam shade
contradiction.
The same transport layer now identifies translated horizontal and vertical
port selectors, and both interior predicates, with their global counterparts.
Thus a local seam certificate can be consumed directly by the global shade
contradiction after only coordinate normalization.
Child-interval membership and the executable contained-seam checks are now
proved invariant under the exact parent-block offset.  Consequently a global
wrong-facing, noncontained seam query normalizes to the local query consumed by
`BoundedPaths`; the resulting bounded path translates back to a global
`VerticalSeamPath` or `HorizontalSeamPath` in the arbitrary parent block.
These two route theorems discharge all four cases of `VerticalBoundaryFaces`
and `HorizontalBoundaryFaces` by the shade-preservation contradiction.  The
adapter `forcesRoutedFixedCornerSquares_of_boundedPaths` now connects
`(phase depth) ↦ BoundedPaths phase depth` directly to the routed scaffold's
forward square-forcing property.

The cached odd and even certificates are exposed as `BoundedPaths .odd 0` and
`BoundedPaths .even 1`, respectively.  All fourteen even chunks passed in one
parallel Lake build.  The remaining seam-specific proof
is therefore exactly the scale recurrence: lift these two parity bases through
successive two-substitution refinements to bounded/global seam paths at every
odd depth `d` and every even depth `1 + d`.  A direct sparse-coordinate lift is
not sufficient on its own because each refinement also creates nonsparse
quarter intervals; the recurrence must account for those newly created
coordinates, using the existing refined-coordinate projection and local
connector lemmas.

The coordinate part of that recurrence is now closed in
`OllingerRobinson104PairCoverSeamRefinementCoordinates`.  Successor boards and
each recursive child interval scale by exactly four, `coarseCoordinate` is
monotone, strict coarse child membership lifts to strict fine membership, and
a fine query that does not fit one recursive child projects to a coarse query
that likewise does not fit.  Projecting strict fine board bounds loses
strictness only at the lower edge: the exceptional case is exactly the first
newly created sparse interval.  The remaining recurrence work is semantic:
project free-line and nearest-selected-boundary facts through inherited
intervals, then discharge that explicit lower-interval case by the local
connector audit.

The inherited semantic case is also available in
`OllingerRobinson104PairCoverSeamProjection`.  On literal sparse coordinates,
the projected shade state has exactly the same selected horizontal and
vertical boundary values as the fine state.  Therefore sparse fine free rows
and columns project to coarse free rows and columns, and absence of a selected
boundary strictly between two retained fine coordinates projects to the same
nearest-boundary fact at the coarse level.  It remains to package these facts
as a one-depth boundary-face recurrence and handle coordinates in newly
created intervals.

Boundary orientation is now factored through the fixed-depth structures
`VerticalBoundaryFacesAt phase depth` and
`HorizontalBoundaryFacesAt phase depth`.  One `BoundedPaths phase depth`
certificate produces exactly these local invariants, while pointwise local
invariants reassemble into the existing all-depth public face structures.
This makes a one-step semantic induction expressible without strengthening the
hypothesis to bounded paths at every scale.

`OllingerRobinson104PairCoverSeamFaceRefinement` now proves the complete
inherited part of the one-step recurrence.  For all four orientations, when
the query, free line, and nearest selected boundary lie on literal sparse
coordinates, the fine hypotheses project to depth `d`; the depth-`d` face
certificate determines the orientation; and exact sparse selection transports
that orientation back to depth `d + 1`.  Noncontainment is preserved by the
coordinate theorem above.  Thus only genuinely newly created coordinate
intervals remain in the face step.

`OllingerRobinson104PairCoverSeamFaceStep` makes that last statement exact.
A coordinate is now classified as either the literal sparse representative of
its coarse interval or a strictly created point inside that interval.  The
four next-depth face theorems split on the three queried coordinates: the
all-sparse branch is discharged by the inherited theorem, including strict
successor-board bounds, while every other branch is delegated to
`CreatedVerticalBoundaryFacesAt` or `CreatedHorizontalBoundaryFacesAt`.
Consequently a proof of those two local created-coordinate structures gives
the complete one-depth recurrence without any additional global arithmetic or
lower-edge exception.

`OllingerRobinson104PairCoverSeamCreatedPaths` removes shade semantics from
the cases actually covered by ordinary red-graph seam paths.  Those paths
discharge most of the remaining recurrence, but not the
sparse-boundary/created-free-line family described below; that family genuinely
retains the shade grid and nearest-selected-boundary semantics.

A first finite split of that geometric problem is now certified by
`OllingerRobinson104PairCoverSeamCreatedLocalAuditCheck`.  In every one of the
104 two-substitution macrocells, an even seam path exists if the selected
boundary coordinate is created.  It also exists when the boundary and queried
free-line coordinate are sparse but the transverse coordinate is created.
The exhaustive vertical and horizontal checks leave one dual pair of local
families: a sparse selected boundary with a created free-row/free-column
coordinate.  An exact substitution-language diagnostic showed that this is
not merely a missing neighboring-cell template: the language stabilizes at
204 adjacent pairs and 400 triples by depth three, and the path property still
fails on exact depth-four triples.  This family therefore needs Robinson's
semantic free-line/obstruction argument rather than another even-path audit.
`OllingerRobinson104PairCoverSeamCreatedLocalAudit` proves soundness of this
check as bounded red-graph paths.  Every intermediate port remains in the
audited 8-by-8 macrocell, providing exactly the hypothesis needed by the
existing component-congruence and block-translation lemmas.

`OllingerRobinson104PairCoverSeamCreatedLocalTransport` now performs that
translation at the exact depth-two scale used by the created-coordinate split.
It identifies local and global selected ports and interior predicates, moves
every bounded path by the `(8 * blockX, 8 * blockY)` quarter offset, and exposes
vertical and horizontal global seam paths for every certified local query in
an arbitrary coarse grid.  Cross-macrocell queries remain separate rather
than being hidden behind a false one-cell sentinel claim.
The proposition-facing `verticalSameBlock` and `horizontalSameBlock` wrappers
now consume the actual wrong-facing interior orientation and the audited
created-coordinate disjunction directly, so later recurrence code does not
need to reconstruct Boolean query-list membership.

The first cross-macrocell family is also finitely certified.  The final
substitution address bit reduces adjacent cells to 72 canonical sibling pairs
plus 720 canonical cross-parent pairs, for 792 states in each orientation.
`OllingerRobinson104PairCoverSeamCreatedAdjacentAuditDefs` checks the two-cell
8-by-16 and 16-by-8 windows for a created boundary facing across their common
edge.  Twenty-five independent cached modules cover 32 pair states each, and
`OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunks` assembles all
vertical and horizontal results without rerunning graph search.
`OllingerRobinson104PairCoverSeamCreatedAdjacentAudit` proves soundness of
those assembled checks as bounded red-graph paths in the corresponding
rectangular windows.  Thus every one of the 792 vertical and 792 horizontal
canonical adjacent states now has a proposition-level path certificate; the
remaining step is to classify actual neighboring refined cells by those
canonical states and transport the certified paths into the global grid.
`OllingerRobinson104PairCoverSeamCreatedAdjacentClassification` proves the
classification uniformly at every positive refinement depth.  Neighbors with
an even lower/left coordinate are siblings under one parent; neighbors with an
odd lower/left coordinate lie in the opposite row/column child classes.  In
both cases their canonical component pair belongs to the corresponding finite
audit list.  It remains only to transport the rectangular certificates from
that canonical pair window to the actual neighboring macrocells.
`OllingerRobinson104PairCoverSeamCreatedAdjacentComponents` proves that the
canonical audit window and the corresponding shifted arbitrary-grid window
have identical refined red components.  The proof works through the
thin/thick quotient state rather than evaluating canonical representatives.
`OllingerRobinson104PairCoverSeamCreatedAdjacentTransport` then moves bounded
paths, ports, and interior predicates into global quarter coordinates.  Its
`verticalLower`, `verticalUpper`, `horizontalLeft`, and `horizontalRight`
theorems expose all four boundary-created paths crossing one neighboring
macrocell edge.  `OllingerRobinson104PairCoverSeamCreatedPaths` now records the
correct logical split: `CoveredCreatedPathsAt` asks only for a created boundary,
or a sparse free line with a created transverse coordinate;
`ResidualVerticalBoundaryFacesAt` and
`ResidualHorizontalBoundaryFacesAt` state exactly the remaining sparse-boundary
and created-free-line semantic cases.  The next proof step is to derive those
residual face orientations from validity, freeness, and the absence of an
intervening selected boundary, following Robinson Section 7.  After that, the
same-cell and adjacent certificates can be assembled with the residual theorem
into the all-depth face recurrence.

The residual semantic argument now has a reusable certificate language.
`OllingerRobinson104RedShadeConstraints` treats a finite list of red ports as
signed shade constraints, with parity zero denoting light and parity one dark.
It proves that a weighted graph flood reaching any constrained port with the
opposite parity contradicts every valid shade assignment.  The accompanying
port lemmas prove that a present unselected vertical or horizontal interior is
dark.  Direct one-cell and two-cell audits nevertheless have genuine
counterexamples in every residual orientation: the relevant light red cycle
can close outside any such local window.  Enlarging that audit is therefore
not the right proof boundary.

`OllingerRobinson104PairCoverSeamCycleContradictions` instead formalizes the
global step used in Robinson Section 7.  If a selected boundary port has an
even red-graph route into a cycle and a free row or column crosses the cycle
interior, even connectivity around the cycle reaches a perpendicular red
interior on the free line and contradicts freeness.  Requiring the selected
port itself to be a literal cycle side is too strong: newly created red
segments can route to a canonical cycle without lying on it.  The remaining
residual task is geometric: use the existing sparse-boundary ancestry
classifiers to construct that even route and enclosing cycle, then use the
absence of an intervening selected boundary and the failed child-containment
test to place the created free line strictly inside the cycle.  The four face
orientations can then be discharged by the cycle contradiction, after which
the all-depth pair-cover recurrence can be assembled.

`OllingerRobinson104PairCoverSeamResidualCycles` makes that remaining boundary
precise.  `ResidualCycleWitnessesAt` asks each wrong-facing case for an
existential `RowSeparatingCycle` or `ColumnSeparatingCycle`, including an even
path from the selected source into the cycle.  The separation has exactly the
two cases in Robinson's Section 7 argument: either the queried free line
crosses the cycle, or a parallel side of the cycle lies strictly between the
query and its nearest selected boundary.  The cycle needs to contain the source's
transverse coordinate only in the second case; a diagnostic found sources
immediately inside the parent boundary, where imposing that condition also on
the crossing case is false.  The module proves that the four branch-precise
witnesses imply both residual face structures.  It remains to construct the
witnesses from aligned canonical cycles, the sparse-boundary ancestry
classification, the nearest-boundary hypothesis, and the failed
contained-child test.

The hierarchy composition part is now isolated in
`OllingerRobinson104PairCoverSeamResidualCycleBridges`.  An even route from the
selected source to an enclosing cycle composes with any `EvenCycleBridge` to a
descendant cycle, and branch-specific row and column constructors package that
descendant directly as a separation witness.  Thus the residual proof no
longer needs to build a graph path for each query: it needs one source-ancestry
route and an arithmetic choice of a bridged descendant cycle.

That last boundary is now represented without the four semantic face cases.
`ResidualSourceAncestorsAt` has one horizontal and one vertical obligation,
independent of the query line.  `ResidualDescendantSelectionsAt` has one row
and one column obligation, independent of shade states and selected-boundary
orientation.  Their assembly theorem reconstructs all four fields of
`ResidualCycleWitnessesAt`; the remaining proofs can therefore reuse the
existing local ancestor audits and treat descendant selection as pure
hierarchy arithmetic.

Cycle ancestry itself is now stable under the two-substitution recurrence.
`CycleAncestor.refineSparse` lifts a coarse ancestor cycle, entry, and even
route to their literal sparse copies; `CycleAncestor.refineThrough` then
prepends any even fine-grid connector.  The horizontal and vertical source
selectors are also proved to choose live ports whenever their interior signal
exists.  Consequently the finite local step need only return a live coarse
predecessor and an even connector to its sparse copy.

The needed finite predecessor statement is now certified for all 104 closed
tiles.  On each literal sparse local row, every horizontal interior segment
has a bounded even route from a genuine coarse horizontal selector; the
vertical statement holds dually on sparse local columns.  The exhaustive
weighted searches are split into eight cached parent ranges, and their
soundness theorem exposes the particular coarse predecessor and bounded path
needed for translation into an arbitrary macrocell.

Those finite witnesses now transport into arbitrary two-substitution
macrocells.  Every live horizontal selector on a sparse fine boundary has a
live coarse horizontal predecessor whose boundary maps exactly to the fine
boundary, together with an even connector from the fine selector to the
predecessor's sparse copy; the vertical theorem is dual.  These are precisely
the local hypotheses of `CycleAncestor.refineThrough`.  The next step is to
induct through the hierarchy, retaining the board bounds needed to apply the
base-cycle audit, and thereby instantiate `ResidualSourceAncestorsAt`.

A second finite audit now handles the complementary created-boundary case.
Every live horizontal selector at local rows `2` through `7`, and every live
vertical selector at local columns `2` through `7`, has a bounded route to the
canonical depth-two cell cycle.  The route parity is retained rather than
incorrectly required to be even: exhaustive diagnostics show that both
parities genuinely occur.  The certificate is proved for all 104 parents and
transported into arbitrary macrocells.  An even local route gives cycle
ancestry directly; an odd local route composes with Robinson's existing odd
parent-child cycle bridge to give an even route.  Thus the hierarchy induction
now has exhaustive local cases: sparse boundaries project to a coarse source,
and created boundaries terminate at a local hierarchy cycle.

This also exposes a needed refinement of the current factorization.
`CycleAncestor` forgets which canonical hierarchy cycle was reached, while
`ResidualDescendantSelectionsAt` consequently asks for a descendant of an
arbitrary `CycleOn`, which is stronger than Robinson's argument and need not be
true.  The retained ancestry theorem should carry canonical cycle coordinates
and their enclosing hierarchy block through the induction; descendant
selection can then use the existing certified hierarchy bridges from that
specific ancestor.

`OllingerRobinson104PairCoverSeamResidualCanonicalAncestors` now makes that
refinement concrete.  `CanonicalCycleAncestor` records the scale and block of
the reached Robinson cycle as well as the even source path.  The created-source
audit's arbitrary parity is normalized explicitly: an even route stays on the
local cell cycle, while an odd route crosses the odd corner bridge back to its
parent.  The named witness converts to the older unlabelled interface and is
preserved by a two-substitution sparse lift, so it is ready for the exhaustive
sparse/created hierarchy induction.

That induction step is now proved in
`OllingerRobinson104PairCoverSeamResidualCanonicalAncestorRecurrence`.
The predecessor witness records that its transverse coordinate stays in the
same two-cell macro-block, which proves that the collar
`[quarterWest west - 1, quarterEast east)` projects into itself.  Every live
fine selector then splits exhaustively: a sparse selected boundary uses the
certified predecessor, canonical sparse lift, and even connector; a created
selected boundary uses the parity-normalized local-cycle theorem.  The
remaining source-ancestry work is the finite even/odd base certificate and its
iteration to the recurrence depths used by `ResidualSourceAncestorsAt`.

The base certificate is now complete and factored into a reusable soundness
module plus 26 four-parent native-decision cache modules.  A single weighted
flood starts from the two consecutive canonical cycles and simultaneously
checks every live source in the stable collar.  Both the depth-four even base
and depth-five odd base are certified for all 104 parent tiles.  The public
`sourceAncestorsIn` theorem hides the finite partition, while the small cache
modules ensure that changing later hierarchy code does not rerun the audit.

The base theorem also now transports from its constant-parent audit square to
every block of an arbitrary coarse grid.  The proof retains whether the
checked route began on the large or small base cycle until after translation;
this gives the exact global canonical hierarchy block instead of attempting
to recover it from an unnamed existential ancestor.  The transported theorem
is already stated in the stable collar required by the two-level recurrence.

The recurrence is now iterated at every hierarchy depth and stated directly
with `refinedGrid` and `successorWest`/`successorEast`.  A compatibility theorem
instantiates `ResidualSourceAncestorsAt` without using its sparse-boundary
hypothesis; the stronger named theorem covers both sparse and created sources
and retains the exact canonical cycle needed by descendant selection.

Descendant selection also needs to know that this named cycle belongs to the
queried outer hierarchy block.  `HierarchyAddressWithin` records that a lower
level block, divided by the appropriate power of two, is the outer block.
The transported finite base now proves this relation directly: a route either
lands on the queried outer cycle or on its one-level-lower crossing cycle at
block address `2 * block`.  The original `SourceAncestorsIn` base remains as a
projection of this hierarchy-localized theorem.

The localized recurrence is now complete.  Sparse sources raise both the
ancestor and outer levels by two and preserve their quotient address.  Created
sources retain the exact audited macrocell (`coordinate / 8`); the canonical
collar bounds prove that cell belongs to the outer block, and the odd-parity
normalization also preserves the relation when it moves to the cell's parent.
`sourceAncestorsWithinAt` iterates this invariant at every phase and depth,
while `sourceAncestorsAt` and `ResidualSourceAncestorsAt` remain compatibility
projections.  Descendant selection can now consume the exact ancestor level,
block, cycle, and containment proofs directly.

Canonical descendant connectivity is now available at arbitrary hierarchy
levels.  `evenDescendantBridge` shifts the existing base-four induction by an
arbitrary bottom level, and `oddDescendantBridge` prefixes one certified corner
crossing before the even descent.  Thus an ancestor reaches every contained
canonical descendant with path parity equal to the level difference.  These
theorems live downstream of the native source certificates, so later
connectivity work does not invalidate their caches.  Hierarchy-address
quotients are now converted to the exact descendant interval bounds, and the
even-family and odd-family common-outer lemmas connect any two canonical
cycles of the same parity through their enclosing outer cycle.  The remaining
step is geometric: choose row- and column-separating descendants in the
appropriate parity family and package their bridges as residual selections.

The residual selection interface has now been corrected as well.  The old
`ResidualDescendantSelectionsAt` quantified over every arbitrary `CycleOn`,
discarding both the source route and the canonical hierarchy address; finite
coordinate diagnostics show that obligation is unnecessarily strong.
`LocalizedResidualSelectionsAt` instead receives the exact
`CanonicalCycleAncestorWithin` produced for the selected source.
`residualCycleWitnessesAt` assembles this localized obligation directly with
`sourceAncestorsWithinAt` for all four residual orientations.  The remaining
selector may therefore use the source path, ancestor parity, block address,
and local component constraints when choosing its separating cycle.

Graph connectivity has now been removed from the remaining finite obligation.
`CanonicalRowTarget` and `CanonicalColumnTarget` retain only a target level,
target block address, the shared even/odd hierarchy family, and the required
coordinate inequalities.  Generic conversion theorems transport the target
cycle into the full outer refinement, connect it to the actual source ancestor
through the common outer cycle, and package the separating path.
`LocalizedResidualTargetsAt.toSelections` reduces the remaining residual proof
to these pure target certificates.  The local selected-interior hypothesis is
retained explicitly in this final obligation: diagnostics found boundary-edge
coordinates satisfying the raw inequalities but carrying no red source in the
actual refined board.  Keeping the concrete component fact prevents the
target audit from quantifying over these impossible queries.

Further finite diagnostics refute the canonical-target obligation itself.
For an even successor board, the live source at `(34, 48)` reaches the outer
level-four cycle, while the created query row `34` is too close to that outer
boundary for any same-parity canonical descendant to separate it.  The actual
red graph nevertheless has a 57-edge even route to a vertical segment on the
query row.  Thus the square-cycle factorization is stronger than the semantic
argument and is no longer the intended proof endpoint.

`OllingerRobinson104PairCoverSeamResidualDirectPaths` now states the exact
replacement.  `DirectResidualPathsAt` asks directly for the two
shade-independent seam paths used by the contradiction: a wrong-facing
horizontal source must reach either a vertical segment on the free row or a
horizontal segment strictly between it and the row, and dually for columns. Its
`verticalResidual` and `horizontalResidual` theorems discharge all four
semantic residual orientations.  Existing cycle witnesses remain valid
sufficient certificates, but the remaining recurrence and finite audits
should target direct paths and need not choose a canonical descendant square.

The hierarchy contribution to those direct paths is now isolated as well.
`OllingerRobinson104PairCoverSeamResidualDirectPathBridges` refines every
localized canonical ancestor into one of two parity families.  Two source
ports whose ancestors lie in the same family are connected evenly through
their common outer hierarchy cycle.  Four constructors then turn a
same-family live target into either crossing or between-line alternatives for
`VerticalSeamPath` and `HorizontalSeamPath`.  Consequently the finite
remaining invariant is only target recognizability: for the source's actual
family, find a live target on the query line or strictly between it and the
source.  All graph connectivity is supplied generically.

`OllingerRobinson104PairCoverSeamResidualDirectPathTargets` now states that
recognizability invariant as `FamilyTargetsAt`.  `RowFamilyTarget` and
`ColumnFamilyTarget` allow exactly the crossing and between-line alternatives
from the seam definitions.  Each `FamilyTargetsAt` field jointly chooses a
source ancestor family and a target ancestor in that family; it does not demand
a target for every possible existential ancestor witness.  Its `toDirectPaths`
theorem applies the same-family bridge, yielding `DirectResidualPathsAt` with no
remaining graph search.  The next finite work can therefore focus solely on
recognizing one compatible source/target family from local two-substitution
data and transporting that joint certificate through recurrence.

The orientation premise is essential.  An initial diagnostic accidentally
asked for a path from every live residual source, including sources already
facing in the conclusion's required direction.  The even-board query
`(column, boundary, row) = (34, 48, 50)` has a south-facing source and needs no
contradiction in the below-boundary case; unsurprisingly it has no even seam
path.  `DirectResidualPathsAt` and `FamilyTargetsAt` now retain exactly the four
wrong-facing component equalities used by the semantic proof, avoiding this
second overstrengthening of the finite target invariant.

The first corrected diagnostic, on the constant parent-zero even board, finds
a compatible joint family target for every wrong-facing row query.  The family
transport API now proves that both two substitutions and an even connector to
a sparse predecessor preserve the chosen localized family.  This is the
inductive interface needed to combine the existing predecessor audit with the
remaining finite source/target recognition checks.

The stronger possibility that every wrong-facing query has targets in both
families is false: the earlier `(34, 48, 34)` query has only the odd-family
target required by its source.  The joint-family formulation is therefore
necessary, not just a proof convenience.  The new
`OllingerRobinson104PairCoverSeamResidualDirectPathFamilySearch` module turns an
accepted lightweight finite flood from either localized family into a proved
`CanonicalCycleAncestorWithinFamily`.  Its soundness proof reconstructs the
descendant level and block addresses, proves the cycle exists in the common
outer refinement, and reverses the certified even path to the endpoint.  The
`OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetSearch` module
now reuses this trusted primitive for both source and target witnesses.  Its
row and column checks search the two cached family floods, require the source
and target to occur in one common family, and prove the resulting
`RowFamilyTarget` or `ColumnFamilyTarget`.  Thus the executable layer has a
sound bridge all the way to the joint certificates consumed by
`FamilyTargetsAt`; the remaining finite work is to enumerate every applicable
even/odd base query once, then transport those certificates through the
two-substitution recurrence.

The finite family flood now also retains a bounded path inside the complete
constant-parent refinement.  Every family start is proved to lie inside the
exact quarter-coordinate parent width, and bounded weighted-search soundness
produces the named descendant cycle, its hierarchy family, and a confined
path to the accepted endpoint.  The generic `OnCycleTranslation` adapter and
`OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTransport` then move
that certificate into any parent block of any coarse grid.  The transport
reconstructs the absolute descendant address, obtains its canonical cycle in
the global refinement, and translates and reverses the even path.  Thus the
remaining finite target enumeration can run only on constant-parent blocks;
it no longer needs to prove global-grid family ancestry separately.

Boundedness is now retained through the joint endpoint checks as well.
`BoundedRowFamilyTarget` and `BoundedColumnFamilyTarget` keep each accepted
target route inside the exact parent block, and the corresponding joint
soundness theorems retain bounded routes for both the source and target in one
chosen family.  `OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetTransport`
translates the target inequalities, strict-between relation, live interior,
selected port, and family ancestor together.  Its final row and column
wrappers turn an accepted constant-parent Boolean check directly into the
global joint certificate consumed by `FamilyTargetsAt`.  What remains at this
layer is the finite enumeration of all applicable local base queries and the
arithmetic normalization from successor-board coordinates to these translated
local coordinates.

That arithmetic normalization is now complete in
`OllingerRobinson104PairCoverSeamResidualDirectPathFamilyBase`.
`BoundedFamilyTargetsAt` is the exact finite certificate boundary: for each of
the 104 constant parent tiles it checks every wrong-facing, non-contained
residual row and column query, retaining the sparse-boundary and created-line
filters from the semantic goal.  Its `toFamilyTargetsAt` theorem translates
local coordinates, interiors, child-containment tests, source routes, and
target routes into an arbitrary parent block.

The executable base layer now has a proof-sound dense reachability index.
Every indexed hit is checked again against the retained path node before its
soundness theorem recovers the original family-reach predicate, so the mutable
array is only an accelerator and carries no trusted invariant.  Indexed row,
column, and joint-family checks feed a single `check_sound` theorem for the
exact `BoundedFamilyTargetsAt` interface.

A first odd-depth diagnostic with a deliberately small flood budget found
that both family floods hit the budget before reaching the first residual
source.  Increasing this whole-board search is not the intended inductive
proof: the existing `horizontalPredecessor` and `verticalPredecessor` theorems
already give every sparse-boundary fine port an even local connector to a live
coarse predecessor.  The family-predecessor layer now transports a supplied
coarse canonical-cycle family through exactly this audited even connector,
both horizontally and vertically.  The hierarchy-level wrappers additionally
retain the selected coarse predecessor and its stable-collar bounds at every
depth.  Combining this with the all-depth source-ancestor hierarchy now gives
the actual inherited family at every sparse fine source without a family
flood.  `InheritedFamilyTargetsAt` now exposes this coarse source, its old
family ancestor, and the transported fine ancestor to a target-only
recognition obligation; its adapter proves the complete `FamilyTargetsAt`
interface.  Finite diagnostics show the first two target forms: a local
transverse turn, and a parallel target at the sparse projection of the query
line.  `SameFamilyPredecessors.refine` now proves the common recursive step:
even local connectors at both endpoints lift any coarse same-family relation
to the fine pair.  The next step is to certify the finite endpoint-choice
transitions and show that every nonlocal branch projects to another coarse
pair, reserving the whole-board checker for base validation.

Literal-sparse target refinement is now complete as well.
`RowFamilyTarget.refineSparse` and `ColumnFamilyTarget.refineSparse` preserve
both target alternatives, their selected ports, and their hierarchy family
through two substitutions.  The associated interval lemma is stronger than
the exact sparse case: a coarse parallel target remains strictly between any
fine point assigned to the coarse query interval and the sparse copy of the
boundary.  Consequently the remaining finite endpoint transition only needs
to handle genuinely created query coordinates and the local connector from
the actual fine source; it no longer needs to re-prove sparse target transport.

The first forward endpoint-transition audit is now proof-producing and split
into independently cached chunks.  Starting from an exact sparse copy of a
coarse horizontal or vertical target, it searches the corresponding `8 x 8`
two-substitution macrocell for an even route to every aligned fine coordinate,
while constraining the new parallel coordinate to the old target's sparse
interval.  Search soundness recovers a `BoundedPath`; no Boolean result is
trusted directly.  An initial diagnostic appeared to fail on parent tiles
`0..7`, but those cases all asked for a fine coordinate in the same `8`-block
rather than in the old target's actual sparse interval.  After restricting the
checker to `coarseCoordinate fine = old`, the audit succeeds for all 104 parent
tiles.

The semantic lift is therefore complete for every selected target.
The local bounded path translates into an arbitrary hierarchy macrocell, and
the translated endpoint is proved to have the same `coarseCoordinate` as the
old target.  A strengthened interval theorem lifts strict betweenness when
both the query and target are arbitrary points of their respective sparse
intervals.  Four branch-specific constructors now cover the transverse and
parallel alternatives of `RowFamilyTarget` and `ColumnFamilyTarget`, preserving
board bounds, live interiors, and the exact hierarchy family.  No exceptional
parent hypothesis remains.  `RowFamilyTarget.refineAt` and
`ColumnFamilyTarget.refineAt` package the four constructors into one theorem
for an arbitrary target alternative and arbitrary fine query coordinates in
the selected coarse intervals.  `RowFamilyTarget.refineIterate` and its column
dual now iterate this transport through an arbitrary number of hierarchy
levels using only repeated coarse-coordinate equations; recursive level and
scale indices keep the dependent proof fast to elaborate, with separate
closed-form lemmas recovering `level + 2 * depth` and `4 ^ depth * bound`.
Conversely, an existing even `VerticalSeamPath` or `HorizontalSeamPath` now
recovers a target in the source's exact hierarchy family, so the established
created-coordinate path audits can seed the target recurrence.

The predecessor audit's older interface retains only a common two-cell block.
A new proof-producing exact checker instead fixes the selected predecessor to
`oldColumn = coarseCoordinate fineColumn` (and the row-dual equality); cached
native certificates prove this stronger property for all 104 parent tiles.
Its soundness theorem recovers a bounded even path, and the transport theorem
moves that path into an arbitrary hierarchy macrocell while preserving the
exact projection equation.  The same finite certificate also proves that the
projected source has exactly the fine source's directional interior, so the
recursive argument retains the wrong-facing orientation required by the
created-path seed theorem.

`OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorHierarchy`
packages that exact predecessor with the all-depth source-family hierarchy.
Its horizontal and vertical records carry the projected coordinate, collar
bounds, preserved orientation, coarse family ancestor, and refined family
ancestor.  Their `refineTarget` eliminators lift any target for the exact
coarse source directly to the original fine query.  The next step is only the
finite-depth seed recursion.  The existing complete bounded seam-path bases
are now exposed directly as same-family target seeds: the even certificate at
depth one and the odd certificate at depth zero require no additional family
flood or generated audit.  Follow exact sparse predecessors to one of these
cached depths and apply the hierarchy eliminators while unwinding the
recursion.  In particular, the even certificate now closes the complete
`FamilyTargetsAt .even 0` interface, including canonical source-family
selection.  Projection can place a created query coordinate exactly on the
coarse collar's lower edge, so the remaining recursion must handle that case
explicitly instead of assuming strict bounds survive every projection.
The exact predecessor now retains a family-polymorphic transport theorem as
well: a base or diagonal finite certificate may choose either hierarchy
family, and that chosen source/target pair transports together to the fine
query.  This avoids fixing an unrelated family witness before endpoint
selection.

The two projection-stopping cases are now represented by a small finite
interface, `BoundedExceptionalTargetsAt`.  It checks the source boundary for
north/east sources (the relation-collapse case) and the lower collar edge for
south/west sources (the bound-collapse case).  The same certificate also
checks every ordinary residual query when the transverse source coordinate is
exactly the lower collar edge; this is the remaining weak-bound case omitted
by the strict cached seam-path interface.
The checker reuses one indexed pair of family floods per parent and is split
into 26 four-parent chunks; only depth-zero even and odd certificates are
needed, because arbitrary-family predecessor transport lifts these seeds to
all later hierarchy levels.
All 26 chunks are now certified in both phases and assembled as
`PairCoverSeamResidualDirectPathFamilyExceptionalBase.evenTargets` and
`.oddTargets`.  The expensive finite computation is therefore isolated behind
two proof-level depth-zero target interfaces.
The certified local witnesses now transport into arbitrary parent blocks while
preserving both the selected source family and its row/column target.
Exact inherited sources now retain the stronger projected bounds needed by
that checker: transverse coordinates may equal the lower collar edge, while
the projected sparse source boundary remains strictly inside.  The query
projection is packaged into four cases with preserved orientation: ordinary
strict south/west and north/east queries, south/west at the lower edge, and
north/east equal to the source boundary.  Thus the remaining recursion can
dispatch its stopping cases and lower-edge transverse sources directly to the
certified exceptional base.
This dispatch now closes `FamilyTargetsAt .odd 0`.  Every exact inherited
query projects either to a strict cached odd path, a lower-edge query, a
source-boundary query, or a strict query whose transverse source lies on the
lower edge.  The latter three cases use the transported exceptional
certificate; all four preserve the selected canonical hierarchy family while
refining the target back to the original query.
The six exceptional row/column shapes are now packaged as the two-field
semantic interface `ExceptionalFamilyTargetsAt`.  Both finite base
certificates instantiate it, so the all-depth proof can recurse over a small
proof-level state without exposing finite flood or checker implementation
details.

The all-depth boundary-face induction is now packaged independently of the
finite searches. `PairCoverSeamFaceRecurrence.StepData` contains exactly the
created-coordinate paths and direct residual paths consumed by one refinement;
same-family targets instantiate its residual field. The separate
`PairCoverSeamFaceRequired` adapter alone imports the cached odd depth-zero and
even depth-one bounded searches, seeds the two face families, and exposes
`requiredFaces` at precisely the odd depths `d` and even depths `1 + d` used by
the final light-board construction. Thus ordinary changes to the semantic
recurrence avoid replaying the native parity certificates, and no all-depth
`BoundedPaths` hypothesis is required by the retained forward architecture.

`PairCoverSeamRequiredForward` now carries these fixed-depth faces through the
rest of the forward proof.  It builds the successor board's contained geometry
directly from its child covers and the two local face structures, iterates only
the even `1 + d` and odd `d` families, and invokes the existing unbounded
light-board construction.  Consequently `forcesRoutedFixedCornerSquares_of_stepData`
requires only semantic `StepData` at the used depths; the unused even depth-zero
face obligation has disappeared from the final forward theorem surface.

`PairCoverSeamResidualDirectPathAllFamilyTargets` isolates the target state
that is actually closed under coarse projection: unlike the older residual
interface, it does not require the projected free-line coordinate to remain
newly created.  The cached even path base proves this stronger state directly;
`PairCoverSeamResidualDirectPathAllFamilyTargetsOddBase` proves the odd base by
the exact-predecessor dispatch and exceptional certificates.  Both modules sit
downstream of all native audits so the remaining target recurrence can be
developed without invalidating finite certificates.

The target recurrence now has an explicit created-boundary branch.
`PairCoverSeamResidualDirectPathAllFamilyTargetsCreated` converts the existing
created seam paths into row and column targets in any hierarchy family already
carried by the selected source.  Thus the recursive step can split the coarse
selected boundary: retained boundaries recurse, while created boundaries use
these adapters; only the separately packaged exceptional query shapes bypass
that split.

Canonical-cycle targets now include the geometrically valid corner ports.
`PairCoverSeamResidualDirectPathCornerTargets` proves that the southwest and
northwest vertical ports and the southwest and southeast horizontal ports have
the required nonempty signal interiors.  Each corner connects by an even red
path to a strict south-side `OnCycle` entry, so it defines a
`CanonicalCycleAncestorWithinFamily` without weakening or changing the
selected hierarchy family.  This removes the artificial loss caused by the
strict-side-only `OnCycle` syntax at exact cycle-corner coordinates.

The corner cases are now hidden behind a closed-side target API.
`PairCoverSeamResidualDirectPathCornerTargets.verticalWest` and
`.horizontalSouth` cover every point of a canonical west or south side,
including both endpoints.  `PairCoverSeamResidualDirectPathCanonicalSideTargets`
then converts a purely arithmetic choice of a crossing or separating canonical
side directly into `RowFamilyTarget` or `ColumnFamilyTarget`.  The remaining
created-boundary proof can therefore work entirely with hierarchy addresses,
family parity, and inequalities; it no longer needs to inspect red-graph ports.

The created-boundary recurrence now has a concrete seed.
`PairCoverSeamCreatedBoundaryBase.evenBase` reuses the cached even depth-one
path audit to prove `CreatedBoundaryPathsAt .even 0` directly.  No new native
search is introduced: the theorem only adapts the already checked global seam
paths to the narrower created-boundary interface.

The local part of every created-boundary obligation is now closed at all
depths. `PairCoverSeamCreatedBoundarySameBlock.vertical` and `.horizontal`
translate the existing 8-by-8 created-source audit into an arbitrary refined
grid whenever the query and selected boundary lie in the same depth-two
macrocell. A generic seam-path widening lemma moves the finite target interval
to the enclosing canonical collar; the collar alignment follows arithmetically
from its level being at least two. Thus the remaining created-boundary work is
only the cross-macrocell case, and this step adds no native computation.

The adjacent finite case is strengthened without making one monolithic
certificate. `PairCoverSeamCreatedAdjacentFullAuditDefs` asks one weighted
flood to cover every query coordinate in the neighboring 8-wide macrocell,
rather than only its shared edge. All 792 realizable pair states pass in both
directions; `PairCoverSeamCreatedAdjacentFullAuditChunks` assembles the 25
independent 32-pair certificates. A single chunk takes roughly two minutes to
rebuild on the current machine, while Lake can build changed chunks in
parallel.

`PairCoverSeamCreatedAdjacentFullAudit` lifts those Boolean certificates to
ordinary propositions. For every realizable vertical or horizontal pair, it
provides a bounded seam path from each live created boundary to every query
coordinate in the opposite macrocell. The finite computation is therefore
fully separated from the remaining coordinate transport and hierarchy
arithmetic.

`PairCoverSeamCreatedAdjacentFullTransport` now moves each of those bounded
certificates into an arbitrary global refined grid. Unlike the earlier
edge-only transport, these theorems preserve the actual opposite-macrocell
query coordinate, which is what the created-boundary obligation requires.

The exact neighboring-macrocell cases are now reduced to those transported
certificates. `PairCoverSeamCreatedBoundaryAdjacent` classifies every actual
positive-depth adjacent pair into the 792 audited states, normalizes global
coordinates into its 8-by-16 or 16-by-8 window, and widens the result to the
hierarchy collar. Together with the same-block theorem, only queries separated
from their created boundary by at least one whole intervening macrocell remain.

All four canonical cycle sides remain useful target constructors, but they do
not cover every realizable far query.  An exact coordinate audit found, for
example, a realizable outer-level-four source at
`(column,row,boundary) = (34,49,68)` whose family has no canonical closed side
accepted by the query.  The rejected `FarCanonicalChoicesAt` interface has
therefore been removed instead of being retained as an unprovable obligation.

The far case instead has a simpler local proof.  In every realizable adjacent
pair of depth-two macrocells, a created source has an even path to a parallel
red segment on each live query-facing side.  The 25 cached
`PairCoverSeamCreatedFarParallelAudit` chunks certify this finite fact for all
792 vertical and 792 horizontal pair states.  Their proposition-level API
returns a bounded path, so translation cannot leave the audited rectangle.

`PairCoverSeamCreatedBoundaryFar` places that adjacent pair at the source,
translates the bounded path into the global refined grid, and observes that
the parallel segment lies strictly between any separated query and source.
`PairCoverSeamCreatedBoundaryAllDepth` then splits coordinates into same,
adjacent, and separated depth-two macrocells.  This proves
`CreatedBoundaryPathsAt` for both phases at every depth without hierarchy
induction and deletes the obsolete `FarFamilyTargetsAt` adapter.

The exceptional target recurrence is now closed at every depth. Sparse source
boundaries use an exact predecessor and inherit the old same-family target.
Non-sparse boundaries use the already certified same/adjacent/far created
paths for the lower-collar and lower-transverse cases. The remaining
source-equality case has its own small 104-parent, 8-by-8 finite path audit;
its bounded certificate transports into any hierarchy block and preserves the
source family. Starting from the certified even and odd depth-zero targets
therefore proves `ExceptionalFamilyTargetsAt` for both phases at every depth.
`PairCoverSeamRequiredForward.closed104_forcesRoutedFixedCornerSquares` now
discharges the routed scaffold's forward fixed-corner-square property with no
hypotheses.

### 1. Obtain arbitrarily large free squares (complete)

The shade decoration selects a noncrossing family of red borders with
unbounded light members, and Robinson obstruction signals are instantiated on
exactly those borders. The board/free-line recurrence, contained pair covers,
and all exceptional residual seam cases now combine into the unconditional
forward theorem above, which supplies arbitrarily large recognizable active
squares with their routed fixed corner.

### 2. Prove backward realization

Construct scaffold tilings containing active-corner boxes of every finite size,
or equivalently finite layer patches that compactness assembles into the
required plane tiling. Show arbitrary payload tiles can be routed through the
active square and obstruction channels.

The generic payload assembly is now separated from this geometry.
`RoutedCoreBoxLayerPatch` prescribes payloads only on non-inactive scaffold
cells and asks for matching only between adjacent prescribed cells.  Its
`toRoutedCombinedBoxLayerPatch` construction fills every inactive cell with a
complete-palette absorber, preserving all routed membership and matching
conditions.  Consequently the concrete backward target can be stated as
`HasRoutedCoreBoxLayerPatches`; the generic adapter
`hasRoutedCombinedBoxLayerPatches_of_coreBoxLayerPatches` then supplies the
compactness interface.  The remaining constructive work is purely the
Robinson routing core: index active crossings by one supplied fixed-corner
square and place constant horizontal/vertical wire payloads along the clear
corridors between them.

That payload construction is now factored through
`RoutedCoreLabeling.Labeling`. A concrete finite scaffold box labels each
constrained cell as a logical square tile, a horizontal edge wire, or a
vertical edge wire. The finite compatibility relations certify the only
possible constrained adjacencies. For every supplied fixed-corner square,
`Labeling.toRoutedCoreBoxLayerPatch` then constructs all payload tiles, proves
wire-palette membership, places the seed at every corner label, and derives
physical matching from the logical square. The remaining backward theorem is
therefore the scaffold-only finite statement `HasRoutedCoreLabelings`.
`hasRoutedCoreBoxLayerPatches_of_labelings` connects that statement directly
to the generic compactness pipeline.

Backward shade construction is also reduced to its actual finite invariant.
`RedShadeGraphColoring.ValidParityColoringOn` records a Boolean XOR coloring
of the live red-port graph in a finite rectangle: continuations preserve the
bit and crossings reverse it.  Its `validShadeRectangle` theorem constructs
the concrete `RedShades.State` rectangle and proves every local incidence,
corner, crossing, and edge-match rule.  Thus no infinite shaded plane or
type-local shade table is required for backward realization.  The remaining
shade obligation is the hierarchy-specific bipartiteness certificate for one
sufficiently large finite substitution supertile.

That hierarchy-specific certificate is now represented as a finite-state
shaded substitution.  The 104 corrected tiles admit 176 locally valid
tile/shade-block states, each with one or two valid two-substitution (`4 x 4`)
expansions.  A memoryless choice table does not close under iteration, but one
additional context bit with a 16-position transition table does.  Starting
from the selected seed gives a closed subsystem of 312 context/state nodes.
The SAT search was used only to discover the two finite tables; Lean's native
checker independently reconstructs the expansions and verifies that every
reachable node has all 16 children, every child remains reachable, and all
generated horizontal and vertical boundaries are compatible.  A second
all-pairs audit verifies that every compatible pair among the 312 reachable
states preserves its compatibility under expansion; this is the induction
invariant needed across descendants with different immediate parents.  The
proof-facing API packages reachability as a `Node` subtype with a total
`Fin 16` child operation and defines its iterated `4 x 4` supertile grids.
The resulting flattening theorem constructs, for every level, a concrete
quarter-state square of side `2 * 4^level` and proves all local shade rules and
all internal horizontal and vertical matches.

The obstruction-signal layer is now constructive on every such finite shaded
rectangle.  Its horizontal and vertical constraints separate into finite
one-dimensional flow paths.  A three-endpoint induction proves that every
finite sequence of selected-border orientations admits a matching path; row
and column paths then combine into signal states satisfying every local rule
and all internal edge matches.  Thus backward realization needs no second
substitution certificate and no pre-existing infinite signal plane.  The next
step is to align these valid shaded signal supertiles with the audited
free-grid geometry, index one clear grid by a supplied fixed-corner payload
square, and feed that data to the routed-core patch constructor.

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
