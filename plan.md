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
