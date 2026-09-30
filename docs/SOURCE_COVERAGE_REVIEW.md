# Source coverage review

Manuscript: *Dynamical C*-algebras and coarse geometry*, `paper/main.tex`.

The revised manuscript has been reviewed and its SHA256 synchronized with the inventory.

## Inventory status

The source inventory has been reviewed across all 62 mathematical statement
environments, all 35 citation occurrences, and the mathematical prose and
background definitions. `inventory_complete` records this inventory review,
not completion of every proof obligation. Theorems A–E and all supporting
statement environments and all mathematical prose entries are verified. The countability qualification and the revised growth reduction are reviewed; see
[the resolved qualifications below](#completion-review-of-additional-prose).

Cited results required by the proof are supplied by checked Mathlib results or
project proofs. Historical and novelty attributions are distinguished from
mathematical dependencies. No question or conjecture is asserted as a theorem.

## Checked correspondence

All names below are in namespace `DynamicalCStarAlgebras`.

| Source | Lean | Review |
| --- | --- | --- |
| Theorem C | `theoremC` | Full unconditional Roe < AP_strip < quasi-local for raw expander unions, including empty initial components. |
| Theorem D | `theoremD` | Full strict decay chain for every 0 < alpha < beta and injective isometric bounded complex matrix-product embedding with exponential range. |
| Ozawa Theorem A, cited at line 1560 | `boundedMatrixProduct_not_range_subset_uniformRoe` | Full nonunital nonembedding theorem for every ULF pseudometric space; no external assumption. |
| Remark 808 | `maximalULF_counterexample` | Full literal ℕ example: maximal ULF structure, bounded-height characterization, all common continuity points, and explicit flat-row non-quasi-local witness. |
| Metric propagation, line 436 | `metricPropagation_lt_top_iff` | Extended nonnegative support-distance supremum, exact radius characterization and equivalence to finite propagation. Zero support has supremum zero. |
| Cited Braga–Exel Proposition 2.1, line 219 | `isCoarseReal_iff_uniformRoe_continuous` | Coarse heights are exactly those making every Roe operator a continuity point, for arbitrary ULF coarse structures. Necessity is proved using partial translations and Fejer approximation. |
| Ozawa finite-representation step, cited at line 1560 | `signedBasisRepresentation_irreducible` | Finite signed-permutation group and irreducible norm-preserving complex representation in every positive dimension. |
| Ozawa lower amplification step, cited at line 1560 | `matrix_embedding_amplification_norm_lower_bound` | Injective nonunital matrix-algebra homomorphisms supply an isometric copy; an invariant tensor vector gives the lower bound one. |
| Li–Zhang–Zhu finite probabilistic argument, cited at line 1905 | `exists_frame_bound_of_coordinate_tails` | Exact constant32 after all finite-net/counting/union estimates. This source proof step has an explicit concentration premise, now discharged by CoordinateGaussian. |
| `lem:smoothing` | `quasiLocal_smoothing` | Full arbitrary-coarse-space statement, exact oscillation threshold and error 16*delta*norm(a)+8/delta*epsilon. Cosine square-partition, finite-sign orthogonality and bounded operator construction are proved. |
| Claim at line 818 | `height_band_nonzero_compression` | Nonzero compression forces adjacent bands and disjointness of the band rectangle from the restricted entourage, with both literal source conclusions. |
| Remark at line 1004 | `controlled_operator_partial_translation_decomposition` | Finite disjoint partial-bijection partition, partial isometries, bounded diagonal coefficients and entire exponential analyticity of each summand. Holds for arbitrary ULF coarse spaces. |
| Ozawa Lemma 3, cited nonembedding proof at line 1560 | `irreducible_unitary_average_norm_le` | Schur averaging and coefficient orthogonality prove the exact reciprocal-square-root dimension bound. |
| Ozawa amplification proof at line 1560 | `controlled_unitary_amplification_norm_bound` | Controlled-relation decomposition gives a sufficient N² amplification bound. This is an intermediate proof step, not the sharp source threshold or final nonembedding theorem. |
| `Prop.palpha.is.inQLalpha.exp` | `CoarseGraphUnion.projection_mem_polynomialQuasiLocal` | Full polynomial membership for the source projection data, including the finite initial zero segment. The ambient modulus follows from finite expander estimates and uniform block compression. Finite-subspace existence is now proved in GoodSubspaces. |
| Assumption.1, strong-sum construction | `exists_projection_strong_sum` | Any supplied family of component orthogonal projections assembles to an orthogonal projection; exact restrictions and strong convergence on every vector are proved. Prescribed ranks and compression bounds are not postulated as a universal existence theorem. |
| Strict-inclusion proof from Assumption.1 | `ExpanderGraphUnion.strict_decay_inclusions_of_projection_data` | Combines membership, norm-closure nonmembership and existing algebra inclusions from actual projection data. This intermediate implication is consumed by the now-checked unconditional C/D assembly. |
| `Eq.UnifExpDecay` | `CoarseGraphUnion.good_projection_block_exponential_bound` | Exact 2*C*kappa^(-r/24) modulus bound for supported contractions with the source good-projection estimates. Every nonnegative radius and all component sizes are handled. |
| Matrix-product argument, lines 1247–1296 | `CoarseGraphUnion.exists_matrixProduct_embedding_of_good_subspaces` | From actual good closed finite subspaces with exact ceil(card^(1/4)) dimensions, constructs an injective isometric nonunital star-algebra map with exponentially decaying range. Models the bounded complex matrix product by lp infinity. Universal subspace existence is now proved in GoodSubspaces. |
| Appendix reductions, lines 1918–1938 | `quarter_power_compression_of_frame_bound`, `logarithmic_rank_compression_of_frame_bound` | Exact rank rounding and constants, including the quarter-power factor 3*C. These are implications from the frame bound, not themselves existence arguments; the cited frame-subspace theorem is now proved separately. |
| `lem:volume` | `volume_approximation` | Full N_X/eta statement, exact factor-two tail for every cutoff, and Roe membership. Supremum definitions use closed balls and distances at least m; empty suprema are zero. |
| `Defi.Exp.Growth` | `atMostExponentialGrowth_iff_volume_bound` | Standalone N_X and equivalence with the uniform closed-ball growth predicate under uniform local finiteness. The source positive-radius convention is preserved. |
| `Thm.qla.h.Points.Cont.Substructure` | `quasiLocal_inter_continuityPoints` | Full arbitrary-coarse-space equality. Fejer averaging preserves each (epsilon,E) estimate; finite integer bands prove the three-error restricted-height bound. No local finiteness or metric assumption. |
| Coarse equivalence and metric independence, lines 424–462 | `CoarseDisjointUnion.bijectivelyCoarselyEquivalent` | Exact coarse-map/closeness definitions and arbitrary finite metric components, including empty ones. Internal component isometries give coarse equivalences independently of cross distances. |
| Example `Defi.21.sep.26.1.qqq` | `IsLargeScaleGeodesic.atMostExponentialGrowth`, `graphMetric_atMostExponentialGrowth` | ULF bounded-step chains of affine-controlled length imply exponential growth in the original metric. Connected graph metrics and finitely generated Cayley graphs are checked special cases. |
| Uniform local finiteness, line 409 | `coarse_uniformlyLocallyFinite_iff` | Exact symmetric-entourage finite-fiber definition, symmetrization for general entourages, and equivalence with the metric ball definition. |
| Continuity algebra, line 221 | `continuousOrbitSubalgebra_isClosed` | General complex C*-automorphism families, including nonunital algebras; orbit continuity is not assumed. |
| Weak integral, line 479 | `exists_unique_weakIntegral` | General complex Hilbert spaces and measure spaces, scalar integrability plus bounded integrated form, and unique representing operator. No separability or strong operator integrability assumption. |
| Finite-strip definitions, line 916 | `isStripExponentialType_iff_stripAnalytic` | Named positive-width/some-strip predicates and the finite-strip exponential-type condition. The compact imaginary-segment maximum supplies positive exponential constants; entire exponential type remains distinct. |
| Iterated commutator definition and recursion, line 1731 | `iteratedCommutator_characterization` | Entrywise representation for arbitrary heights, uniqueness if bounded, order zero, and the exact successor recursion. Does not assert existence of bounded commutators. |
| Integrated Fejer estimate, lines 564–572 | `fejerAverage_sub_norm_le_of_local_bound` | Exact epsilon+8*norm(a)/(s*pi*delta) estimate. Integrates the inverse-square tail to 4/(s*pi*delta), complementing the earlier dominated-convergence proof. |
| Theorem `Thm.QLthetaDoesNotContainP` | `CoarseGraphUnion.projection_not_mem_polynomialQuasiLocal` | Full nonmembership in the norm-closed polynomial algebra under the projection data of Assumption.1. Uniform local finiteness supplies the common degree bound; self-adjoint approximation, component transfer, coordinate trace/rank identities and the trace contradiction are checked. The theorem also allows an ambient self-adjoint operator with the same eventual component data, so its conclusion applies to the source projection. The prescribed finite subspaces and their strong-sum projection are now constructed in GoodSubspaces and ExpanderProjectionExistence. |
| Claim `Claim.ddd.q` | `small_projection_compression_bound` | Exact compression estimate for nonempty sets of size at most k sqrt(card X), from the projection estimate in Assumption.1. Uses the star-projection norm-square identity and a finite-cardinality entropy bound; valid whenever card X>1. Does not construct the good subspaces. |
| Equation `Choiceofn` | `eventually_small_compression_majorant` | The exact source majorant tends to zero for alpha>0 as component sizes diverge, giving an eventual bound by any positive delta. |
| Bounded-degree ball count (lines 1503–1509) | `graph_ball_card_le_sqrt` | Shortest walks give the geometric-sum count, the bound k^(r+1), and the exact k sqrt N consequence of the source radius constraint. Finite connected graphs, degree bound k>=2, all nonnegative real radii. |
| Radius choice and `Eq.mnrn.k.claim` | `eventually_nonmembership_radius_admissible` | The exact source floor choice of m and real-power choice of r are eventually positive and satisfy m r <= log N/(2 log k). This holds for each fixed delta>0; the component threshold may depend on delta. This suffices for the checked two-limit argument. |
| Equation `Eq.t.q.c.a.aa` | `nonmembership_radius_error_le` | Exact delta^m compression-error bound at the chosen radius, for every positive natural m. Positivity of m is supplied eventually by the preceding theorem. |
| Uniform power estimate (lines 1511–1521) | `eventually_nonmembership_power_bound` | Assembles graph counts, small compressions, radius admissibility and the checked compression lemma to prove norm(a_n^m delta_x)<=2(2delta)^m uniformly in x on sufficiently large components. Only the source projection/approximation/modulus data remain as inputs. Global approximant transfer and coordinate trace/rank assembly are now included in the full nonmembership theorem. |
| Lemma `lem:trace` and citation at line 1382 | `trace_projection_estimate` | Full arbitrary finite-dimensional complex Hilbert-space statement. Exhibits the trace as a real scalar and proves the exact rank lower bound for every natural power, including zero. Checked spectral eigenvector bases and finite Jensen replace the spectral measure argument; Bessel handles the projection range. |
| Equation `Eq.1.sep.26.1.rain` | `trace_power_ratio_bound` | Exact factor-eight comparison from the stated rank lower bound and per-basis-vector power bound. These hypotheses are intermediate estimates in the source; the basis-vector estimate is now assembled below from the source projection and decay hypotheses. Coordinate trace/rank identification and global approximant transfer are now connected in the full nonmembership theorem. |
| Numerical contradiction after `Eq.1.sep.26.1.rain` | `trace_asymptotic_obstruction` | Checks natural-floor rounding, comparison of real-power exponents as component sizes diverge, and the logarithm ratio limit as delta tends to zero. The eventual component threshold may depend on delta. Geometric admissibility is now proved below. The global norm-closure nonmembership theorem is now complete under the source projection data. |
| Expander separation (lines 470–475) and its citation | `vertex_expansion_uniform_separation` | Derived directly from external vertex-boundary expansion. One κ>1 depends only on γ and gives min(relative sizes) ≤ κ^(-r/2) for all nonnegative real radii and all finite graphs with that expansion constant. Includes empty sets and radius zero. Repeated neighborhoods and short walks supply the proof; no asymptotic-expander citation is assumed. |
| Equation `Eq.t.t.e.tb` | `graph_diameter_le_log_card` | Exact 2 log(card X)/log κ diameter bound for the connected graph's shortest path metric, from its checked separation estimate. |
| Scalar step in `Eq.21.Aug.26.lb.2` | `sqrt_entropy_le_two_cuberoot` | Exact sqrt(δ log(1/δ)) ≤ 2 δ^(1/3), for every δ>0. This establishes the numerical step, not the good-subspace operator bound. |
| Equation `Eq.ddqd.q` | `entropy_mass_of_exponential_bound` | Proves monotonicity of t log(e/t) on (0,1] and the exact exponential entropy bound, retaining the source polynomial factor. |
| Final majorant step in `Prop.palpha.is.inQLalpha.exp` (lines 1366–1370) | `polynomialDecay_of_expander_modulus_bound` | The source square-root modulus majorant implies polynomial decay with one constant for every positive radius. The majorant is an explicit input to this intermediate theorem and is now proved for the source projection in the full membership proposition above. No subspace-existence claim is inferred from this calculation. |
| Theorem E (`thmE`) | `theoremE` | Full forward inclusion for uniformly locally finite metric spaces, and equality given a coarse disjoint union of finite connected graphs. The `CoarseGraphUnion` witness records a countable partition, finite connected graph fibers, exact shortest path metrics, and separation as n+m tends to infinity with n≠m. No auxiliary moment, compactness, or analytic hypotheses. |
| Theorem `Thm.Led.In.Band` | `exponentialQuasiLocal_subset_stripAnalyticPoints` | Full reverse inclusion. The diagonal graph-block proof combines with a checked Roe off-block remainder. Scalar normalization removes the contraction bound and norm closure gives the whole algebra. The reverse argument also works for pseudometric ambient spaces and does not need uniform local finiteness. |
| Off-block compactness, proof near line 1867 | `CoarseGraphUnion.exists_compact_offBlock` | Constructs the matrix-defined diagonal part and proves the remainder compact. Finite cut averaging gives a tail norm bound of four times the quasi-locality modulus. Finite-coordinate errors are compact, and their norm limit is compact. No external compactness result is assumed. The diagonal part is identified by its exact coefficients; separate SOT convergence notation is not asserted. |
| Coarse disjoint union definition, graph specialization (lines 457–468) | `CoarseGraphUnion` | Exact metric and eventual separation conditions for the finite connected graph case. Component indices start at zero, a harmless reindexing of the sequence. The generic finite-metric-space union and metric-independence assertions are now checked above. |
| Compression modulus inequality, line 1872 | `quasiLocalModulus_componentOperator_le`, `quasiLocalModulus_componentOperator_le` | Arbitrary coordinate compressions and isometric coordinate restriction do not increase the modulus, at every real radius. Coordinate inclusions are constructed as Hilbert-space isometries; restriction uses their adjoints. |
| Diagonal graph-block argument, lines 1868–1882 | `graph_blockDiagonal_part_mem_stripAnalyticPoints` | Constructs the diagonal part of an exponentially decaying contraction, proves its norm and modulus bounds, and proves membership in AP_strip for every coarse height. Finite connected graph fibers have their shortest path distances equal to ambient distances. Uniform finite-block moments are lifted and assembled with no extra moment assumptions. The off-block remainder, scaling, and final reverse inclusion are now also checked. |
| Lemma `Lemma.IterSlicing` | `graph_slicing_estimate` | Full finite connected graph result in the shortest path metric, with the least Lipschitz constant and exact factor 2(3 Lip(h))^k. All positive orders; constant heights included. The tail is indexed by n+2 and is proved summable using finiteness. |
| Exponential sum estimate, line 1877 | `exponential_moment_sum_bound` | Exact exp(c) k! / c^(k+1) bound and summability for c>0, via checked Mathlib integral comparison. |
| Uniform finite graph step, lines 1871–1882 | `coarse_graph_uniform_moments` | A single positive pair of factorial constants works for all finite graph contractions with the specified exponential modulus bound and unit-edge maps into the ambient metric space. This supplies the finite-block estimates; transfer to ambient operators is now checked below. The decay hypothesis is required only for r>0, as in the source. |
| Infinite block moment assembly, lines 1871–1882 | `stripExtension_of_fiber_moments` | Arbitrary coordinate partitions, exact local moment identities, and uniform factorial bounds imply a global strip extension. Global moment operators are constructed from bounded finite matrix forms. Local bounds are explicit inputs to this intermediate step and are discharged in the final theorem. Component-to-ambient transfer is now supplied by the graph-block theorem below. The supremum norm equality itself is not claimed here. |
| Lemma `Lemma.BandFromMoments` | `stripExtension_of_factorial_moments` | Full strip-existence assertion and every positive width below 1/B. Bounded moment operators satisfy exactly the source entrywise commutator powers, including k=0. Factorial growth gives Taylor convergence on the disk of radius 1/B. Translating disks along the real axis and comparing matrix coefficients gives local agreement, holomorphy on the open strip, and continuity on every smaller closed strip. Arbitrary X and real h; the separate A>0 hypothesis is unnecessary for this proof. |
| Equation `Eq.BinomialSlicing` | `iterate_diagonalCommutator_add` | Exact binomial expansion for arbitrary bounded complex diagonals. Proved by operator extensionality and the scalar binomial formula. |
| Equation `Eq.AdbBounds.223.0` | `iterate_diagonalCommutator_eq_sum_integerBand` | Every commutator order, including zero, expands as a finite weighted sum of bands. Explicit finite index sets cover all height indices and differences. This is the source finite-sum identity, not the final graph norm estimate. |
| Equation `Eq.AdbBounds.223.1` | `norm_integer_floor_band_le_modulus` | Rounding an L-Lipschitz height in mesh L, with L>0, gives band norm at most epsilon_a(abs(m)) whenever distances are natural-number-valued. Proved for every band index. This intermediate bound now feeds the complete graph slicing lemma below. |
| Theorem `Thm.Band.In.Led` and Theorem E, forward inclusion | `strip_analytic_hasExponentialDecay`, `stripAnalyticPoints_subset_exponentialQuasiLocal` | Full operator decay assertion and AP_strip ⊆ QL_exp. The proof combines the estimate outside a finite set with decay of each exceptional row and column, finite sums, and the exact three-term decomposition. No auxiliary estimates or outside hypotheses are assumed. The statement also holds for pseudometrics and handles the empty space. Taking norm closures preserves the source order of quantifiers. |
| Definition `Defi.AP_band` and following algebra claim | `stripAnalyticPoints`, `stripAnalyticPoints_algebra` | Closure after intersecting over all coarse real maps, with a positive width chosen separately for each map. Restriction to the smaller width handles sums and products; conjugate reflection gives adjoints. Closed-strip continuity and interior holomorphy are proved. This is a closed unital complex star-subalgebra for every coarse space. |
| Lemma `Lemma.BandStructure` | `IsStripExtension.translate`, `IsStripExtension.strip_norm_supremum` | Horizontal covariance on the closed strip and a finite supremum attained on its imaginary segment. No countability or boundedness hypothesis on h. |
| Lemma `Lemma.GapEstimate` | `gapEstimate` | Extended-real infimum and supremum with the author-authorized infinite right-hand side in unbounded cases, even if the weighted operator has norm zero. The finite case is proved by supported diagonal factorization. Arbitrary nonempty sets retained. |
| Internal claim at line 1650 | `weightedBound_closed_cover` | Closed countable cover of normalized 1-Lipschitz maps in the pointwise topology. Weighted bounded operators are characterized by finite matrix-form inequalities. Source positive indices use n+1. |
| Claim `Claim.g.hg.cg` | `exists_uniform_weighted_gluing` | Baire on the compact normalized Lipschitz space yields one index and a finite region. The gluing preserves a finite set of prescribed values and equals g/2+c outside that region, for every real 1-Lipschitz g. A checked Lipschitz extension replaces the source minimum formula; zero diameter is included. |
| Equation `Eq.28.aug.26.1` | `strip_decay_outside_finite` | Uniform exponential compression bound N exp(-r/(2N)) outside one finite exceptional set, for N>0, all real r, and arbitrary separated subsets, including empty ones. The exceptional row/column bounds and full forward inclusion are now proved as well. |
| Theorem B (`thmB`) | `theoremB` | Exact revised conjunction for every uniformly locally finite metric space: quasi-local=CP and Roe=AP. No growth assumption. The same-set exponential-growth metric has precisely the original controlled sets. |
| Proposition `PropNotInQLThereisCoarseNotInCPFlow` and Corollary `Cor.cstql=CP.metric` | `nonQuasiLocal_coarse_discontinuous`, `quasiLocal_eq_coarseContinuityPoints` | Full detection proposition and equality. Finite rank-one approximations show that deleting finitely many rows/columns changes an operator by a Roe operator. Finite ball neighborhoods and strong recursion produce separated blocks. A 1-Lipschitz real extension supplies the coarse height function. The proof also works for pseudometric spaces with the stated finite-ball bounds. |
| Internal claim at line 857 | `nonQuasiLocal_finite_buffer_witnesses` | One uniform positive lower bound survives every finite buffer and every radius. The existential witness epsilon is halved as in the source. Pointwise separation ≥R for every real R implies the source strict separation >r by taking R=r+1. Finite subsets witness every strict compression norm bound. |
| Introduction, uniform local finiteness | `UniformlyLocallyFinite` | For each positive real radius, a natural bound controls cardinalities of all finite closed balls. This is the usual ball-cardinality condition; open and closed ball formulations agree after increasing the radius. No uniform discreteness assumption is imposed. |
| Proposition `PropNotInQLThereisCoarseNotInCPFlow`, second half of proof | `separated_blocks_detect_discontinuity` | From the source’s separated blocks and uniform compression lower bound, produces a 1-Lipschitz coarse map with discontinuous orbit. Uses checked Lipschitz extension instead of the sum of ramps. Indices are n+1. Finite-block extraction and recursive separation are now proved as well, completing the proposition. |
| Lemma `lem:commutator` (Ozawa Lemma 6) | `quasiLocal_commutator_bound` | Exact constants 4 and 2, proved by disjoint coordinate blocks, finite integer bands, floor rounding, and norm perturbation. The proof applies to any relation and nonnegative epsilon; no citation is assumed. |
| Theorem `Thm.Quasi-LocalContainedContinuityPoints` | `quasiLocal_subset_coarseContinuityPoints` | Full quasi-local ⊆ CP inclusion for arbitrary coarse spaces. The proof applies the commutator estimate to the sine and cosine parts of each phase, using a direct estimate; the separate smoothing lemma is also now proved with its exact constants. The metric reverse inclusion is verified by the detection proposition. |
| Lemma `lem:detect` and Corollary `cor:detect` | `lipschitz_detect`, `infinitePropagation_lipschitz_detect` | Exact 1-Lipschitz and 1/9 detection bounds with a strictly increasing subsequence. Proved for arbitrary pseudometric spaces. The replacement proof treats bounded endpoint subsequences separately, orients escaping pairs individually, and uses distance to the second endpoints; no Ramsey result is assumed. |
| Theorem `thm:roeentire` and Theorem B, analytic equality | `finitePropagation_iff_coarse_entireExponential`, `uniformRoe_eq_exponentialAnalyticPoints` | Both directions of the operator characterization and the norm-closure equality are checked. Quantification is over all coarse real maps. Holds for arbitrary pseudometric spaces. The forward inclusion still holds for arbitrary coarse spaces. |
| Lemma `lem:allrates` | `entire_coefficient_all_rates` | Every positive exponential weight has a uniform finite coefficient bound. Detection and the exact entire coefficient formula at two imaginary times give the contradiction. Entire extensions are required only for 1-Lipschitz real maps. |
| Definition `Def.AP.entire.algebra` | `entireAnalyticPoints` | Norm closure of the intersection of entire points over all coarse real maps, in that order. |
| Definition `Defi.Exp.Growth` | `AtMostExponentialGrowth` | Uniform finite closed-ball cardinal bounds L^m for every positive natural m, with L>1; radius zero is not constrained. This directly expresses the supremum bound used in the paper. The standalone N_X function and its equivalence with this predicate are checked in VolumeApproximation. |
| Proof of Theorem B, exponential-growth step | `uniformRoe_eq_entireAnalyticPoints_of_exponentialGrowth` | Retained as an intermediate lemma. Uniform exponential volume bounds and all-rates coefficient decay yield summable row and column shell bounds; Schur estimates and truncation give norm approximation. The final theorem removes the growth hypothesis. |
| Lemma `lem:volume`, supporting approximation argument | `uniformRoe_of_summable_shell_bounds`, `finitePropagation_approximation_of_schur_tail` | General summable-shell approximation is checked and used by the growth theorem. The literal N_X/eta formulation and its exact factor-two tail error are additionally checked in volume_approximation. |
| Proposition `Prop.analitic.iff.finite.dh.prop` | `isEntireExponentialType_iff_finitePropagation` | Full equivalence for arbitrary X and real h, including unbounded h. Forward growth bounds give the precise propagation radius K. Conversely, finite propagation M yields the exact complex-time entries and norm bound norm(a) exp(M abs(Im z)); entire holomorphy and real-orbit agreement are checked. No local finiteness or extra regularity assumptions. |
| Equation fix2:eq.complexbound and the Boas citation | `norm_sum_exponentials_le`, `finiteOrbitForm_norm_le` | The required finite-exponential-sum Phragmen–Lindelof estimate is proved using Mathlib. Zero coefficients need no frequency restriction. Specializing to finite vector pairings yields the exact manuscript constant. This does not claim every assertion of the cited book theorem. |
| Equations Eq.19.Aug.26.tarde.2–3 and Arendt–Nikolski application | `matrixEntry_finitePropagationExtension`, `norm_finitePropagationExtension_le`, `differentiable_finitePropagationExtension` | The bounded form is extended in both variables from dense finite vectors and represented by a Hilbert-space operator. Scalar Schwarz bounds prove norm continuity; matrix-coefficient Cauchy formulas and the Cauchy power series prove operator-valued holomorphy. The full abstract separating-functional theorem is not assumed or claimed. |
| Definition `Def.AP.algebra.defi` and following algebra claim | `exponentialAnalyticPoints`, `exponentialAnalyticPoints_algebra` | Norm closure after intersection over all coarse real maps, exactly as in the manuscript. Sums, products, conjugate-reflected adjoints, and scalar operators have checked entire extensions and positive exponential bounds. The resulting closed unital complex star-subalgebra is proved for arbitrary coarse spaces. Equality with the uniform Roe algebra is now checked for metric spaces. |
| Proposition `Prop.xy.coordinates.ana.extension` and preceding uniqueness claim | `IsStripExtension.matrixEntry_eq`, `IsStripExtension.unique` | Exact coefficient formula on the full closed strip, including its boundary. A witness is an ambient function constrained only on the strip, using ContinuousOn and DifferentiableOn; values outside are unrestricted. The intervals [-δ,δ] and (-δ,δ) for the imaginary part express the closed strip and its interior for δ>0. Checked scalar identity theorem on the convex interior, boundary continuity, and operator extensionality. |
| Lemma `lem:compression` | `norm_pow_delta_le_compression` | Exact ball-compression bound for all natural powers, including zero. Checked support, norm, and accumulated error bounds for localized iterates; pseudometric generality causes no singleton-ball assumption. |
| Definition Defi.QLalpha and Section 5 inclusion chain | `polynomialQuasiLocal_algebra`, `decayAlgebra_inclusions` | Exact all-positive-radius polynomial bounds, positive constants, and positive exponents. Norm-closed complex star-subalgebras and all four inclusions are checked. Large-radius comparisons are extended to small radii using the operator norm; no asymptotic weakening of the definition. Strictness on expander unions is now proved unconditionally in Theorem D. |
| Definition Defi.QL.exp and Section 5 algebra claim | `exponentialQuasiLocal_algebra` | Exact exponential bounds for all nonnegative radii, positive constants and rates, followed by norm closure. Checked closed complex star-subalgebra and Roe/quasi-local inclusions. Polynomial comparisons are now proved in the inclusion-chain theorem. |
| Section 5, modulus algebra identities | `quasiLocalModulus_algebra` | All three stated identities, with exact constants. The product bound is proved more generally at r+s using independent radii. Pseudometrics and empty compression sets are allowed. The decay-algebra inclusion chain is now proved separately. |
| Lemma `Lemma.Duhamel` and the preceding Lipschitz-orbit claim | `duhamel_norm_le`, `lipschitzWith_diagonalFlow_of_commutator` | Full statement for arbitrary X, arbitrary real h (possibly unbounded), and all real times. `HasDiagonalCommutator h a b` means exactly that bounded operator b has entries (h(x)-h(y)) a_xy. The oriented integral is constructed on vectors using strong continuity, not assumed operator-norm continuity. Coordinate evaluation and scalar FTC identify the integral with the orbit difference. The exact constant is the norm of b. |
| Sections 4 and appendix, bounded diagonal functions acting on l2 | `diagonalMultiplierStarHom`, `diagonalMultiplier_isometry`, `diagonalMultiplier_mem_uniformRoe` | Concrete pointwise multiplication by complex l-infinity functions; unital, star preserving, isometric, and supported on the diagonal. Arbitrary X, including empty X. |
| Appendix, definition of ad and Eq.defi.adk.inductive (bounded diagonal case) | `matrixEntry_iterate_diagonalCommutator` | Iterated operator commutators have exactly (f(x)-f(y))^k times the original coefficient. Proved for complex bounded f, hence also real f. Unbounded h is not covered by this construction. |
| Eq.BinomialSlicing.bounds.1, Eq.BinomialSlicing.bounds.2, Eq.AdbBounds | `iterate_diagonalCommutator_bounds` | Both norm and quasi-locality modulus estimates, with exact factor (2L)^k, for every supremum-norm bound L. Compression commutes with bounded diagonal commutation. All real radii and arbitrary pseudometric spaces are allowed. The separate graph slicing argument is checked in graph_slicing_estimate. |
| Theorem `Thm.uRa.h.Points.Cont.Substructure` | `uniformRoe_inter_continuityPoints` | Full equality for arbitrary coarse spaces and arbitrary real h. The left side is the intersection with ambient norm-continuity points. Support-preserving Fejer averages extend to the Roe closure by operator-norm continuity. |
| Introduction, CP; Section 4 | `coe_coarseContinuityPointsStarSubalgebra`, `coarseContinuityPointsStarSubalgebra_isClosed` | Intersection over all coarse real maps, bundled as a closed complex star-subalgebra; metric specialization uses the checked coarse-map equivalence. |
| Section 4, Roe inclusion in CP | `uniformRoe_subset_coarseContinuityPoints` | For coarse h, every original entourage has bounded h-variation; the Roe continuity-substructure result applies. |
| Section 4, diagonal action on quasi-local operators | `diagonalFlow_mem_quasiLocal` | Coordinate projections commute with every diagonal unitary. Compression norms and the same (epsilon,E) bounds are preserved, with no coarseness assumption on h. Does not assert norm continuity in time. |
| Section 2.1, five coarse axioms | `CoarseStructure` | All five axioms; arbitrary set, no connectedness or finiteness assumptions. Relational composition has the manuscript's order. |
| Section 2.1, metric entourages | `CoarseStructure.ofPseudoMetric` | An entourage admits a finite real distance bound. Valid for pseudometrics, hence also metrics. |
| Section 2.1, coarse maps | `IsCoarseMap`, `IsCoarseReal`, `isCoarseReal_iff` | Exact image-of-entourage definition; equivalent bounded oscillation for the real target with its standard metric. |
| Introduction / Section 3, d_h | `realPullbackPseudoMetric_dist` | Distance is exactly abs(h(x)-h(y)); h need not be injective. |
| Definition `Definition.Eh.largest.coarse.substructure` | `CoarseStructure.restrictReal` | Entourages of the original structure with bounded h-oscillation. All five closure properties are proved. |
| Proposition `PropLargestCoarseStrucWithhCoarse` | `CoarseStructure.restrictReal_largest` | Includes inclusion in the original structure, coarseness of h, and maximality among every coarse substructure making h coarse. |
| Section 2.2, matrix coordinates | `HilbertSpace`, `Operator`, `delta`, `matrixEntry_eq_inner` | Complex square-summable families over any set and bounded complex-linear maps. Paper uses inner product linear in the first variable; Mathlib uses linearity in the second, so arguments are reversed in the checked identity. |
| Introduction / Section 2.2, propagation | `operatorSupport`, `HasControlledPropagation`, `HasFinitePropagation`, `controlled_iff_finitePropagation` | Nonzero coefficients define support. Positive-radius finite propagation is equivalent to controlled support in the metric coarse structure. |
| Section 2.2, uniform Roe definition | `uniformRoe_algebra`, `uniformRoe_metric_eq` | Exactly the operator-norm closure of controlled operators, agreeing with closure of finite-propagation operators. The closed unital complex star-subalgebra structure is checked for arbitrary coarse spaces. Zero-error compression estimates prove support closure under products, sums, and adjoints. |
| Proof of `Thm.uRa.h.Points.Cont.Substructure` | `uniformRoe_restrictReal_subset` | The inclusion following from E_h being a substructure, used in the full equality below. |
| Introduction / Section 2.2, coordinate projections | `coordinateProjection_eq_self_iff` | Orthogonal projection onto the closed subspace of vectors vanishing outside A; its fixed vectors are exactly that subspace. |
| Section 2.2, quasi-local algebra | `IsQuasiLocalAt`, `IsQuasiLocal`, `quasiLocalStarSubalgebra_isClosed` | Exact entourage definition, now bundled as a norm-closed unital complex star-subalgebra for arbitrary coarse spaces. Multiplication uses relational composition and projection splitting, with no metric or local finiteness assumption. |
| Section 2.2, Roe inclusion | `uniformRoe_subset_quasiLocal` | Proved for every coarse space, without local finiteness. A rectangle disjoint from the operator support gives a zero compression. Closure then uses norm-closedness of quasi-locality. |
| Section 2.2, metric quasi-locality | `isQuasiLocal_iff_metric` | Entourage and positive-radius definitions agree. Separation means all pointwise distances are at least the radius, also covering empty subsets. Works for arbitrary pseudometric spaces. |
| Definition `Defi.QL.Decay.modulus` | `quasiLocalModulus` | Supremum of norms of separated compressions; nonemptiness, boundedness, and nonnegativity are proved. The real-input definition agrees with the paper on nonnegative radii. |
| Example `Example.decay.ql` | `isQuasiLocal_iff_modulus_tendsto` | Exact equivalence between quasi-locality and the modulus tending to zero at positive infinity. |
| Example `Example.decay.uRa` | `finitePropagation_iff_modulus_eventually_zero` | Exact equivalence between positive-radius finite propagation and eventual vanishing of the modulus. |
| Introduction / Section 3, diagonal conjugation | `diagonalFlow`, `diagonalFlow_zero`, `diagonalFlow_add`, `diagonalFlow_norm`, `matrixEntry_diagonalFlow` | Concrete diagonal phase multiplication on complex l2, conjugation, group law, exact norm preservation, and the exponential matrix formula. No boundedness/coarseness assumption on h. |
| Section 4, invariance of the uniform Roe set | `diagonalFlow_mem_uniformRoe` | The diagonal conjugation preserves support, hence controlled propagation; continuity in the operator argument passes this to the norm closure. This is not continuity in the time argument. |

| Introduction, diagonal pre-flow | `diagonalFlowEquiv`, `diagonalFlowEquiv_apply` | Bundled complex star automorphism agrees with the concrete conjugation; adjoints of the diagonal unitaries are their inverse-time operators. |
| Introduction, diagonal continuity algebra | `continuityPointsStarSubalgebra_isClosed`, `coe_continuityPointsStarSubalgebra` | Closed unital complex star-subalgebra with exactly the norm-continuous orbits as carrier. The general arbitrary-C*-algebra claim is now checked by continuousOrbitSubalgebra_isClosed above. |
| Introduction, continuity points | `mem_continuityPoints_iff_continuousAt_zero` | Group law transports continuity at zero to every time. This does not say every operator is a norm-continuity point. |
| Section 3, strong and weak continuity | `continuous_diagonalUnitary_apply`, `continuous_diagonalFlow_apply`, `continuous_inner_diagonalFlow` | Arbitrary X and h, including unbounded h. Finite-sum approximation and the uniform norm bound prove strong continuity directly; joint continuity gives strong conjugation continuity and then weak continuity. No invocation or assumption of Stone's theorem. |

| Section 3, weak average Theta | `averagingOperator`, `inner_averagingOperator`, `averagingOperatorL1_toL1` | Integrates each vector orbit for arbitrary X and h. The bounded linear operator has the exact weak identity. Almost-everywhere equality of kernels gives equal averages, and the L1-class version agrees with every integrable representative. Inner-product arguments are reversed to preserve the manuscript's scalar convention. |
| Equation `Eq.BoundNormThetafa` | `averagingOperatorL1_norm_le` | Exact bound by the L1 norm times the operator norm, with no continuity assumption on the operator orbit. |
| Equation `Eq.Theta.Schur.mult` | `matrixEntry_averagingOperator`, `fourierPlus` | Positive exponential sign and no 2 pi factor, exactly as in the paper. The entry is the Fourier transform at h(x)-h(y) times the original entry. |
| Equation `Eq.1.03.Aug.26` | `averagingOperator_sub_norm_le` | For norm-continuity points and an integrable kernel of mass one; also holds for complex kernels with their absolute value. This is the general error bound; Fejer convergence is checked separately below. |
| Theorem A proof, averaging inside A | `averagingOperator_mem_invariant_subalgebra` | Norm-continuity points have operator-valued Bochner averages, and those remain in each invariant norm-closed complex star-subalgebra. Uses a nonunital subalgebra type to avoid adding a unit hypothesis. |
| Equation `Eq.Fejér.kernel` | `fejerKernel`, `fejerKernel_zero`, `integrable_fejerKernel` | Real nonnegative kernel with the continuous sinc value at zero. Integrability proved by an explicit constant multiple of (1+t^2) inverse. Mass one and the Fourier transform are checked below. |
| Approximation proof, pointwise tail estimate | `fejerKernel_tail_bound` | K_s(t) <= 2/(s pi t^2) for every s>0 and t nonzero. The exact integrated tail estimate is now checked above; the Fourier transform is checked below. |

| Equation `Eq.2.03.Aug.26`, mass | `integral_fejerKernel`, `integral_norm_fejerKernel` | Mass and L1 norm equal one at every positive scale. Obtained by Fourier inversion of the triangular convolution, with all integrability hypotheses checked. |
| Equation `Eq.2.03.Aug.26`, Fourier transform | `fourierPlus_fejerKernel` | Exactly max(1-abs(xi)/s,0), with positive exponential sign and no 2 pi factor. Computes the interval-indicator Fourier transform, its convolution as the triangular function, and applies Mathlib inversion; no transform identity is assumed. |
| Lemma `Lemma.support.ThetaKsa` | `matrixEntry_fejerAverage_eq_zero` | All matrix coefficients vanish at distance greater than s in d_h. Arbitrary X and h; no boundedness, countability, or metric separation assumptions. |
| Lemma `Lemma.ThetaKs(a).tends.to.a` | `tendsto_fejerAverage` | Operator-norm convergence as real scales tend to positive infinity. Change of variables gives a fixed K_1 integrable majorant; dominated convergence uses norm continuity of the orbit at zero. This replaces the explicit integrated-tail calculation in the written proof. |
| Theorem A, forward inclusion | `continuityPoint_mem_closure_finitePropagation` | Exact inclusion for every invariant closed complex star-subalgebra, including nonunital ones. Uses finite propagation and norm convergence of Fejer averages, together with their membership in the subalgebra. The reverse inclusion and full equality are checked below. |

| Section 3, translation covariance | `fourierPlus_translate`, `diagonalFlow_averagingOperator` | Translating the kernel by t-r multiplies its transform by exp(i r xi), and conjugating an average translates the kernel. Valid for every integrable complex kernel. |
| Equation `Eq.5.03.Aug.26` | `integral_norm_valleePoussin_le`, `fourierPlus_valleePoussin_plateau` | Exact L1 bound of three and transform equal to one on the closed interval [-s,s]. The kernel is 2 K_(2s)-K_s, viewed in complex scalars. |
| Theorem A proof, kernel translations | `tendsto_integral_norm_translate_sub`, `valleePoussin_has_integrable_bound` | Dominated convergence proves L1 translation continuity for continuous kernels bounded by C/(1+t^2); the de la Vallee Poussin kernel has this checked bound. No general L1 translation theorem is assumed or claimed. |
| Theorem A proof, reverse inclusion | `averaging_valleePoussin_eq_self`, `finitePropagation_mem_continuityPoints` | Fourier plateau reproduces all finite d_h-propagation operators. Averaging covariance and the L1 norm estimate then prove their norm-continuity. |
| Theorem A | `theoremA` | Both assertions: the ambient equality with the d_h uniform Roe closure and the equality inside every invariant closed complex star-subalgebra. Arbitrary X and real h; A may be nonunital. The equalities concern underlying sets of operators with their operator-norm topology; continuity of A-valued orbits agrees with ambient continuity by the subspace topology. |

`BoundedVariation` uses an existential finite real bound, rather than Lean's
totalized real supremum, which would not encode boundedness. Since
`Real.dist_eq` identifies real distance with absolute difference, this preserves
the manuscript's bounded-oscillation condition, including empty entourages.
No project axiom, proof placeholder, or external mathematical hypothesis is used.

The registered roots are the checked manuscript statements in the table, including
prose identities, the explicit inclusion in the Section 4 proof, and the full
Theorems A and B. All five named theorems A–E now have complete checked proof chains. Supporting declarations
are separately registered.

`compression_norm_le`, `compression_sub_norm_le`, and `IsQuasiLocalAt.perturb`
are the norm estimates supporting quasi-local norm-closedness. Orthogonal
projection existence uses Mathlib's closed-submodule projection theorem in the
complete complex Hilbert space. The closure proof chooses a quasi-local
approximant at distance less than epsilon/2 and an entourage at tolerance
epsilon/2; their two errors sum to less than epsilon.

The new modulus proofs use all subsets of X, not just finite subsets. The
supremum's defining set is nonempty even when X is empty, and all compression
norms are bounded by the operator norm. No unsupported use of a conditionally
complete real supremum occurs. Antitonicity makes an arbitrarily small modulus
value into an eventual bound. For finite propagation, increasing a propagation
radius R to R+1 handles the strict/non-strict separation boundary. Conversely,
singleton compressions show that a zero modulus forces all entries at that
separation to vanish. Operator extensionality uses Mathlib's density of the
coordinate vectors in l2, without a countability assumption.

`DiagonalFlow.lean` constructs diagonal multiplication using Mathlib's `lp.mapCLM`:
each scalar phase has norm one, giving a uniform norm bound even for unbounded h.
The addition law and zero-time identity establish inverse conjugations, and the
two norm-contraction estimates establish exact preservation of operator norm.
The coefficient formula is exp(i t (h(x)-h(y))) times the original entry; the
complex exponential never vanishes, giving equality of supports. `DiagonalStar`
adds the adjoint identity and bundled star automorphisms. `ContinuityPoints`
constructs their closed norm-continuity subalgebra. `StrongContinuity` proves
strong continuity by finite-sum approximation; no countability assumption on X
is needed. The identification of norm-continuity points with the Roe algebra
is now proved in `TheoremA`, together with its invariant-subalgebra generalization.

## Reviewed manuscript conventions

1. **Gap estimate (`Lemma.GapEstimate`, line 1617).** Nonempty A and B need not
   have finite inf h(A) and sup h(B). On 2026-09-21 the author explicitly chose
   **extended-real bounds**, retaining arbitrary nonempty sets. The finite-bound
   case is now proved by supported diagonal factorization; unbounded cases
   have an explicitly infinite right-hand side in the extended nonnegative codomain.
   The lemma is verified. No manuscript edit has been made.
2. **Baire/gluing proof (around lines 1669–1703).** The finite neighborhood set
   is named I, then the diameter and gluing formulas use F without defining it.
   The formalization consistently uses the chosen finite set S in both places.
   The checked extension proof handles diameter zero as well. This records the
   interpretation of the source typo; the manuscript remains unchanged.
3. **Index and analytic conventions.** The source distinguishes N from
   N union {0}; positive-index statements must not silently become statements
   at zero. The Fejer formula at zero requires its continuous sinc extension.
   Balls are explicitly closed before `lem:compression` (line 1399).
   These conventions must be reflected in the relevant definitions.

## Completed dependency work

The verified theorem chains include A–E, both coarse-space continuity
substructure equalities, the literal volume lemma, general weak integration,
coarse remetrization and growth, and the exact Fejer tail estimate. The original
alternative proofs using density, dominated convergence or direct selection
remain checked; the additional source estimates now have their own proofs.

The cited Li–Zhang–Zhu Proposition 6.3 is now proved unconditionally with
constant32. Gaussian ratio concentration, its Haar-sphere identification, the
complex half-net and the finite union bound are all checked. Both appendix
good-subspace existence lemmas are unconditional (constants96 and32). Their
projection and expander-algebra consequences are checked, including the literal
Assumption.1 construction and unconditional Theorems C and D.

Ozawa's nonembedding theorem is proved, including nonunital embeddings. Finite
irreducible unitary representations, Schur averaging, both amplification
bounds, coordinate/tensor identification and the infinite bounded-product
diagonal contradiction are checked. Theorem D combines this with the actual
expander embedding and strict decay chain; Theorem C follows using Theorem E.

The exact smoothing lemma, maximal-ULF coarse-space example and partial-translation
decomposition are now checked. The final prose review and both wording qualifications are complete. Positive expansion proves preconnectedness even for an empty graph. A checked
adapter enumerates occupied labels of the literal raw sequence on the same
metric space, yielding the nonempty connected bundle while preserving all
constants, separation and divergence. This correspondence issue is resolved.

## Completion review of additional prose

The 2026-09-28 reread identified prose obligations beyond the statement
environments: bijective coarse invariance of the dynamical algebras, the
Property A equality and collapse of intermediate algebras, general-flow density
of entire analytic elements, the named Lipschitz/differentiable regularity
algebras, and actual counterexamples to metric-decay coarse invariance. These
now have explicit inventory entries; mathematical background assertions have
not been dismissed as historical citations.

The countable-approximation assertion at lines 175–177 now explicitly assumes
infinite X. `uniformRoe_not_subset_closure_countable` proves it for every coarse
structure, even when the countable family contains arbitrary ambient operators.
The revised manuscript removes the old graph-union growth caveat and special
remetrization remark. Their dedicated proof modules have been removed. The new
DGLY proposition instead supplies a degree-three graph embedding for every ULF
metric space. Pulling back its graph metric along the injective root map gives
exponential growth on the same set, with exactly the original coarse structure.
This establishes the growth reduction without asserting invariance of concrete
operator algebras under arbitrary nonbijective coarse equivalence.

The introduction's reference to “all h” is read under the paper's explicit global
convention (Section 2.1) that real-valued maps are coarse, consistently with
Theorem `thm:roeentire`. The proof of Theorem B is implemented using the injective
embedding's image. Suggested wording clarifications were sent to the author;
the manuscript itself has not been edited for this update. These interpretations
are recorded explicitly, rather than strengthening either formal statement.

The positive prose obligations are now checked: `analyticOrbitSubalgebra_dense`
proves general-flow analytic density for nonunital C*-algebras;
`uniformRoe_eq_quasiLocal_of_propertyA` proves the Property A equality through
finite probability kernels, clipping and finite-sign averages; and
`regularityPoints_between_Roe_quasiLocal` handles the named Lipschitz,
differentiable and C^k norm-closure constructions. Spatial relabeling proves
bijective coarse invariance for all the dynamical constructions. The Property A
proof supplies the cited complex Hilbert-space application; it does not claim
to formalize every broader Banach-space result in the cited papers.

The final pass additionally checks the finite-generation Cayley-graph examples:
`finitelyGeneratedGroup_cayley_geometry` proves both uniform local finiteness
and exponential growth in the actual shortest-path metric. `CoarseStructure.IsMetrizable`
uses genuine metrics, and `maximalULF_not_metrizable` certifies the introduction's
nonmetrizable example. `exists_discontinuous_diagonal_preflow` supplies a literal
quadratic-height/unilateral-shift witness for the norm-discontinuity assertion.

The quantitative decay noninvariance assertions now have concrete counterexamples,
including a constructed expander family. No expander-existence premise remains.
The square-root metric changes every positive polynomial exponent, and the
logarithmic metric strictly enlarges the exponential-decay algebra while keeping
the same coarse structure and uniform local finiteness.


## Revised graph construction and Theorem B

`exists_boundedDegree_coarseEmbedding` proves the cited DGLY Proposition 5.1
inside the project. A countable cover of bounded relations by finite partial
matchings is placed on rays indexed by X. Each vertex has at most two vertical
neighbors and one matching neighbor. Every pair of roots is connected. A
matching at level n gives a walk of length 4n+2; a walk of length k from a root
has original displacement at most k². These estimates prove both coarse
controls. The empty domain embeds in the one-vertex graph.

`exists_exponentialGrowth_metric` restricts the graph metric to the roots.
Degree-three ball counting bounds its volumes, and the two controls identify
its controlled sets with the original ones. Consequently
`uniformRoe_eq_entireAnalyticPoints` removes the growth assumption from the
previous analytic lemma. `theoremB` has exactly the two revised equalities;
`entireAnalyticPoints_eq_exponentialAnalyticPoints` supplies the new corollary.
The merged definition `Def.AP.algebra.defi` is represented by both
`entireAnalyticPoints` and `exponentialAnalyticPoints`.

The two new Ewert–Meyer citations are historical attributions to instances of
already checked continuity results. No external theorem is taken as an axiom.

## Final validation — 2026-09-29

The full build, all 17 audit regression tests, ordinary audit and terminal audit
pass. All 1,328 inventory entries are verified. The dependency audit checks that
all 1,288 source declarations in 194 modules support the 136 manuscript roots.
Only `propext`, `Classical.choice` and `Quot.sound` occur as foundational axioms;
there are no project axioms or proof placeholders.

Reviewed manuscript SHA256: `2afdc5e2011fb9f96e73b4c9125c5f9a7e32cd3e122678d6221dc31082f1eab9`.
