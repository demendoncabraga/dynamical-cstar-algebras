# Verification scope

The target is *Dynamical C*-algebras and coarse geometry*, `paper/main.tex`.
Coverage includes Theorems A–E, supporting definitions and results, the
coarse-space generalizations, and required appendix dependencies. The manuscript
has the reviewed countability qualification and unconditional Theorem B; Lean/Mathlib
v4.33.1 pins are unchanged.

Theorems **A–E are verified**, including all cited mathematical dependencies in
their proof chains. The inventory review covers all 62 statement environments,
35 citation occurrences, and mathematical prose/background definitions.
The revised graph-embedding proposition and analytic-algebra corollary are included.
See [resolved manuscript qualifications](SOURCE_COVERAGE_REVIEW.md#completion-review-of-additional-prose).

## Checked results

The foundations cover arbitrary coarse structures, coarse maps and equivalences,
metric coarse structures, restriction by a real height, and uniform local
finiteness with the exact symmetric-entourage definition and metric equivalence.
The complex l2 operator model, coordinate projections, controlled propagation,
uniform Roe algebra and quasi-local algebra are implemented. Both algebras have
checked closed complex star-subalgebra structures. Metric quasi-locality agrees
with the entourage definition and with vanishing of its compression modulus.

The diagonal action has checked group, star-automorphism, norm and matrix-entry
identities, and strong/weak continuity for arbitrary real heights. Continuity
points form a closed complex star-subalgebra; the general assertion for arbitrary
C*-automorphism families, including nonunital C*-algebras, is also proved.
The general Hilbert-space weak integral exists uniquely whenever its scalar
coefficients are integrable and the integrated sesquilinear form is bounded.
No separability or operator-norm integrability is imposed.

The Fejer kernel has its continuous value at zero, integrability, mass one,
triangular Fourier transform and exact integrated tail estimate. Averaging gives
finite height propagation and norm convergence. Theorem A includes invariant
closed complex star-subalgebras without a unit assumption. Both the uniform Roe
and quasi-local continuity-substructure equalities hold for arbitrary coarse
spaces and arbitrary real heights. The quasi-local proof explicitly preserves
each tolerance/entourage estimate under Fejer averaging.

Theorem B proves quasi-local = common coarse continuity points and Roe = entire
analytic points for every uniformly locally finite metric space. Exponential
growth is no longer a hypothesis. A directly proved degree-three graph embedding
supplies an equivalent metric with exponential growth on the same set. The new
corollary identifies the entire and exponential-type analytic closures. Finite witnesses, buffer removal and separated-block
selection construct the height detecting non-quasi-locality. The literal volume
lemma now includes the exact supremum definitions of N_X and eta_a, the stated
factor-two tail at every cutoff, and Roe membership.

Theorem E identifies strip analytic points with exponential quasi-locality on
coarse unions of finite connected graphs; the forward inclusion holds for all
uniformly locally finite metric spaces. Its proofs include the Baire/gluing
argument, the author-approved extended-real gap estimate, graph slicing,
factorial moment bounds, strip extensions, compact off-block remainders and norm
closure. Strip and entire analytic predicates, algebra closure, extension
uniqueness and the entrywise iterated-commutator recursion are checked, retaining
unbounded heights and explicit bounded-operator existence conditions.

Generic finite coarse disjoint unions are independent of cross-component metric
choices up to bijective coarse equivalence. Uniformly locally finite
large-scale geodesic spaces also have exponential growth; the checked definition
uses bounded-step chains with an affine length bound. Connected shortest-path
graphs supply the graph/Cayley special case.

## Checked expander theorems

Positive vertex expansion gives preconnectedness, and connectedness for nonempty
graphs. Uniform degree, expansion and diverging component cardinalities are
bundled; coarse separation and bounded degree give uniform local finiteness.
The separation, diameter, graph-ball, entropy, compression, trace, rounding and
asymptotic estimates required by the expander argument are proved.

`Prop.palpha.is.inQLalpha.exp` and `Thm.QLthetaDoesNotContainP` are verified under
the exact projection data stated in Assumption.1. The membership proof establishes
the ambient polynomial modulus. The nonmembership proof includes self-adjoint
approximation and the full norm-closure trace contradiction. A supplied family
of component orthogonal projections has a checked global orthogonal projection
as its strong sum, with exact restrictions to every component.

From the actual prescribed projection data, the strict decay-algebra inclusions
are proved. From actual good subspaces with the exact quarter-power dimensions
and compression bounds, an injective isometric nonunital star-algebra map from
the bounded product of complex matrix algebras into the ambient operator algebra
is constructed; every image is exponentially decaying. The product is modeled by
`lp` at infinity, not by the unrestricted algebraic product. The uniform source
estimate has its exact constant 2*C and exponent -r/24. Both appendix reductions
from the cited frame bound are checked with their exact ranks and constants.

The complex frame-subspace existence theorem is now proved unconditionally with
universal constant32. The proof constructs Haar probability, proves Gaussian
quadratic exponential moments and coordinate-ratio concentration, identifies
the normalized Gaussian with the Haar sphere law, and applies the checked
complex half-net and finite union argument. No concentration theorem or external
existence result is assumed. The two good-subspace existence consequences, source Assumption.1 projections,
and full unconditional expander assembly are checked.

Ozawa's finite-dimensional obstruction is now proved: for each controlled
entourage, sufficiently large matrix algebras contain a contraction staying at
least1/2 from every controlled operator even after adding any complementary
contraction. Finite irreducible representations, Schur averaging, coordinate/tensor
identification and both amplification bounds are checked. The bounded-product
nonembedding theorem is proved by a diagonal contradiction over cofinal
controlled entourages, including nonunital embeddings. Theorems C and D follow
with all strict inclusions and the bounded matrix-product embedding.

The exact smoothing lemma is proved, including its stated radius and constants,
using an explicit cosine partition and finite-sign orthogonality. Both conclusions
of the height-band claim are checked. Controlled operators on arbitrary uniformly
locally finite coarse spaces admit the finite partial-translation decomposition,
including the partial-isometry and entire exponential analytic assertions.

The maximal ULF coarse-space example is proved on literal ℕ: coarse heights are
exactly bounded functions, all operators are common continuity points, and a
constructed flat-row operator is not quasi-local.

A checked adapter now removes empty component labels on the same metric space,
preserving graph constants, separation and cardinal divergence. Property A implying Roe = quasi-local is checked using finite probability
kernels and an explicit 18t approximation estimate. Entire analytic elements
are proved dense for arbitrary norm-continuous flows on possibly nonunital
C*-algebras. The norm closures of common Lipschitz, differentiable and C^k
orbits are checked closed star-algebras between Roe and quasi-local, and all
these dynamical constructions are proved bijective coarse invariants.
Explicit metric-decay noninvariance examples are checked, using an actual
constructed expander family and square-root/logarithmic changes of metric.
Cayley-graph ULF/growth, coarse metrizability, the nonmetrizable coarse example
and an explicit norm-discontinuous diagonal pre-flow are also checked. For infinite
spaces, a diagonalization proves the countable approximation obstruction.
See `lean/coverage.json` for individual statuses.

## Verification standard

The ordinary audit checks the build, manuscript fingerprint, dependency pins,
registered declarations and their foundational axioms. The dependency audit
checks that every project declaration is registered and lies in the dependency
closure of a genuine manuscript root. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. No `sorry`, project axiom or external-result assumption
is admitted. Mathematical correspondence is reviewed separately in
`SOURCE_COVERAGE_REVIEW.md`.

Latest validation (2026-09-29): the full build, all 17 audit regression tests,
ordinary audit and terminal audit pass. All 1,328 inventory entries are verified;
1,288 source declarations in 194 modules support 136 manuscript roots. The
reviewed source SHA256 is `c9b6926f5d053ee24f2755f94015d9de77094bcc1b47e32ea21a655382f0f699`.
The audit verifies dependency closure and permitted axioms. The previous public
version additionally passed a separate source-only rebuild; for this revision,
Lake rebuilt the changed modules and affected dependents in the working checkout.
Hosted GitHub Actions status is separate from these local checks.
