# Formalization and verification record

## Current reviewed scope — 2026-09-29

Theorems A–E, supporting definitions and results, coarse-space generalizations,
and required cited mathematical dependencies are proved. Review covers all
62 mathematical statement environments, 35 citation occurrences and mathematical
prose/background assertions. Questions and conjectures are not claimed as results.

All 1,328 inventory entries are verified: 1,288 source declarations in 194 proof
modules support 136 manuscript roots. Every declaration is registered and belongs
to their dependency closure, including elaboration dependencies in Lean's index.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted foundational
axioms. Cited proof dependencies are supplied by Mathlib or proved in the project.
Lean/Mathlib remain pinned to v4.33.1.

Reviewed manuscript SHA256:
`2afdc5e2011fb9f96e73b4c9125c5f9a7e32cd3e122678d6221dc31082f1eab9`.

## Revised Theorem B and graph embedding

Theorem B now states quasi-local = CP and uniform Roe = AP for every ULF metric
space, without exponential-growth assumptions. The cited DGLY Proposition 5.1 is
proved directly using partial matchings on rays, a connected graph of degree at
most three, and both distance controls for its injective root embedding. The
empty-space case is included. Pulling back the graph metric gives exponential
growth and precisely the same coarse structure on X. The former growth theorem
is retained only as an intermediate analytic lemma. The new AP = AP_exp corollary
is checked, and the merged AP/AP_exp definition is reflected in the inventory.

Removed three obsolete proof modules: CoarseRemetrization,
GraphUnionExponentialMetric and SingletonGrowthCounterexample. Their manuscript
passages were removed by the author. Split the early quasi-local characterization
from final Theorem B to keep imports acyclic; made the coordinate-embedding import
explicit in HaarFrameSubspaces. Refreshed source locations, manuscript roots,
citation review, README and the requested definitions reading extract.

The manuscript was preserved exactly as supplied. The source review records the
global coarse-height convention and the injective-image interpretation of the
growth reduction. Suggested prose clarifications have not been applied without
author approval. See `docs/SOURCE_COVERAGE_REVIEW.md` for the precise correspondence.

Validation passed: full library build, all 17 audit regression tests, ordinary
axiom audit and terminal audit. The terminal check verifies the source fingerprint,
complete coverage, allowed axioms and source dependency closure. Lake rebuilt the
changed modules and affected dependents; initial dependency downloads were not
repeated. Hosted workflow status is not inferred from local validation.

## Established conventions and publication

- The author chose extended-real bounds for Lemma.GapEstimate on 2026-09-21.
  Unbounded images retain an infinite right-hand bound; no boundedness hypothesis
  was added.
- The author's infinite-space countability qualification is checked by
  uniformRoe_not_subset_closure_countable.
- The previous version passed terminal completion on 2026-09-28 and a separate
  rebuild of all then-current 193 proof modules from source using pinned Mathlib
  caches. It was published at
  https://github.com/demendoncabraga/dynamical-cstar-algebras.
- Build artifacts and generated audit files stay under ignored .lake/; the public
  sources include pinned dependencies, setup instructions and a GitHub workflow.
  Licensing remains undecided at the author's request; provenance is preserved.
