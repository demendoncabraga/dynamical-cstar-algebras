# Formalization and verification record

## Reviewed mathematical scope

Theorems A–E, supporting definitions and results, coarse-space generalizations,
and required cited mathematical dependencies are proved. The source review covers
63 mathematical statement environments, 32 citation occurrences, and mathematical
prose/background assertions. Questions and conjectures are not claimed as results.

All 1,325 inventory entries are verified. There are 1,287 distinct source
declarations in 193 proof modules, supporting 138 manuscript roots. Every source
declaration is registered and belongs to the checked dependency closure of those
roots, including elaboration dependencies recorded in Lean's source index.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed foundational
axioms. The verification scope is unconditional: cited results required by the
proofs are supplied by Mathlib or proved within this project.

## Resolved manuscript conventions

- The author chose extended-real bounds for `Lemma.GapEstimate` on 2026-09-21.
  Unbounded image sets retain an infinite right-hand bound; no boundedness
  assumption was added.
- The author's infinite-space qualifier for countable approximation is proved
  by `uniformRoe_not_subset_closure_countable` in `RoeCountability.lean`.
- On 2026-09-28 the author approved the remetrization qualification at line 922.
  The exponential-growth remetrization theorem and a counterexample in the
  original metric verify the corresponding prose assertions.

The exact reviewed manuscript SHA256 is
`c98f4f45f7b9028824915228714a6fc7254dda7e10699cb206ebd5d9d5aa6c72`.
Further conventions and the result-by-result review are in
`docs/SOURCE_COVERAGE_REVIEW.md`.

## 2026-09-28 — Terminal completion

The full build, all 12 then-current audit regression tests, ordinary axiom audit,
and terminal completion audit passed. The terminal check verified the source
fingerprint, complete coverage, allowed axioms, and source dependency closure.
Lean and Mathlib remain pinned to v4.33.1.

## Publication preparation

Moved the generated axiom-checking file to ignored `.lake/audit/`, reduced the
entry point to terminal-module imports, and retained all proof modules and their
provenance. Consolidated the resolved manuscript notes into the source review
and replaced the incremental working log with this verification record.
Added a reproduction guide, a Theorems A–E source map, and a GitHub verification
workflow. The audit now explicitly validates the reviewed dependency pins;
five additional regression tests exercise pin drift and unlocked dependencies.
Licensing remains undecided at the author's request.

Publication validation passed:

- All 17 audit regression tests.
- Ordinary and terminal audits in the working checkout.
- A separate source-only copy rebuilt all 193 project proof modules and the
  library entry point, then passed the terminal audit. Only pinned third-party
  dependency caches were reused; no compiled project proofs were copied.
- Source equality between the independent copy and the working checkout,
  manuscript fingerprint, relative documentation links, shell syntax, workflow
  YAML parsing, ignored-artifact rules, and publication file inventory.

The GitHub workflow has not yet run on a hosted runner. Initial network downloads
were not repeated during the isolated local rebuild. No remote publication or
change to the surrounding repository's Git history was performed.
