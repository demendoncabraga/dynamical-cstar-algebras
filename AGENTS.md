# Repository guidelines

The authoritative manuscript is `paper/main.tex`, *Dynamical C*-algebras and
coarse geometry*. Preserve it unless the author requests changes. The Lean
library is `DynamicalCStarAlgebras`, under `lean/`, pinned to Lean/Mathlib v4.33.1.
Keep dependency pins unchanged unless the user requests an upgrade.

## Scope and mathematical integrity

The intended scope is the current paper, including Theorems A–E, its supporting
results, and the coarse-space generalizations. The reviewed formalization is complete.
Maintain the inventory of manuscript definitions, results, and cited dependencies
when changing the source or proofs; do not infer coverage from build success alone.
Do not attempt to prove questions or conjectures as established results.

Do not add project axioms, proof placeholders, external hypotheses, or silently
weaken statements. Cited results must be supplied by checked Mathlib theorems or
proved within the project. No external mathematical assumptions are authorized.
If an ambiguity or missing external result blocks progress, record it and report
it to the author; a citation alone is not a checked proof.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted foundational
axioms. Preserve scalar fields, quantifiers, generality, and regularity conditions
from the manuscript. Report mathematical ambiguities rather than guessing.

## Organization and verification

Use `lean/DynamicalCStarAlgebras/` for project modules and import them from
`lean/DynamicalCStarAlgebras.lean`. Use two-space indentation in Lean.
Keep `lean/coverage.json`, `docs/SOURCE_COVERAGE_REVIEW.md`,
`docs/VERIFICATION_SCOPE.md`, and `lean/FORMALIZATION_LOG.md` accurate.
Every inventory item needs a unique `id`, `status` (`not_started`, `in_progress`,
or `verified`), and a source reference/description; a verified item also needs
its qualified `declaration`. Register proof dependencies as well as paper results.
`paper_roots` lists the final manuscript declarations, not arbitrary helper lemmas.
Keep the root list in `scripts/DependencyAudit.lean` consistent with it.
Update `source_sha256` after reviewing any authorized manuscript change.

Validate from the repository root:

```sh
python3 scripts/test_audit.py
sh scripts/audit.sh
```

The ordinary audit checks build readiness and registered declarations. It is not
a completion certificate. Once the full inventory and all proofs are complete:

```sh
sh scripts/audit.sh --terminal
```

The terminal audit additionally requires complete, nonempty coverage and checks
source dependency closure. A passing audit never replaces mathematical review
of the correspondence between the manuscript and Lean statements.
Do not retain unused developments or obsolete theorem versions. Preserve
unrelated user work and any vendored licenses/provenance. Do not commit build
caches, download metadata, or LaTeX auxiliary files.
