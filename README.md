# Dynamical C*-algebras and coarse geometry

Lean verification of Bruno M. Braga's article
[*Dynamical C*-algebras and coarse geometry*](paper/main.tex).
The project uses **Lean 4.33.1 and Mathlib v4.33.1**, with exact dependency
revisions recorded in `lake-manifest.json`.

Theorems A–E, supporting results, cited mathematical dependencies needed by their
proofs, and the coarse-space generalizations are formalized. The reviewed inventory
contains 1,328 verified entries: 1,288 distinct declarations in 194 proof modules,
supporting 136 manuscript roots. The terminal audit checks every declaration's
axioms and its connection to those roots. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted; there are no project axioms or proof placeholders.

## Reproduce the verification

Clone or download this project, then open a terminal in the directory containing
`lakefile.toml`. On Linux, macOS, or Windows via WSL, install Git, curl, and
**Python 3.11 or newer**, then run:

```sh
sh scripts/setup.sh
python3 scripts/test_audit.py
sh scripts/audit.sh --terminal
```

The setup script installs elan if needed, installs the pinned Lean toolchain,
downloads the Mathlib compiled cache, and builds the project. Network access is
required for the initial downloads. Allow several gigabytes for Lean, Mathlib,
and build artifacts. Project proofs are compiled from the included Lean sources.
No sibling repository, private file, external Python package, or manuscript
compilation is needed. Do not run `lake update` to reproduce this version.

A successful final command ends with:

```text
Terminal mechanical audit passed. Source-to-statement review is also required.
```

The audit checks the manuscript SHA256, reviewed dependency pins, complete
coverage, proof placeholders, declaration axioms, and source dependency closure.
The separate [source correspondence review](docs/SOURCE_COVERAGE_REVIEW.md)
explains how the Lean statements match the article. Kernel checking certifies
the formal statements; it does not itself establish that they express the
intended mathematics. See [verification scope](docs/VERIFICATION_SCOPE.md) for
the conventions and coverage details.

For subsequent checks, run `sh scripts/audit.sh --terminal` again. For development,
`lake build` builds the library and `sh scripts/audit.sh` runs the ordinary audit.
GitHub Actions runs setup, the audit regression tests, and the terminal audit on
pushes and pull requests when this directory is published as the repository root.

## Find the main results

All declarations below belong to the namespace `DynamicalCStarAlgebras`.

| Article | Lean declaration | Source |
| --- | --- | --- |
| Theorem A | `theoremA` | [TheoremA.lean](lean/DynamicalCStarAlgebras/TheoremA.lean) |
| Theorem B (no growth hypothesis) | `theoremB` | [TheoremB.lean](lean/DynamicalCStarAlgebras/TheoremB.lean) |
| Theorem C | `theoremC` | [ExpanderTheorems.lean](lean/DynamicalCStarAlgebras/ExpanderTheorems.lean) |
| Theorem D | `theoremD` | [ExpanderTheorems.lean](lean/DynamicalCStarAlgebras/ExpanderTheorems.lean) |
| Theorem E | `theoremE` | [StripCharacterization.lean](lean/DynamicalCStarAlgebras/StripCharacterization.lean) |

The cited degree-three graph embedding is proved in
[BoundedDegreeEmbedding.lean](lean/DynamicalCStarAlgebras/BoundedDegreeEmbedding.lean).
Its supporting construction is in `CoarseMatchingCover.lean` and
`MatchingRayGraph.lean`. The same-set metric reduction and the revised Theorem B
use no external mathematical assumptions. The new AP = AP_exp corollary is in
`TheoremB.lean`.

For manual review, [MAIN_THEOREM_DEFINITIONS.txt](docs/MAIN_THEOREM_DEFINITIONS.txt)
collects the definitions used to read Theorems A–E and their growth reduction.

Import the whole library with `import DynamicalCStarAlgebras`. The entry point
imports the terminal proof modules; their imports expose the remaining modules.
The proof files stay in a single namespace directory so that module names and
source links remain stable. The [coverage inventory](lean/coverage.json) maps
manuscript results and proof dependencies to qualified declarations. Its
`paper_roots` field lists the final manuscript declarations used by the audit.

## Repository contents

| Path | Purpose |
| --- | --- |
| `paper/main.tex` | Authoritative manuscript, including its bibliography |
| `lean/DynamicalCStarAlgebras/` | Proof sources and definitions |
| `lean/DynamicalCStarAlgebras.lean` | Public library entry point |
| `lean/coverage.json` | Coverage inventory and manuscript fingerprint |
| `lean/FORMALIZATION_LOG.md` | Concise verification and maintenance record |
| `docs/` | Mathematical correspondence and verification scope |
| `scripts/` | Setup, audit implementation, and regression tests |
| `.github/workflows/verify.yml` | Automated reproduction on GitHub |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Toolchain and dependency pins |
| `AGENTS.md` | Maintenance rules for automated contributors |

Build products, downloaded dependencies, and the generated axiom report live
under the ignored `.lake/` directory. Python caches, editor metadata, and LaTeX
auxiliary files are also excluded from version control.

## Publication and maintenance

Publish **this directory's contents** as the root of the GitHub repository.
The current development checkout may be nested in a larger repository; do not
publish that parent's unrelated projects or history by accident. Include the
lockfile, all Lean sources, the manuscript, the coverage records, and the hidden
`.github/`, `.gitignore`, and `.gitattributes` files. Exclude `.lake/` and other
ignored artifacts. The line-ending attributes preserve the manuscript fingerprint
across platforms.
Public repository: https://github.com/demendoncabraga/dynamical-cstar-algebras.
Hosted workflow results are available in its Actions tab; local validation is
recorded separately in `lean/FORMALIZATION_LOG.md`.

After an authorized manuscript change, review its mathematical correspondence
before updating `source_sha256`. Keep `paper_roots` synchronized with
`scripts/DependencyAudit.lean`, and run both the tests and terminal audit.
Changing the reviewed Lean/Mathlib pins also requires updating the pin checks in
`scripts/audit.py` and reviewing the verification record.

Licensing is undecided by the author; no project license has been assigned.
The manuscript's publication rights are unchanged. Four expander-construction
modules retain their source provenance comments crediting the same author's
`propertyH_lean` formalization; their proofs are included here in full and do not
import that project. Downloaded dependencies retain their own licenses.
