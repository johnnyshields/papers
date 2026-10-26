# Computational supplement — Primitive period comparison and smaller skew Schur probes

Cross-check scripts for `shields-2026-skew-period-comparison.tex` compare original Jacobi–Trudi determinants with ribbon coarsenings, endpoint correlations, and formal residue formulas.  All computations use exact integer, rational, or symbolic arithmetic.

The paper proves direct primitive period exclusion and constructs actual smaller equal ribbon-outer probes on its stated comparison domains.  Lower rooted transport gives conditional period consequences; arbitrary chart restoration and complete marked-key recognition are not supplied by these checks.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Use Python 3.10 or later.  Install `requirements.txt`, then run `bash run_all.sh`.

## Scripts by section

| Where | Script | Paper section | Content |
|---|---|---|---|
| §3 | `check_primitive_profiles.py` | `sec:lcm` | Positive-block profile derivatives and zero-join contraction identities |
| §4 | `check_window_recognition.py` | `sec:recovered-entry` | Actual singleton-seam high derivatives, including signed phases |
| §5 | `check_window_recognition.py` | `sec:recovered-recognition` | Complete small cut-set cases, optional seams, midpoint and half-phase cases |
| §6 | `check_residue_arithmetic.py` | `sec:older-cells` | Residue-ratio prime-divisor step, row-collapse specialization, pivot congruence mod \(b\), heterogeneous-reduction scalars |
| §7 | `check_residue_arithmetic.py` | `sec:positive-oo` | Matched top indices, common span and area bound of the smaller ordinary probes |
| §7 | `check_hook_transfer.py` | `sec:positive-oo` | Literal ordinary-gauge placement identity |
| §8 | `check_hook_transfer.py` | `sec:parent` | Hook support exponents, direct hook determinants, and the first two image layers |

Each script prints `PASS` lines and ends with the sweep; a failed identity raises `AssertionError` and exits nonzero.

## Coverage by section

**Work in progress.**  These marks describe computational coverage, not the validity of the proved implications or discharge of their hypotheses.

| Result group | Coverage | Scope |
|---|---|---|
| Primitive comparison | ⚠️ Partial | Local determinant identities, not a census of source-minimal charts |
| Window recognition | ⚠️ Partial | Bounded exact cut-set and raw-matrix sweeps |
| Positive ordinary probes | ⚠️ Partial | Window and gauge identities; not the entire legal-chart construction |
| Image layers and hook transfer | ⚠️ Partial | Exact finite partition and support tests |
| Residue exclusions (§6) | ⚠️ Partial | Elementary arithmetic and specialization algebra only; residue fields, gradings (`lem:triangular-residue`, `lem:graded-degree`, `lem:grading-shape`) and primitive triangularity are not computational |
| Rooted transport and conditional comparison (§9) | — | Logical equivalences and implications from stated hypotheses; nothing to compute, and the consuming probes above are the computational content |
| Hall-tail geometry and current-area restoration (Appendix A) | ❌ Missing | Not computationally verified here |

## Dependencies

Refer to `requirements.txt`.

## License

MIT; refer to `LICENSE.txt`.

This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

Refer to the paper for references.
