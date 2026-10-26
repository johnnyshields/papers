# Computational supplement — Short coarsenings determine ribbon Schur equivalence

Cross-check scripts for *Short coarsenings determine ribbon Schur equivalence*.  Every
script rebuilds the objects of the paper from their definitions — the coarsening inventory
\(G_\beta\) of a composition by choosing which cuts to retain, the labeled counts \(K_b\) by
summing over label permutations, the ribbon Schur function by a Jacobi–Trudi determinant,
the substitution maps \(\Psi_\epsilon\) by substituting generators — so each identity is
pinned to the object that defines it and none is read off a formula the paper proves
about it.  All arithmetic is exact (integers, `fractions`, and SymPy for determinants);
there is no floating point anywhere.

Statements about all compositions are swept exhaustively up to a stated weight, and the
weight is printed with each result.  Statements about the deep period chains of
`sec:detector` are checked on pairs drawn from their free parametrization, with the
defining equations of the normalized setting re-checked on every drawn pair, and on every
real pair of compositions of weight up to 18 with equal three-block data.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Reference environment: Python 3.12, SymPy 1.14.0, mpmath 1.3.0.

```bash
python -m pip install -r requirements.txt
./run_all.sh
```

## Scripts by section

Each script prints one `PASS` line per result group, with the sweep it covered, and ends
`ALL PASS`; a broken identity raises `AssertionError` and exits nonzero.

| Where | Script | Paper section | Content |
| --- | --- | --- | --- |
| §1, §2, §2 Lem 2.1 … §2 Rmk 2.6 | `verify_algebra.py` | `sec:introduction`, `sec:algebra` | The worked inventory and multiplicity; \(K_b=\kappa\,m\) and the small-discrepancy consequences; the ribbon expansion against a Jacobi–Trudi determinant; the cut formula for \(\circ\); literal factors; the seam, substitution, composition and split identities; factor reversal preserves \(G\); the nonlinear relation of weight six |
| §3, §3 Lem 3.1 … §3 Prop 3.7 | `verify_balance.py` | `sec:balance` | The triangle identity and low-order balance on all pairs of compositions; exhaustive checks of the clan, deletion and color lemmas on skew-ternary matrices; the support-separation theorem over every nonzero disjoint odd ternary pair on \(\Z/n\) for \(n\le18\); the normalization on every unequal, unreversed pair of weight up to 14 |
| §4 Lem 4.1 … §4 Lem 4.6 | `verify_detector.py` | `sec:detector` | The fiber lemma exhaustively; the four-block identity and its periodicity clause; antichain cancellation; the nested marked identity for chains of one to three strict increases; bottom probes and probe selection |
| §5 Lem 5.1 … §5 Prop 5.5 | `verify_realization.py` | `sec:realization` | Reflected packing to weight \(n\) with the product preserved; the worked example; propagation; termination and the local alternative on every real pair through weight 18 |
| §6, §1 Thm 1.1, §1 Thm 1.2 | `verify_recognition.py` | `sec:recognition` | Coarse recognition on every pair of classes through weight 13; the factor-reversal classification and the near-power congruence; the class corollary; the modular budget; the cut-array recognition algorithm; certificate counts |
| §7, §1 Thm 1.3 | `verify_depth.py` | `sec:depth` | The arithmetic optimization against an exhaustive longest-list search; the cutoff \(B\) and its bounds; exact \(D_=(n)\) and \(C(N)\) from their definitions through weight 19; both lifted families through weight 180 |
| §8 | `verify_recovery.py` | `sec:recovery` | Integral coordinates; first-degree and content preservation; the recovery operators; the subset recurrence; the weight-seventeen parity pair; odd characteristic |
| §A | `verify_multilevel.py` | `app:multilevel` | The weight-72 detector with two strict mask increases, rebuilt from its two cut sets |

## Coverage by section

| Where | Paper item | Check |
| --- | --- | --- |
| §1 Thm 1.1 | `thm:main-recognition`, `eq:main-modular` | `verify_recognition.py` (certificates and modular classes), `verify_depth.py` (the bound \(B\)) |
| §1 Thm 1.2 | `thm:main-structure`, `eq:REV` | `verify_recognition.py` (classification, near-powers, congruence), `verify_algebra.py` (\(\Psi\) laws) |
| §1 Thm 1.3 | `thm:main-depth`, `eq:frontier` | `verify_depth.py` |
| §1 | `eq:old-inclusion` | `verify_recognition.py` (class corollary: the inclusion is consumed there and holds in every case computed) |
| §3 Thm 3.5 | `thm:support` | `verify_balance.py` |
| §7 Prop 7.5 | `prop:logarithmic-cutoff` | `verify_depth.py` (to weight 20000) |
| §7 Thm 7.6 | `thm:lift` | `verify_depth.py` (the lifts of both seeds, two steps each) |
| §9 | `q:fixed-weight`, `q:full-parity` | posed problems; no check is owed |

## Dependencies

Refer to `requirements.txt`.

| Component | Used by | Description |
| --- | --- | --- |
| `_detector_common.py` | `verify_detector.py`, `verify_realization.py`, `verify_depth.py`, `verify_multilevel.py` | The normalized pair of cut indicators of `prop:normalization`, drawn from its free parametrization with the defining equations re-checked on each draw; the probe search of `lem:selection`; the normalized setting of a real pair of compositions.  Shared so the four scripts that argue about masks build the setting once. |
| `_ribbon_common.py` | every `verify_*.py` | Compositions, cut sets, \(\circ\) and \(\odot\); the inventory by enumeration of retained cuts and, independently, by a dynamic program over closed and open blocks; the subset recurrence and the labeled count of `eq:K`; the ring \(\Z[h_1,h_2,\dots]\) as dictionaries of integer coefficients; literal factorization. |
| `run_all.sh` | run directly | Runs the eight scripts in order and ends `ALL PASS`. |

## License

Code is made available under the MIT license (see `LICENSE.txt`), or as
otherwise noted in the comments of the file.

This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. L. J. Billera, H. Thomas, and S. van Willigenburg, *Decomposable compositions, symmetric quasisymmetric functions and equality of ribbon Schur functions*, Adv. Math. **204** (2006), 204–240. [doi:10.1016/j.aim.2005.05.014](https://doi.org/10.1016/j.aim.2005.05.014)

Refer to the paper for references.
