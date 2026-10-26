# Computational supplement — Power rigidity and inflation for constant-excess skew diagrams

Cross-check scripts for `shields-2026-skew-power-rigidity.tex`.  All computations use exact integer or symbolic arithmetic.  Sparse determinant expansion and the independent Hessenberg interval expansion are compared directly.

The paper classifies full connected inflation classes for constant-excess inners with unequal endpoint gaps, symmetric gap words, or the stated balanced-prefix condition.  It also proves balanced-wall inversion and a complementary fixed-inner cut decoder for unequal terminal beta gaps.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Use Python 3.10 or later:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r requirements.txt
bash run_all.sh
```

Assertions stop the suite on a failure.  Successful completion ends with `ALL PASS`.

## Scripts by section

| Paper section | Script | Checks |
|---|---|---|
| Profiles and the main theorem | `check_plan_egp_family_balanced.py` | Terminal gaps, second-subdiagonal indices, power row counts and excess vectors |
| Polynomial inputs | `check_hessenberg_membership.py` | Maximal-cofactor identity, its first-subdiagonal indices, and monomial membership against both the row inequalities and the full-board Hessenberg test, with three firing controls |
| Polynomial inputs | `verify_inflation.py` | Exact lowering and pre-wall coarsening, including internal activations before the terminal wall |
| Power rigidity and literal class exposure | `verify_power_rigidity.py` | All safe high derivatives on a finite profile box, cap differences, balanced-prefix separators, and arbitrary-profile mate searches |
| Power rigidity and literal class exposure | `verify_class_exposure.py` | Cut/contract coefficients, literal split positions, mixed component orientations, and faithful ribbon substitution |
| The balanced wall | `verify_balanced_wall.py` | Independent-alphabet word recovery, invertible shell stripping, complete beta deletion and signs, core-word identification, and first-correction separators |
| Unequal terminal beta gaps | `verify_inflation.py` | Complete wall contacts and private-residue recovery of outer cuts |
| A limitation on arbitrary-mate separation | `check_r_wall_arbitrary_mate_refutation.py` | Four-row beta formulas, negative counts, zero-freeness, nonrotation, and separation times |

`profile_tools.py` supplies sparse polynomial arithmetic and profile operations.  Each verification script states its finite parameter ranges in its loops and prints the number of checked cases.

## Coverage by section

| Section | Computational scope |
|---|---|
| Profiles | Bounded positive gap words and parameters; repeated powers |
| Polynomial inputs | Full determinant comparisons, including a non-Hessenberg zero-free inner; Hessenberg membership on every connected profile through five rows |
| Powers | Exact derivative identities checked independently of interval expansion; candidate searches preserve only the recovered row/gap multisets, not the excess vector |
| Class exposure | All component orientations in the stated test boxes; equal endpoint lengths and coincident merger/internal row labels included |
| Balanced wall | Full independent-alphabet polynomials, symbolic shell identities, and full parent determinants through the first correction |
| Unequal terminal gaps | Bounded fixed-inner families, with all common betas deleted |
| Limitation | Direct permutation determinants for the displayed four-row family |

These are finite cross-checks, not proofs of the unbounded theorems.  The excluded secondary balanced-prefix example is checked as a genuine rotated-cap equality, not as a counterexample to power rigidity.  No general classification outside the paper's domain is tested or claimed.

## Dependencies

Refer to `requirements.txt`.

## License

The code is licensed under the MIT License; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

Refer to the paper for references.
