# Computational supplement — Polynomial recognition and inflation of Hessenberg skew Schur classes

Cross-check scripts for `shields-2026-skew-hessenberg-recognition.tex`.  Complete determinant polynomials are compared with interval and permutation expansions using exact integer arithmetic.  Finite-field evaluations reject unequal candidates only; retained equality claims use complete integer polynomials.

The paper proves positional exposure for connected zero-free inners, a sharp four-member bound for three zero-free blocks with a rigid total merger, and legal generation for commuting blocks without individual block rigidity.  Constant-gap power recognition is complete through five rows, and balanced Hessenberg wall orientation through four rows.  These results give complete inflation classes and legal generation for constant-gap inners through four rows, together with unbounded-height and non-Hessenberg domains.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Use Python 3.10 or later.  From this directory:

```bash
python3 -m pip install -r requirements.txt
./run_all.sh
```

The suite exits on the first failure and ends with `ALL PASS`.  `PYTHON` may select another Python executable.  The largest row-order and constant-gap sweeps take longer than the coefficient probes.

## Scripts by section

| Paper section | Script | Check |
|---|---|---|
| Profiles and polynomial data; the balanced cut-set inverse | `verify_hessenberg.py` | Independent interval and determinant expansions, complete contact lists, deletion signs, two-arm decoding, direct cofactor ratios |
| Positional exposure | `verify_exposure.py` | Ordered split positions, rotated components, equal endpoints with palindromic gaps |
| Positional exposure | `check_zero_cut_inventory.py` | Full block expansion, invariant internal-unit count, extreme-component readings, and the 19-cell inventory obstruction |
| The zero-free hypothesis in the block-function conclusion | `check_parity_pair_equality.py` | The obstruction remark's witness pair: equal Jacobi--Trudi determinants, equal area, not rotations, with three perturbation controls |
| The zero-free hypothesis in the block-function conclusion | `check_parity_pair_determinant.py` | The same witness equality by symbolic Jacobi--Trudi determinants, sharing no code or algorithm with the permutation sum |
| Positional exposure; recognition of rigid powers; inflation and legal generation | `check_zero_free_exposure.py` | Complete invariant fibers for Hessenberg and non-Hessenberg inners, pre-threshold and post-threshold classes, literal charts, and mixed-zero recoding |
| Positional exposure | `check_separated_support.py` | Reconstruction with disjoint gap supports, a nonrigid-block probe, complete rigidity fibers, and controls for shared supports and one-row blocks |
| Positional exposure | `check_three_block_classes.py` | Area cuts, retained-end cancellation, the three rigidity tests, maximal-cofactor products, and all three span cases in the sharp class bound |
| Positional exposure | `check_three_block_generation.py` | Common primitive extraction, literal empty-overlap charts, and selected rigid total powers with a nonrigid inner |
| Recognition of rigid powers; inflation and legal generation | `verify_recognition.py` | Disjunctive pattern recognition, exact power classes, dense private-endpoint example, profile recoding |
| Oriented boundary coefficients; selected coefficients and reductions | `verify_wall_criteria.py` | Wrapped matching and ratios, core/mixed/parent deletions, selected parent coefficients, vanishing-matching control |
| Selected coefficients and reductions | `check_four_row_wall.py` | Exhaustive six-parameter branch checks, selected one-return coefficients, and symmetry and multiplicity controls |
| Selected coefficients and reductions | `check_four_row_return.py` | Independent extraction of entire one-return coefficient polynomials, including double and coincident-label resonances |
| Selected coefficients and reductions; inflation and legal generation | `check_four_row_wall_cells.py` | Independent literal-cell wall and post-wall inequalities; exact pre-wall equality rejects dropping the threshold |
| Recognition of rigid powers | `check_multiplicity_recognition.py` | Multiplicity-only powers, the arbitrary-height family's hypotheses, and a larger-class control |
| Recognition of rigid powers; selected coefficients and reductions | `check_five_row_classification.py` | The balanced/unequal-end split, balanced power orders, and exact core-deletion identities |
| Recognition of rigid powers | `check_constant_gap_boundary.py` | Complete bounded profile enumeration with both endpoint and internal legality; criterion escapes |
| Recognition of rigid powers | `check_five_row_powers.py` | Exact first and second powers of the balanced exceptional form and a recognized control |
| Recognition of rigid powers | `check_five_row_split.py` | Independent escape enumeration and exact extra mates in every unequal-end escape |
| Recognition of rigid powers | `check_pattern_controls.py` | Ribbon classes larger than reversal orbits and the classical four-member example [1] |
| Introduction; the balanced cut-set inverse | `check_nearest_prior.py` | Translation of unmatched content sets [2] and the distinction between shape and polynomial data |
| Concluding remarks | `check_orientation_reduction.py` | The explicit symmetric-core obstruction to full-core residue exclusion, without asserting a wall counterexample |
| Recognition of rigid powers; inflation and legal generation | `check_widening_controls.py` | Firing controls for private-row cofactor splitting, inflation separation, and the recoding restrictions |
| Inflation and legal generation | `check_literal_charts.py` | Literal end-row and empty-edge placements, sufficient I–V certificates, exact infinite-chain membership, and threshold and displacement controls |
| Inflation and legal generation | `check_reversal_towers.py` | Fixed left-associated ribbon-prefix towers, full determinant and coarsening comparisons, marked rotations, and controls for the threshold and all-power hypothesis |

The `verify_*` scripts carry the primary sweeps; `check_*` scripts test individual mechanisms or hypothesis boundaries.  All mathematical inputs are contained in this directory.  No reference-library files or external data are required.

## Coverage by section

Coverage below concerns the computational supplement, not validity of the paper's proofs.  The marks are ✅ Full, ⚠️ Partial, ❌ Missing, and —.  Finite tests do not verify universal all-power or all-outer quantifiers.

| Section | Status | Coverage and limit |
|---|---|---|
| Introduction | — | Context and theorem summaries; the nearest-prior comparison has a concrete algebraic check |
| Profiles and polynomial data | ⚠️ Partial | Exact determinant/interval identities on the displayed test profiles; cited general reconstruction and irreducibility are not proved by the scripts |
| Positional exposure | ⚠️ Partial | Zero-cut inventory, area-cut recovery, the sharp three-block bound, rigidity tests, and commuting-block charts with nonrigid constituents; no enumeration of all mates at all powers |
| Recognition of rigid powers | ⚠️ Partial | Complete equality decisions in the declared finite windows, with genuine extra-mate controls; the uniform recognition theorems are proved in the paper |
| The balanced cut-set inverse | ⚠️ Partial | Complete beta lists and signed lowest components on finite families; the unbounded decoder is proved in the paper |
| Oriented boundary coefficients | ⚠️ Partial | Exact matching, ratio, deletion and coefficient instances; exhaustion beyond four-row balanced inners remains open |
| Selected coefficients and reductions | ⚠️ Partial | Core/mixed/parent identities, the exhaustive four-row parameter split, full one-return coefficient polynomials, and resonance controls; the unbounded proof is in the paper |
| Inflation and legal generation | ⚠️ Partial | Literal charts and retained-context towers, full-polynomial transport, non-Hessenberg unequal-terminal class fibers, and threshold and recoding controls; the general quantifiers are proved in the paper |
| Concluding remarks | ⚠️ Partial | Exact balanced-obstruction data and the full zero-cut sum expansion; higher-row orientation and general three-block legal generation remain open |

The declared windows and their resulting counts are printed by the scripts.  Full-polynomial equality is never inferred from agreement at evaluation points.  The common-unit deletion signs are retained, as in the bottom-component setting [3].  The literal charts use the horizontal composition and empty-overlap conventions of [4].

## Dependencies

Refer to `requirements.txt`.  The scripts use the Python standard library and SymPy for independent symbolic checks.

## License

MIT; see `LICENSE.txt`.

This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. L. J. Billera, H. Thomas and S. van Willigenburg, *Decomposable compositions, symmetric quasisymmetric functions and equality of ribbon Schur functions*, Advances in Mathematics 204 (2006), 204–240.  https://doi.org/10.1016/j.aim.2005.05.014
2. W. Y. C. Chen and A. L. B. Yang, *Stanley's zrank conjecture on skew partitions*, Transactions of the American Mathematical Society 360 (2008), 3121–3131.  https://doi.org/10.1090/S0002-9947-08-04342-0
3. P. Clifford and R. P. Stanley, *Bottom Schur functions*, Electronic Journal of Combinatorics 11 (2004), Research Paper 67.  https://doi.org/10.37236/1820
4. P. R. W. McNamara and S. van Willigenburg, *Towards a combinatorial classification of skew Schur functions*, Transactions of the American Mathematical Society 361 (2009), 4437–4470.  https://doi.org/10.1090/S0002-9947-09-04683-2

Refer to the paper for references.
