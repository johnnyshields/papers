# Computational supplement — Class recovery and inflation for repeated-block skew diagrams

Cross-check scripts for `shields-2026-skew-class-inflation.tex`.  The checks use exact integer arithmetic and collected Jacobi–Trudi determinants.  Complete-class searches enumerate every ordering of the necessary row and gap multisets; numerical integer evaluations only reject candidates, and symbolic comparison decides equality.

The paper proves complete connected-class recovery for separated repeated blocks without assuming inner rigidity, and an exact additive-inflation threshold for asymmetric two-row inners.  The checks cover specified finite instances, including a nonrigid five-row inner, and do not prove the uniform theorems.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Python 3.10 or later is required.  The scripts use only the standard library.  Run the suite from this directory with:

```sh
bash run_all.sh
```

Successful completion ends with `ALL PASS`.

## Scripts by section

| Where | Paper section | Script | Assertions |
|---|---|---|---|
| §2, §3, §5 … §8 | Profiles, cuts, and ribbon substitution; Profile transport; The repeated-block inverse; The thin two-row class; The exact inflation threshold; Examples and verification scope | `check_ref1_class_inflation_exact.py` | Generic subset determinant agrees with direct permutation expansion and fraction-free integer elimination on small controls.  Complete classes for asymmetric, symmetric, zero-gap, repeated-row, and nonrigid-inner examples; incorrect one-copy replacements fail.  Exact lowering recovers the uninflated determinant, including unit and newly opened entries.  Boundary beta lists, common-beta deletion sign, lowest homogeneous component, suffix recovery, and threshold-one/two complete classes.  Displayed separating coefficient; eight constructed images separate into four rotation pairs, without an independent fourteen-row exhaustion claim. |
| §2, §4 Lem 4.1, §5 Prop 5.3, §6, §7 Lem 7.1 … 7.3, §8 Cor 8.1 | Profiles, cuts, and ribbon substitution; Rigidity of overlapped powers; The repeated-block inverse; The thin two-row class; The exact inflation threshold; Examples and verification scope (`lem:triangular-substitution`, `lem:overlap-power-rigidity`, `lem:merged-block-rigidity`, `prop:saturation-chart`, `lem:subthreshold-transport`, `lem:boundary-core`, `lem:private-residue-column`, `cor:unbounded-class-splitting`) | `check_expansions_substitutions_and_rigidity.py` | The interval expansion, cut–merge identity, ribbon formula and constant-gap substitution as polynomial identities, each with a control that fails outside its hypotheses; the readings, private corners and substitution identities of the repeated-block and thin families; no factorization of any overlapped power in range, with its ribbon class, and the \(m\ge2\) hypothesis shown necessary; the explicit marked charts built from the printed cells and checked against Hypotheses I–V, with the failure at the threshold; the opening parameter and the boundary-core structure; the private-residue lemma over residue sets with its condition shown necessary; the printed boundary examples and the class sizes \(2^{e+1}\) splitting into \(2^e\) rotation pairs. |
| §2 Lem 2.1 | Profiles, cuts, and ribbon substitution (`lem:hessenberg-membership`) | `check_hessenberg_membership.py` | The signed maximal-label coefficient read off the full determinant equals the separately expanded cofactor; it is a monomial exactly when the board is upper Hessenberg and exactly when the row inequalities hold, and it is then the product of the gap generators.  Controls with a non-strict inequality, a wrong gap index, and a dropped sign each disagree on part of the sweep. |
| §2 Lem 2.2, §5 Lem 5.1 | Profiles, cuts, and ribbon substitution; The repeated-block inverse (`lem:seam-coefficients`, `lem:ribbon-endpoints`) | `check_seam_coefficient_order.py` | Distinguished-gap coefficient identities, including uncut larger gaps; positional reconstruction with empty interiors, zero inner gaps, minimal endpoints, symmetric inners, and merger-row collisions. |
| §3, §7 | Profile transport; The exact inflation threshold (`lem:erosion`, `lem:inflation-lowering`, `cor:inflation-no-escape`, `lem:zero-free-bijection`) | `check_cut_coefficient_lowering.py` | Cut coefficients over all cut subsets and filtered lowering with exact integer polynomials.  Actual cell-component erosion, vanished rows, exact area drop, positive-overlap counts of index \(-1\), no-\(-1\) raising and exact zero-free class bijections in the stated box; controls reject minimum-degree erosion, omitted filters, unconditional raising, general inverse inflation and reverse no-escape. |
| §3 Lem 3.5 | Profile transport (`lem:inflate-chart`) | `check_chart_inflation.py` | Independently asserted I–IV, proper nonrow input and zero-free inflated parent; exact cell equality in all three branches and all four attachment cases, including nonhorizontal marks, phase changes, mixed supplements, the horizontal EMPTY gauge and the maximal-width atom.  IV uses content-derived bounds for all integer translates. |
| §3, §5 | Profile transport; The repeated-block inverse (`lem:inflation-lowering`, `cor:inflation-no-escape`, `lem:total-contraction-inverse`) | `check_two_residue_decoder.py` | Two-residue decoder and its two readings on selected fixtures against literal-cell permutation expansion; controls reject a weakened bottom reading, ignored endpoint orientation, a changed decoder specialization, and the reverse no-escape inference. |
| §1 Thm 1.1, §5 | The repeated-block inverse (`thm:repeated-block-saturation`) | `check_repeated_block_saturation.py` | Complete classes of repeated-block diagrams against arbitrary connected mates, including the halving at a symmetric inner; the boundaries \(M=1\) and \(d=c\) fail as they must. |
| §1 Thm 1.2, §7 | The exact inflation threshold (`thm:sharp-inflation`) | `check_inflation_collapse_threshold.py` | Class size \(2\lvert R(\alpha)\rvert\) below the threshold and \(2\) from it on, compared at the set level, with a control that fires across the threshold. |
| §1 Thm 1.2, §7 | The exact inflation threshold (`thm:sharp-inflation`) | `check_inflation_all_t.py` | The theorem for every inflation parameter at twelve parameter choices: inflation shifts every Jacobi–Trudi label by the parameter and commutes with the candidate orderings, so once every candidate label is positive equality is unchanged under further inflation; the complete class is asserted at the set level up to that point. |
| §2 Lem 2.2 eq. (2.10), §4 Lem 4.1, §6 Thm 6.2 | Profiles, cuts, and ribbon substitution; Rigidity of overlapped powers; The thin two-row class (`lem:seam-coefficients`, `lem:overlap-power-rigidity`, `thm:two-row-thin-class`) | `check_proof_step_equations.py` | The zero-gap extremes of the homogenized function against full determinants; the cut set of an overlapped power, its vanishing initial interval, the period and gcd relations and the residue-class graph of the factorization argument; the orientation multiset of the thin class, where only the two uniform orientations keep the row multiset. |
| §2 Sec 2.4 | Profiles, cuts, and ribbon substitution (`subsec:marked-geometry`) | `check_marked_boundary_words.py` | The consumed boundary-word facts of a marked composition on actual cell unions in all four attachment cases: binary steps and heights, the beta membership words, the periodic slot table, the initial and terminal values, the phases, and the span. |

Each script prints `PASS` lines, ends `ALL PASS`, and exits nonzero on failure.

## Coverage by section

These statuses describe computational coverage, not the validity of the paper's proofs.  **✅ Full** means all explicitly specified instances of a finite check, not all parameters of a theorem.

| Subject | Status | Scope |
|---|---|---|
| Hessenberg membership | ✅ Full | Every connected profile with at most five rows, within the script's row-length bounds. |
| Determinant-engine controls | ✅ Full | All compositions of size at most five and the displayed five-row inflation example. |
| Repeated-block complete classes | ⚠️ Partial | Explicit parameter cases in the script; the nonrigid-inner parent is exhausted over all row/gap orders. |
| Overlap-power rigidity | ✅ Full | No factorization of any overlapped power in range, exhaustively over composition factorizations, with its ribbon class; the cut set, vanishing initial interval, gcd relation and residue-class graph of the period argument for every composition in the box. |
| Proof-step equations and marked boundary words | ✅ Full | The zero-gap extremes, the orientation multiset of the thin class, and the boundary-word tables of a marked composition, over the stated boxes. |
| Expansions and substitutions | ✅ Full | Interval expansion, cut–merge, ribbon formula and constant-gap substitution as identities on every profile in range, with failing controls outside the hypotheses. |
| Marked charts and boundary core | ✅ Full | The printed charts against Hypotheses I–V, the failure at the threshold, and the boundary-core and private-residue statements. |
| Erosion and zero-free class transport | ⚠️ Partial | All connected profiles with 1–4 rows, lengths 1–4 and area at most 9; every legal adjacent overlap.  Actual component determinants, finite class equality and off-domain controls are exact; no uniform theorem is inferred. |
| Marked-chart inflation | ⚠️ Partial | Inners with 1–3 rows, lengths 1–5 and area at most 10, all legal marks found by full end intersections, and every connected nonrow outer of area 2–4 whose inflated parent is zero-free.  Explicit witnesses pin all three alternatives, four attachment cases and nonhorizontal marks.  The bundled cell engine is reused; the new IV check covers every integer translate by exact content bounds. |
| Lowering and boundary-core formulas | ⚠️ Partial | All compositions of total size at most five for the script's four parameter triples. |
| Unbounded class splitting | ⚠️ Partial | The eight constructed members at outer size nine; no independent exhaustive classification there. |

## Dependencies

| Component | Used by | Description |
|---|---|---|
| `_composition_engine.py` | `check_inflation_collapse_threshold.py`, `check_repeated_block_saturation.py`, `check_cut_coefficient_lowering.py`, `check_chart_inflation.py`, `check_expansions_substitutions_and_rigidity.py` | Skew-diagram engine: composition \(\circ_W\), the exact free-\(h\) Jacobi–Trudi determinant, and cell/profile utilities.  Its standalone validation and census entry point is not invoked by `run_all.sh`; the chart-inflation check supplies its own all-integer IV predicate rather than using the engine's fixed-window IV test. |
| `check_paper_crossrefs.py` | `run_all.sh` | Label index and the scanner for number citations over every script and this file; run directly |
| `requirements.txt` | none | Pins the repository's optional symbolic-computation environment; the scripts need no third-party package. |

## License

MIT; refer to `LICENSE.txt`.

This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. J. Shields, *Class recovery and inflation for repeated-block skew diagrams*, preprint, 2026.

Refer to the paper for references.
