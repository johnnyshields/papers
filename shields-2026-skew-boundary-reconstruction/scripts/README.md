# Computational supplement — Boundary reconstruction and cofactor rigidity for skew Schur functions

Cross-check scripts for `shields-2026-skew-boundary-reconstruction.tex`.  Every script rebuilds its
objects from the paper's definitions (the cap grid, the capped cofactor matrix, the cofactors as
Jacobi–Trudi minors) in exact integer arithmetic on signed \(h\)-monomials, so an equality reported
here is a polynomial identity and not a numerical coincidence.  No floating point enters a check.

The paper determines a connected skew diagram from two boundary observations, and proves an
adjacent-edge rigidity for the cofactor difference of two diagrams with equal skew Schur functions
and a common inner boundary.  The scripts check the finite arithmetic those arguments run on, probe
the hypotheses at their boundary, and confirm the numbers printed in the worked example and
figures.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Reference environment: Python 3.12, SymPy 1.14.0, mpmath 1.3.0.

```
pip install -r requirements.txt
./run_all.sh
```

`run_all.sh` ends with `ALL PASS`; a failed check raises `AssertionError` and exits nonzero.  The
figure generator additionally needs matplotlib to write the figures, and not to check them
(`make_figures.py --check-only`, which `run_all.sh` runs).

`FULL=1 ./run_all.sh` adds four slow checks, each taking minutes on one core (the cap-fixed adjacent-edge guard
and the cap-fixed tail check each exceed ten): they are marked **(FULL)** below.

## Scripts by section

| Where | Script | Paper section | Content |
|---|---|---|---|
| §1.1 Thm 1.1, Cor 1.2 | `check_witnesses_independent.py` | `subsec:intro-main`, `rem:one-extension-insufficient`, `ex:actual-equal-chain` | The front-matter witness pairs rebuilt from the definitions by symbolic determinants: equal skew Schur functions, the stated difference of the reversed partners, and the one-extension family |
| §1, §3 Thm 3.9, §4 Thm 4.1 | `check_row_count_is_determined_by_the_skew_function.py` | `thm:boundary-reconstruction`, `cor:two-positive-extensions`, `thm:monge-minor` | The row count \(n\) is determined by the observed skew Schur functions, so fixing it restricts the domain for nothing |
| §1, §4 Thm 4.2, Cor 1.2, §4 Rmk 4.5, §8 Def 8.2 | `check_reconstruction_census.py` | `lem:extension-cofactors`, `eq:Pk-is-capped`, `eq:iterated-cap`, `lem:cofactor-factorization`, `lem:top-row-cofactor`, `lem:two-cofactor-reconstruction`, `thm:boundary-reconstruction`, `cor:two-positive-extensions`, `rem:one-extension-insufficient`, `def:reversal` | The extension lemma and the ratio quantity as a skew Schur function; the cofactor factorization and its exact support criterion on every presentation; the prefix-residual induction run as an algorithm on the observed polynomials alone; injectivity of the three observation maps over all inner boundaries at once; the front-matter witnesses; reversal |
| §1 Thm 1.1, §5 Ex 5.14, §8 Cor 8.6 | `make_figures.py` | `thm:boundary-reconstruction`, `ex:actual-equal-chain`, `cor:boundary-separation`, `fig:boundary-observations`, `fig:cancellation-geometry` | Generates the two figures and asserts every number in them, and in the worked equal pair, against the paper's definitions |
| §1 Cor 1.2, §5 Lem 5.10, §6 Thm 6.1, §7 Cor 7.4, §9 | `check_printed_statement_guards.py` | `ex:actual-equal-chain`, `eq:largest-index`, `eq:cofactor-initial`, `eq:radix-weight`, `cor:unique-ratio`, `prop:caterpillar`, `cor:two-positive-extensions`, `subsec:floor-margin` | The worked equal pair with every printed number, the largest generator index, dominance-minimal versus weight-minimal monomials, the radix-weight increment, at most one ratio identity in the \((r,a)\) plane, the two-extension separation, the dilation family |
| §2 eq. (2.11), §6 Thm 6.2, §9 eq. (9.1) | `check_kernel_relation_and_radix_weight.py` | `eq:Adef`, `eq:dexplicit`, `rem:realizability-terminal` | The row-zero kernel relation \(P_0(C(X))=0\) on every connected parent, the terminal-gap witness \(G_0=1\), and the radix weight as an admissible weight |
| §2 Def 2.2, §9 eq. (9.1) | `check_radix_weight_is_admissible_and_injective.py` | `def:convex-weight`, `eq:radix-weight`, `subsec:weight-scope` | The radix weight is admissible, \(B=2\) is not, and the weight is injective on Jacobi–Trudi monomials where square weight collides |
| §3 | `check_geometry_census.py` | `lem:grid-order`, `lem:diagonal-feasible`, `lem:valuation-laws`, `lem:strict-monge`, `lem:feasible-uncrossing`, `thm:monge-minor`, `prop:cofactor-initial`, `lem:distinguished`, `prop:action-recurrence`, `prop:initial-energy` | Every result stated for an arbitrary admissible convex weight, asserted at four weights over all connected diagrams and a box of staircase minors: valuation laws, strict Monge, the unique initial monomial of every feasible minor and its coefficient, the initial face of every capped cofactor, the action recurrence and the initial energy |
| §3 Lem 3.4, §4 Prop 4.2 | `check_cofactor_factorization_and_reconstruction.py` | `lem:cofactor-factorization`, `prop:stable-cofactor`, `lem:grid-order`, `lem:diagonal-feasible` | Capped cofactors are signed skew Schur functions of \(\lambda/\nu^{(j)}\), are nonzero, and distinguish diagrams; exhaustive over all connected diagrams to the stated size and row bounds |
| §3 Lem 3.4 | `check_top_deletion_descent.py` | `lem:cofactor-factorization`, `eq:cofactor-schur` | The top-deletion descent \(C_0(A)=P_r(C(\bar A))\), \(C_{r+d}(A)=-C_d(\bar A)\) under an overlap-one top seam, with the overlap hypothesis shown load-bearing |
| §3 Lem 3.4, §4 Prop 4.2, §5 Thm 5.5 | `check_cofactor_scalar_reconstruction_support_and_backflow.py` | `lem:cofactor-factorization`, `prop:stable-cofactor`, `thm:no-backflow` | Scalar reconstruction from degree and square-weight pairs, the exact support criterion without connectedness, the one-extension family at every fixed length, the quantitative no-backflow margin |
| §3 Lem 3.8, Thm 3.9 | `check_monge_minor_sign_and_uncrossing_premise.py` | `lem:feasible-uncrossing`, `thm:monge-minor` | The first premise of the uncrossing lemma is unused, and the leading coefficient of a feasible minor is \(+1\) |
| §4 Prop 4.2 | `check_general_weight_recovery.py` | `prop:stable-cofactor`, `eq:scalar-recovery`, `def:convex-weight` | Every admissible weight determines the pair from degree and weight difference; the square weight supplies only the closed form |
| §5, §8 Cor 8.6 | `check_localization_census.py` | `eq:common-row-relation`, `prop:synchronization`, `cor:first-split-anchor`, `lem:tropical-balancing`, `lem:tail-increase`, `thm:no-backflow`, `lem:marching`, `thm:cap-fixed-rigidity`, `lem:equality-normalizes-cap`, `thm:equal-pair-rigidity`, `prop:monomial-prefix`, `cor:boundary-separation` | One census at four admissible weights over every cap-fixed pair with no multiset pre-filter, to first changed row 3: synchronization, the first split and its direction, the anchor, balancing, marching, tail increase, no-backflow, every clause of the cap-fixed conclusion, the necessity of the floor antecedent, and on every equal pair the single-monomial prefix, the exchange identity and both leading-monomial formulas of the separation corollary |
| §5 Thm 5.8, §6.4 (FULL) | `check_capfixed_tail_is_normalized.py` | `thm:cap-fixed-rigidity`, `subsec:locus-family` | The tail sentence compares normalized actions \(\alpha_j\), not raw valuations, on the \(k=2\) member of the ratio family |
| §5 Thm 5.8 (FULL) | `check_cap_fixed_adjacent_edge_guard.py` | `thm:cap-fixed-rigidity` | Every clause of the cap-fixed adjacent-edge conclusion on every pair meeting the hypotheses, to size 14 at the square weight |
| §5 Lem 5.7, Thm 5.8, §6 Thm 6.7 | `check_marching_saturation.py` | `lem:marching`, `thm:cap-fixed-rigidity`, `thm:ratio-rigidity` | The shared marching step, \(R_i=i+2\) and \(M_i=\{i+1,i+2\}\), from its four abstract inputs |
| §5 Thm 5.11, Ex 5.14 | `check_equal_pair_rigidity_unconditional.py` | `thm:equal-pair-rigidity`, `subsec:actual-equality` | Actual skew Schur equality supplies the cap-fixed antecedent with no ratio identity, with controls that must fire |
| §5 Prop 5.13, §6.4 | `check_equality_excludes_ratio_identities.py` | `prop:monomial-prefix`, `subsec:locus-family` | No ratio identity holds on a distinct equal pair, and the leading prefix is a chain of single monomials with alternating signs |
| §6 | `check_ratio_locus_census.py` | `lem:ratio-row-lengths`, `eq:bounded-generator`, `thm:terminal-gap`, `prop:top-terminal`, `cor:cap-fixing`, `thm:ratio-rigidity`, `eq:virtual-gap-general`, `eq:square-gap`, `lem:laplace-equivalence`, `thm:floor`, `thm:two-cap`, `cor:floor-supplies`, `cor:double-cap-kills`, `cor:unique-ratio` | The ratio locus enumerated as the collisions of the one-diagram quantity over all connected diagrams, with no filter on inner boundary, multisets or grid: equal multisets, the cap-fixing corollary, the terminal gap, the virtual row and full chain at four weights, the gap formulas, Cancellative Leftmost, the two-cap and uniqueness corollaries, and both hypotheses of two-cap exclusion shown necessary by formal vectors outside the class |
| §6 Lem 6.1, Thm 6.7 | `check_ratio_identity_forces_equal_row_multisets.py` | `lem:ratio-row-lengths`, `thm:ratio-rigidity`, `cor:floor-supplies`, `cor:double-cap-kills`, `cor:unique-ratio` | A ratio identity forces equal row-length multisets, tested on a population that does not presuppose it |
| §6 eq. (6.8), §9 Prop 9.1 | `check_elbow_cone_matches_the_square_gap.py` | `eq:square-gap`, `prop:elbow`, `thm:ratio-rigidity` | The elbow cone satisfies the paper's square-gap formula, so the formula cannot separate a genuine defect from a formal one |
| §6.4 | `check_locus_family_census.py` | `lem:two-series-reversal`, `prop:staircase-reversal`, `cor:locus-family`, `rem:staircase-boundary` | The staircase family over every word to length 9: the ratio identity at \((2,1)\), the pair counts, \(s_X\ne s_{X^*}\); then the corollary by direct determinants for \(k\le4\), its closed forms \(\alpha_0=13k+20\) and \(\operatorname{wt}G_2=13k-4\), the cofactor factorization, and the diagonal-weight separation to \(k=40\); and the boundary-letter remark for every nonpalindromic word with its weight bookkeeping |
| §6.4 | `check_abstract_reversal_identity.py` | `subsec:locus-family`, `lem:two-series-reversal` | The two-series reversal identity on generic coefficients, with a control that breaks under a non-reversal permutation |
| §6.4 Cor 6.12 | `check_ratio_locus_unbounded_support_family.py` | `subsec:locus-family`, `subsec:floor-margin` | The ratio locus is populated at \(k=1,2,3\) supported shifts by the cheap recurrences |
| §6.4 Cor 6.12 | `check_locus_family_all_k.py` | `cor:locus-family`, `eq:virtual-gap-general` | The corollary for every \(k\) at four admissible weights, with no family determinant: the Hessenberg composition expansion truncated at the excess the gaps need, every coefficient a polynomial in \(k\) of bounded degree from an explicit threshold, the cancellations and the surviving terms read off those polynomials, and the actions in closed form in \(k\) and the weight values |
| §6.4 Rmk 6.13 | `check_staircase_boundary_all_n.py` | `rem:staircase-boundary` | The remark for every word length: the grid, the three column-zero expansions as index identities in the row and column, the first-column expansion and the three-term relation derived from them and the reversal lemma, and the weight bookkeeping symbolic in the column |
| §6.4 Cor 6.12 | `check_locus_family_independent.py` | `subsec:locus-family`, `cor:locus-family` | The family cofactors rebuilt by full symbolic determinants, a route sharing nothing with the cheap recurrences |
| §6.4 Prop 6.11 (FULL) | `check_specialization_bridge.py` | `subsec:locus-family`, `prop:staircase-reversal` | The specialization carrying the abstract lemma onto the capped boards, over every word to the stated length |
| §6.4 Rmk 6.13 (FULL) | `check_boundary_three_exclusion.py` | `subsec:locus-family`, `rem:staircase-boundary` | The boundary-three exclusion: grid, bridge, kernel relation, nonpalindromes and the valuation calibration |
| §7 Thm 7.1 | `check_two_cap_exclusion_arithmetic.py` | `thm:two-cap` | The cap-shift identity, the \(r>0\) and \(r=0\) branches, and the Floor-to-hypothesis chain, over exhaustive parameter ranges |
| §8 Rmk 8.5 | `check_ribbon_reversal_freedom.py` | `rem:factorwise`, `sec:application` | Reversing one factor of a two-factor composition can produce a partner that is neither the composition nor its reverse |
| §8, §9, §A, §B | `check_scope_and_structural_census.py` | `prop:caterpillar`, `prop:elbow`, `subsec:weight-scope`, `subsec:floor-margin`, `subsec:fingerprint-not-classification`, `thm:first-split-majorization`, `rem:higher-strata`, `prop:cap-fixed-comparability`, `rem:which-floor`, `thm:abstract-monge`, `rem:abstract-family` | The four-point monomial identity and the Plücker relation on every feasible staircase, with the feasibility hypothesis shown necessary; the elbow cone on a box; the radix weight injective on every monomial of the capped cofactors; the dilation family and the fingerprint pair; strict majorization of the peel multisets on every cap-fixed pair with equal multisets, comparability under a single non-top transfer and the incomparable moving-cap witness; the two floor functionals; and the abstract Strict-Monge principle on a cost that is not Jacobi–Trudi, with the scaled-row pair showing the sampling hypothesis necessary |
| §2 Def 2.2, §3 Lem 3.7, Lem 3.8, Thm 3.9 | `check_strict_monge_all_admissible_weights.py` | `def:convex-weight`, `lem:strict-monge`, `lem:feasible-uncrossing`, `thm:monge-minor` | The Strict-Monge statements for every admissible weight at once: the weight of a monomial is a nonnegative integer combination of the increments' second differences, so strict inequality at every admissible weight is a componentwise statement checked on a box and on every minor selection of size at most 5, with a linear weight tying as the control |
| §5 Prop 5.1, Cor 5.2, Lem 5.3, Lem 5.4, Thm 5.5, Lem 5.7, Thm 5.8, Thm 5.11, Prop 5.13 | `check_cap_fixed_random_admissible_weights.py` | `prop:synchronization`, `cor:first-split-anchor`, `lem:tropical-balancing`, `lem:tail-increase`, `thm:no-backflow`, `lem:marching`, `thm:cap-fixed-rigidity`, `thm:equal-pair-rigidity`, `prop:monomial-prefix` | The cap-fixed statements at 24 seeded random admissible weights, over every pair on a common cap grid with no multiset filter, on both sides of the floor antecedent |
| §7 Thm 7.1 | `check_two_cap_exclusion_on_formal_vectors.py` | `thm:two-cap`, `eq:two-caps`, `eq:floor-input`, `eq:Phi` | The exclusion run on actual h-polynomial vectors: the valuation of the \(j=0\) summand of the shifted sums, no two coexisting caps under the floor input, and vectors with two vanishing caps built from \(2\times3\) minors on which the floor input must fail |
| §B Lem B.1, Prop B.3 | `check_passive_starvation_and_block_factorization.py` | `lem:starvation`, `prop:block-factorization`, `cor:both-passive`, `app:rank4` | Passive-tail starvation \(\lvert R_{\mathrm{high}}\rvert\le P-1\), the block factorization of a minor, and both-passive vanishing, over every pair of connected diagrams on a common cap grid |

`check_paper_crossrefs.py` guards the other direction: every `\label` named in the scripts above and
in this file resolves in the manuscript, and none of them cites the paper by number.

## Coverage by section

**Work in progress.**  All proofs in the paper are unconditional and noncomputational.  A row
marked **⚠️ Partial** below reflects the state of the computational supplement, not of the paper.
Each check is exhaustive over the stated finite range, which tests the finite arithmetic and the
hypothesis boundaries; it is not a proof for all parameters.

| Paper content | Status | Note |
|---|---|---|
| Coordinates, the extension lemma and the ratio quantity (`sec:coordinates`) | ✅ Full | the extension lemma and the iterated-cap identity on every diagram; the ratio quantity as a skew Schur function |
| Strict-Monge geometry (`sec:geometry`) | ✅ Full | every weight-generic statement at four admissible weights and the Strict-Monge triple at every admissible weight at once; the unique initial monomial of every feasible minor |
| Capped cofactors as skew Schur functions (`lem:cofactor-factorization`) | ✅ Full | every presentation, connected or not, to the size and row caps |
| Reconstruction (`thm:boundary-reconstruction`, `cor:two-positive-extensions`, `prop:stable-cofactor`) | ✅ Full | the prefix-residual induction run as an algorithm; injectivity over all inner boundaries; scalar data; figure numbers |
| First-split localization and cap-fixed rigidity (`thm:cap-fixed-rigidity`, `lem:marching`, `thm:no-backflow`) | ✅ Full | every clause on every cap-fixed pair at four weights, with the floor antecedent shown necessary |
| Equal-pair rigidity (`thm:equal-pair-rigidity`, `prop:monomial-prefix`, `cor:boundary-separation`) | ✅ Full | worked pair and every equal pair in range, at four weights |
| Ratio rigidity and Cancellative Leftmost (`thm:ratio-rigidity`, `thm:floor`, `thm:terminal-gap`) | ✅ Full | the locus enumerated as collisions of the one-diagram ratio quantity, with no pre-filter |
| Reversal pairs on the locus (`subsec:locus-family`) | ✅ Full | the identity over every word to length 9; the corollary by determinants for \(k\le4\) and for every \(k\) by polynomial interpolation in \(k\) of the truncated expansion; the boundary-letter remark for every length |
| Two-cap exclusion (`thm:two-cap`) | ✅ Full | the arithmetic it runs on, the valuation step and the exclusion on formal h-polynomial vectors, two-vanishing-cap vectors on which the floor input fails, the real locus, and both hypotheses shown necessary by formal vectors |
| Composition and reversal (`sec:application`) | ✅ Full | the factor-reversal example and the four-point identity are checked; the section claims no factorization |
| Scope limits (`sec:scope`) | ✅ Full | elbow cone, radix-weight, dilation and fingerprint controls |
| Structural consequences (`app:structural`) | ✅ Full | majorization, comparability, the moving-cap witness and the abstract principle on a non-Jacobi–Trudi cost |
| Passive tail (`app:rank4`) | ✅ Full | on every pair of connected diagrams on a common cap grid in range |

## Dependencies

| Component | Used by | Description |
|---|---|---|
| `_census_common.py` | `check_geometry_census.py`, `check_reconstruction_census.py`, `check_localization_census.py`, `check_ratio_locus_census.py`, `check_locus_family_census.py`, `check_scope_and_structural_census.py` | The shared exact machinery of the census checks: cap coordinates, the capped cofactor vector (a memoized Laplace expansion checked against full permutation expansion), the admissible weights, weights of monomials and polynomials, and the cap-fixed pair object with its normalized actions and tilted costs |
| `check_cofactor_factorization_and_reconstruction.py` | `check_top_deletion_descent.py`, `check_equal_pair_rigidity_unconditional.py`, `check_equality_excludes_ratio_identities.py`, `check_printed_statement_guards.py` | Keeps its row above; also exports the \(h\)-monomial arithmetic (`h`, `padd`, `pmul`, `pscal`, `det`), the capped cofactor matrix and the connected-shape enumerator, so the scripts building on it share one implementation |
| `check_composition_irreducibility.py` | `check_kernel_relation_and_radix_weight.py` | Composition-product and irreducibility machinery used for the terminal-gap witness |
| `check_paper_crossrefs.py` | `run_all.sh` | Label index and the scanner for number citations over every script and this file; run directly |
| `skew_core.py` | `_census_common.py`, `check_monge_minor_sign_and_uncrossing_premise.py`, `check_ratio_identity_forces_equal_row_multisets.py`, `check_ratio_locus_unbounded_support_family.py`, `check_row_count_is_determined_by_the_skew_function.py` | Exact \(h\)-polynomial algebra: the signed monomial dictionaries, the permutation-expansion determinant, the Jacobi–Trudi skew Schur function and the cap-cofactor vector |
| `skew_harness.py` | `_census_common.py`, `check_ratio_identity_forces_equal_row_multisets.py`, `check_row_count_is_determined_by_the_skew_function.py` | Skew-diagram combinatorics: connectedness, the 180-degree rotation, and the enumerator of every connected diagram to a size and row bound |
| matplotlib | `make_figures.py` | Draws the two figures; imported only when the figures are written, not by `--check-only` |
| `requirements.txt` | all scripts | SymPy and mpmath pins; the exact-arithmetic scripts use only the standard library, and the symbolic witness checks use SymPy |

## License

MIT — see `LICENSE.txt` in this directory.  This directory is also subject to the patent and
trademark terms in the LICENSE.txt at the root of the repository.

## References

Refer to the paper for references.
