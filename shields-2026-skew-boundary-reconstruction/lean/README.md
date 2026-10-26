# Lean 4 formalization — Boundary reconstruction and cofactor rigidity for skew Schur functions

A Lean 4 (`v4.34.1`) development in namespace `SkewSchurReconstruction` for `shields-2026-skew-boundary-reconstruction.tex`.  The proof modules contain no `sorry`, project axioms, or `native_decide`; kernel footprint guards cover the principal results and scope witnesses.

The paper reconstructs connected skew diagrams up to translation from two boundary observations, with neither boundary prescribed.  Strict-Monge geometry controls the leading cofactors, the first changed row, and the adjacent cancellation chain; ratio identities supply additional boundary rigidity and exclusion results.

The proofs in the paper are noncomputational and do not depend on the code here.

## Build

```sh
lake exe cache get
lake build
```

The shared `_lean_shared/` directory must be available beside the paper directories.  Mathlib and the toolchain are pinned by the package files.

## Result coverage

All theorem, proposition, and corollary rows below have build-verified proofs at the manuscript's hypotheses.  The status describes the formalization, not the paper: all proofs in the paper are unconditional and noncomputational.

Declaration names below are in namespace `SkewSchurReconstruction`.  Structural rows marked — are definitions or standing assumptions, not missing results.

| Where | Result | Paper | Lean |
|---|---|---|---|
| §1 Thm 1.1 | boundary reconstruction | `thm:boundary-reconstruction` | ✅ Full — `Diagram.boundary_reconstruction_deletion; Diagram.boundary_reconstruction_extension`. Actual boundary observations recover both boundaries with unknown row count. |
| §1 Cor 1.2 | two positive extensions | `cor:two-positive-extensions` | ✅ Full — `Diagram.two_positive_extensions`. Unordered polynomial observations recover the parent up to translation and the unknown unordered cap lengths. |
| §3 Thm 3.9 | monge minor | `thm:monge-minor` | ✅ Full — `monge_minor_initialForm; monge_minor_initial_coefficient`. Unique increasing term, unit coefficient, and feasibility converse. |
| §3 Prop 3.11 | cofactor initial | `prop:cofactor-initial` | ✅ Full — `Diagram.cofactor_initialForm; Diagram.cofactor_leastWeight`. Actual connected-diagram signed cofactors, not an assumed cofactor vector. |
| §3 Prop 3.12 | action recurrence | `prop:action-recurrence` | ✅ Full — `Diagram.parentAction_recurrence; ConvexWeight.strict_monge_int`. Exact action increment and its strict row-parameter comparison. |
| §3 Prop 3.13 | initial energy | `prop:initial-energy` | ✅ Full — `Diagram.parentAction_zero`. Actual cofactor initial action equals row-length energy. |
| §4 Prop 4.2 | stable cofactor | `prop:stable-cofactor` | ✅ Full — `Diagram.rowLength_cofactor_scalar_recovery; Diagram.translationEquivalent_of_cofactorTuple_eq`. Actual degree and square valuation identify both boundaries; denominators are proved nonzero. |
| §5 Prop 5.1 | synchronization | `prop:synchronization` | ✅ Full — `Diagram.parentAction_synchronized; Diagram.parentAction_first_split_ne`. Prefix synchronization and weight-independent first-split direction. |
| §5 Cor 5.2 | first split anchor | `cor:first-split-anchor` | ✅ Full — `Diagram.first_split_anchor`. Nonzero actual defect coordinate and exact minimum parent action. |
| §5 Thm 5.5 | no backflow | `thm:no-backflow` | ✅ Full — `Diagram.defect_no_backflow; Diagram.defect_no_backflow_square_margin`. Qualitative localization and the exact quantitative square-weight margin, including vanishing later coordinates. |
| §5 Thm 5.8 | cap fixed rigidity | `thm:cap-fixed-rigidity` | ✅ Full — `Diagram.cap_fixed_minimizers; Diagram.cap_fixed_floor; Diagram.cap_fixed_action_strict`. The strict floor supplies row multisets; exact adjacent pairs, support, profile, and tail follow. |
| §5 Thm 5.11 | equal pair rigidity | `thm:equal-pair-rigidity` | ✅ Full — `Diagram.equal_pair_rigidity`. Equality supplies cap normalization, the first changed row, and strict floor. |
| §5 Prop 5.13 | monomial prefix | `prop:monomial-prefix` | ✅ Full — `Diagram.cap_fixed_monomial_prefix; Diagram.cap_fixed_prefix_initialForm_eq`. Actual prefix leading terms are unit monomials with alternating signs and are independent of the admissible weight. |
| §6 Thm 6.2 | terminal gap | `thm:terminal-gap` | ✅ Full — `terminal_gap`. Fresh-generator differentiation eliminates a terminal supported shift beyond the actual union-grid bound. |
| §6 Prop 6.4 | top terminal | `prop:top-terminal` | ✅ Full — `Diagram.gridDefect_terminal_of_top_lt; Diagram.lastDefectShift_eq_terminalBound_of_top_ne`. With a common inner boundary, distinct tops force terminal support on the union grid. |
| §6 Cor 6.5 | cap fixing | `cor:cap-fixing` | ✅ Full — `Diagram.ratioIdentity_fixes_cap`. With a common inner boundary, the ratio identity supplies row count, top, and the common cap grid. |
| §6 Thm 6.7 | ratio rigidity | `thm:ratio-rigidity` | ✅ Full — `Diagram.ratio_rigidity; Diagram.ratio_square_gap`. The actual ratio identity supplies normalization, the virtual and genuine adjacent chain, the strict floor, support, and exact general/square gaps. |
| §6 Thm 6.9 | floor | `thm:floor` | ✅ Full — `Diagram.ratio_floor; Diagram.ratio_cancellative_leftmost`. The actual floor functional vanishes automatically; the first positive supported shift lies on its floor. |
| §6 Prop 6.11 | staircase reversal | `prop:staircase-reversal` | ✅ Full — `staircase_ratioIdentity; staircase_schurFunction_ne_reverse; staircase_not_translationEquivalent`. Every binary row-length word with endpoint two gives the actual reversal ratio identity; nonpalindromic words give inequivalent parents. |
| §6 Cor 6.12 | locus family | `cor:locus-family` | ✅ Full — `locusFamily_defect_support; locusFamily_leading_valuations; locusFamily_positive_floor; locusFamily_floor_gap; locusFamily_positive_support_card`. The exact support, valuations, floor face, and unbounded positive support count are proved for every positive scale. |
| §7 Thm 7.1 | two cap | `thm:two-cap` | ✅ Full — `Diagram.two_cap_exclusion`. The explicit global square-floor criterion makes two same-base cap identities impossible. |
| §7 Cor 7.2 | floor supplies | `cor:floor-supplies` | ✅ Full — `Diagram.ratio_floor_supplies`. Actual ratio rigidity supplies zeroth support and the criterion at every supported union-grid shift. |
| §7 Cor 7.3 | double cap kills | `cor:double-cap-kills` | ✅ Full — `Diagram.double_cap_kills`. Two ratio identities force translation and zero defect, with neither boundary prescribed. |
| §7 Cor 7.4 | unique ratio | `cor:unique-ratio` | ✅ Full — `Diagram.unique_ratio`. The square gap fixes the base/cap parameters; the two-cap theorem excludes distinct and mixed-base identities. |
| §8 Prop 8.1 | caterpillar | `prop:caterpillar` | ✅ Full — `caterpillar; caterpillarMinor_initialForm`. Actual double-omission maximal minors have equal crossing initial monomials and strictly larger separated-pair weight for every admissible convex weight. |
| §8 Cor 8.6 | boundary separation | `cor:boundary-separation` | ✅ Full — `Diagram.cap_fixed_boundary_response; Diagram.cap_fixed_ratio_response; Diagram.equal_pair_ratio_exclusion`. Actual positive-cap and ratio responses have the exact leading polynomial and are nonzero. |
| §9 Prop 9.1 | elbow | `prop:elbow` | ✅ Full — `elbowVector_response_zero; elbowVector_ratioIdentity; elbowVector_support; elbowWitness_actions`. Exact formal-vector relations and the square-action witness \((20,18,18)\). |
| §A Thm A.1 | first split majorization | `thm:first-split-majorization` | ✅ Full — `Diagram.first_split_majorization; Diagram.first_split_majorization_reverse`. Actual peel multisets are strictly ordered in standard sorted-prefix dominance, with zeros retained. |
| §A Prop A.3 | cap fixed comparability | `prop:cap-fixed-comparability` | ✅ Full — `Diagram.cap_fixed_comparability`. Every actual peel of a single non-top transfer is comparable in sorted-prefix dominance. |
| §A Cor A.4 | solid prefix | `cor:solid-prefix` | ✅ Full — `Diagram.ratio_rigidity`. Every coordinate from zero through the first-split barrier is nonzero on the actual ratio locus. |
| §A Thm A.6 | abstract monge | `thm:abstract-monge` | ✅ Full — `ValuedMongeFamily.abstract_monge`. All four clauses over independently ordered row and column index types, an arbitrary ordered additive value group, and an actual common entry family. |
| §B Cor B.2 | both passive | `cor:both-passive` | ✅ Full — `Diagram.passive_tail_both_passive`. Actual passive/starved suffixes supply the two-column obstruction under the stated saturated-capacity hypothesis. |
| §B Prop B.3 | block factorization | `prop:block-factorization` | ✅ Full — `Diagram.passive_tail_block_factorization`. Selected passive columns form the required suffix; the actual sorted determinant factors with no permutation sign. |

## Structural coverage

| Where | Result | Paper | Lean |
|---|---|---|---|
| §1 eq. (1.1) | edge chain intro | `eq:edge-chain-intro` | ✅ Full — `Diagram.equal_pair_rigidity; Diagram.ratio_rigidity`. |
| §2 eq. (2.1) | Adef | `eq:Adef` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.2) | ddef | `eq:ddef` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.3) | dexplicit | `eq:dexplicit` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.4) | capmatrix | `eq:capmatrix` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.5) | cofactor | `eq:cofactor` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.6) | defect | `eq:defect` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.7) | Pk | `eq:Pk` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.8) | first change | `eq:first-change` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.9) | q def | `eq:q-def` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.10) | common row relation | `eq:common-row-relation` | ✅ Full — `Diagram.common_row_defect_relation`. |
| §2 eq. (2.11) | P0 vanishes | `eq:P0-vanishes` | ✅ Full — `Diagram.capPolynomial_zero`. |
| §2 eq. (2.12) | ratio identity | `eq:ratio-identity` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.13) | Pk is capped | `eq:Pk-is-capped` | ✅ Full — `Diagram.schurFunction_extendNortheast`. |
| §2 Lem 2.1 | extension cofactors | `lem:extension-cofactors` | ✅ Full — Diagram.cofactor_extendNortheast; Diagram.schurFunction_iterated_extendNortheast |
| §2 eq. (2.14) | iterated cap | `eq:iterated-cap` | ✅ Full — `Diagram.schurFunction_iterated_extendNortheast`. |
| §2 Def 2.2 | convex weight | `def:convex-weight` | — Notation or contextual definition; no separate proof obligation. |
| §2 eq. (2.15) | alpha general | `eq:alpha-general` | — Definition or genuine standing assumption; its consumers are graded above. |
| §2 eq. (2.16) | F general | `eq:F-general` | — Definition or genuine standing assumption; its consumers are graded above. |
| §3 Lem 3.1 | grid order | `lem:grid-order` | ✅ Full — Diagram.rowParam_strictMono; Diagram.capShift_strictMono |
| §3 Lem 3.2 | diagonal feasible | `lem:diagonal-feasible` | ✅ Full — Diagram.diagonal_feasible |
| §3 eq. (3.1) | diagonal feasible | `eq:diagonal-feasible` | ✅ Full — `Diagram.diagonal_feasible`. |
| §3 Lem 3.4 | cofactor factorization | `lem:cofactor-factorization` | ✅ Full — Diagram.cofactor_shear_determinant; Diagram.cofactor_ne_zero_iff_contained |
| §3 eq. (3.2) | nu j | `eq:nu-j` | — Definition or genuine standing assumption; its consumers are graded above. |
| §3 eq. (3.3) | cofactor support | `eq:cofactor-support` | ✅ Full — `Diagram.cofactor_ne_zero_iff_contained`. |
| §3 eq. (3.4) | cofactor schur | `eq:cofactor-schur` | ✅ Full — `Diagram.cofactor_shear_determinant`. |
| §3 Lem 3.6 | valuation laws | `lem:valuation-laws` | ✅ Full — monomialValuation_mul; monomialValuation_add_ge; monomialValuation_add_eq_min |
| §3 Lem 3.7 | strict monge | `lem:strict-monge` | ✅ Full — ConvexWeight.strict_monge_int |
| §3 Lem 3.8 | feasible uncrossing | `lem:feasible-uncrossing` | ✅ Full — uncrossMatching_feasible |
| §3 eq. (3.5) | matching index | `eq:matching-index` | — Definition or genuine standing assumption; its consumers are graded above. |
| §3 eq. (3.6) | cofactor initial | `eq:cofactor-initial` | ✅ Full — `Diagram.cofactor_initialForm`. |
| §3 eq. (3.7) | cofactor val | `eq:cofactor-val` | ✅ Full — `Diagram.cofactor_monomialValuation`. |
| §3 eq. (3.8) | sigma def | `eq:sigma-def` | — Definition or genuine standing assumption; its consumers are graded above. |
| §3 eq. (3.9) | initial energy | `eq:initial-energy` | ✅ Full — `Diagram.parentAction_zero`. |
| §4 Lem 4.1 | distinguished | `lem:distinguished` | ✅ Full — Diagram.cofactor_initialForm; Diagram.exchangeRow_eq_rowLength; Diagram.exchangeZero_next_eq_overlap |
| §4 eq. (4.1) | Qj | `eq:Qj` | ✅ Full — `Diagram.cofactor_initialForm and row/overlap coordinate identities`. |
| §4 eq. (4.2) | scalar data | `eq:scalar-data` | — Definition or genuine standing assumption; its consumers are graded above. |
| §4 eq. (4.3) | scalar recovery | `eq:scalar-recovery` | ✅ Full — `Diagram.rowLength_cofactor_scalar_recovery`. |
| §4 Lem 4.3 | top row cofactor | `lem:top-row-cofactor` | ✅ Full — Diagram.cofactor_one_eq_neg_deleteFirstRow |
| §4 Lem 4.4 | two cofactor reconstruction | `lem:two-cofactor-reconstruction` | ✅ Full — Diagram.translationEquivalent_of_two_cofactors_eq |
| §4 Rmk 4.5 | one extension insufficient | `rem:one-extension-insufficient` | ✅ Full — `Diagram.one_extension_insufficient; Diagram.oneObservation_not_translationEquivalent`. Every prescribed positive extension length admits actual connected nontranslate parents with equal extension and unequal original Schur functions. |
| §5 eq. (5.1) | synchronized | `eq:synchronized` | ✅ Full — `Diagram.parentAction_synchronized`. |
| §5 eq. (5.2) | first split | `eq:first-split` | ✅ Full — `Diagram.parentAction_first_split_ne`. |
| §5 Lem 5.3 | tropical balancing | `lem:tropical-balancing` | ✅ Full — Diagram.defectMinimizers_card_ge_two |
| §5 eq. (5.3) | F parent | `eq:F-parent` | — Definition or genuine standing assumption; its consumers are graded above. |
| §5 Lem 5.4 | tail increase | `lem:tail-increase` | ✅ Full — Diagram.parentTiltedProfile_step_lt |
| §5 eq. (5.4) | no backflow | `eq:no-backflow` | ✅ Full — `Diagram.defect_no_backflow`. |
| §5 eq. (5.5) | no backflow margin | `eq:no-backflow-margin` | ✅ Full — `Diagram.defect_no_backflow_square_margin`. |
| §5 eq. (5.6) | R upper | `eq:R-upper` | ✅ Full — `Diagram.defectMinimizers_le_split`. |
| §5 Lem 5.7 | marching | `lem:marching` | ✅ Full — Diagram.defectMinimizers_interlace; interlacing_max_strict |
| §5 eq. (5.7) | floor antecedent general | `eq:floor-antecedent-general` | — Definition or genuine standing assumption; its consumers are graded above. |
| §5 eq. (5.8) | adjacent chain capfixed | `eq:adjacent-chain-capfixed` | ✅ Full — `Diagram.cap_fixed_minimizers`. |
| §5 eq. (5.9) | floor set general | `eq:floor-set-general` | ✅ Full — `Diagram.cap_fixed_floor`. |
| §5 eq. (5.10) | support prefix | `eq:support-prefix` | ✅ Full — `Diagram.cap_fixed_prefix_support`. |
| §5 eq. (5.11) | prefix profile | `eq:prefix-profile` | ✅ Full — `Diagram.cap_fixed_action_strict`. |
| §5 Lem 5.10 | equality normalizes cap | `lem:equality-normalizes-cap` | ✅ Full — Diagram.equality_normalizes_cap |
| §5 eq. (5.12) | largest index | `eq:largest-index` | ✅ Full — `Diagram.terminalGenerator_largest`. |
| §5 eq. (5.13) | equal pair chain | `eq:equal-pair-chain` | ✅ Full — `Diagram.equal_pair_rigidity`. |
| §5 Rmk 5.12 | no virtual row | `rem:no-virtual-row` | — Convention distinguishing equality from the nonzero-defect ratio problem. |
| §5 eq. (5.14) | monomial prefix exchange | `eq:monomial-prefix-exchange` | ✅ Full — `Diagram.cap_fixed_initial_pair_relation`. |
| §5 Ex 5.14 | actual equal chain | `ex:actual-equal-chain` | ✅ Full — `Diagram.equalChain_defect; Diagram.equalChain_square_actions; Diagram.equalChain_zero_minimizers; Diagram.equalChain_one_minimizers`. Actual boundaries, grid, Schur equality, kernel relations, adjacent minima, and separated deletions. |
| §6 Lem 6.1 | ratio row lengths | `lem:ratio-row-lengths` | ✅ Full — `Diagram.rowLength_multiset_eq_of_ratioIdentity`. |
| §6 eq. (6.1) | bounded generator | `eq:bounded-generator` | ✅ Full — `gridDefect_coefficient_vars_bound`. |
| §6 Rmk 6.3 | realizability terminal | `rem:realizability-terminal` | ✅ Full — `formalTerminalVector_terminal_failure; formalTerminalVector_not_actual`. The constant formal vector satisfies every base-zero ratio identity but violates the terminal bound and the actual zeroth-row relation. |
| §6 eq. (6.2) | gamma | `eq:gamma` | — Definition or genuine standing assumption; its consumers are graded above. |
| §6 eq. (6.3) | virtual edge | `eq:virtual-edge` | ✅ Full — `Diagram.ratio_virtual_minimizers_normalized`. |
| §6 eq. (6.4) | full edge chain | `eq:full-edge-chain` | ✅ Full — `Diagram.ratio_rigidity`. |
| §6 eq. (6.5) | universal floor set | `eq:universal-floor-set` | ✅ Full — `Diagram.ratio_rigidity`. |
| §6 eq. (6.6) | automatic floor antecedent | `eq:automatic-floor-antecedent` | ✅ Full — `Diagram.ratio_strict_floor_normalized`. |
| §6 eq. (6.7) | virtual gap general | `eq:virtual-gap-general` | ✅ Full — `Diagram.ratio_virtual_gap_normalized`. |
| §6 eq. (6.8) | square gap | `eq:square-gap` | ✅ Full — `Diagram.ratio_square_gap`. |
| §6 eq. (6.9) | P0 | `eq:P0` | ✅ Full — `gridDefect_response_zero`. |
| §6 eq. (6.10) | J0 | `eq:J0` | — Definition or genuine standing assumption; its consumers are graded above. |
| §6 Lem 6.8 | laplace equivalence | `lem:laplace-equivalence` | ✅ Full — `Diagram.laplaceFloorSum_eq_zero_iff`. |
| §6 eq. (6.11) | J0 equivalence | `eq:J0-equivalence` | ✅ Full — `Diagram.laplaceFloorSum_eq_zero_iff`. |
| §6 eq. (6.12) | floor | `eq:floor` | ✅ Full — `Diagram.ratio_cancellative_leftmost`. |
| §6 eq. (6.13) | floor strong | `eq:floor-strong` | ✅ Full — `Diagram.ratio_floor`. |
| §6.4 | reversal pair count | `subsec:locus-family` | ✅ Full — `binary_words_card; palindromic_words_card; nonpalindromic_reversal_pairs_card`. The total, palindromic, and unordered nonpalindromic reversal counts are exact for every interior length, including the zero and one boundaries. |
| §6 Lem 6.10 | two series reversal | `lem:two-series-reversal` | ✅ Full — `TwoSeries.wordMatrix_det_reversal; TwoSeries.wordMatrix_det_coefficientMinor`. Generic commutative-ring series with unit constant coefficient, including the actual sorted residual minor. |
| §6 eq. (6.14) | word minor | `eq:word-minor` | ✅ Full — `TwoSeries.wordMatrix_det_coefficientMinor`. |
| §6 Rmk 6.13 | staircase boundary | `rem:staircase-boundary` | ✅ Full — `staircase_boundary_three_relation; staircase_boundary_three_ratio_exclusion; endpointThreeWitness_residual_initialForm`. Endpoint-three words have the exact correction relation and are excluded from the ratio locus; the literal smallest-word initial form is proved on the actual four-row diagrams. |
| §7 eq. (7.1) | Phi | `eq:Phi` | — Definition or genuine standing assumption; its consumers are graded above. |
| §7 eq. (7.2) | two caps | `eq:two-caps` | — Definition or genuine standing assumption; its consumers are graded above. |
| §7 eq. (7.3) | floor input | `eq:floor-input` | — Definition or genuine standing assumption; its consumers are graded above. |
| §7 eq. (7.4) | cap shift | `eq:cap-shift` | ✅ Full — `cap_shift_square`. The finite difference of actual supported summand weights is exactly the asserted square-weight shift. |
| §8 eq. (8.1) | tropical seam chain | `eq:tropical-seam-chain` | ✅ Full — `Diagram.equal_pair_rigidity`. |
| §8 Def 8.2 | reversal | `def:reversal` | — Notation or contextual definition; no separate proof obligation. |
| §8 Def 8.3 | composition | `def:composition` | — Notation or contextual definition; no separate proof obligation. |
| §8 Def 8.4 | generated | `def:generated` | — Notation or contextual definition; no separate proof obligation. |
| §8 Rmk 8.5 | factorwise | `rem:factorwise` | ✅ Full — `factorwise_census_minimal; factorwise_census_four_at_nine`. Actual ribbon Schur equality below total nine permits only global reversal; four distinct connected equal ribbons occur at nine. |
| §8 eq. (8.2) | cap leading monomial | `eq:cap-leading-monomial` | ✅ Full — `Diagram.cap_fixed_boundary_response`. |
| §8 eq. (8.3) | ratio leading monomial | `eq:ratio-leading-monomial` | ✅ Full — `Diagram.cap_fixed_ratio_response`. |
| §9.2 | radix separation | `subsec:weight-scope` | ✅ Full — `Diagram.cofactor_support_exponent_le; Diagram.cofactor_radixWeight_injective; Diagram.cofactor_radixCollapse_coeff; Diagram.cofactor_radixCollapse_eq_iff`. Actual cofactor digit bounds supply exact coefficient recovery and equality reflection at every admissible radix larger than the row count. |
| §9 eq. (9.1) | radix weight | `eq:radix-weight` | — Definition or genuine standing assumption; its consumers are graded above. |
| §9.3 | strict floor and unbounded slack | `subsec:floor-margin` | ✅ Full — `Diagram.floorMargin_square_actions; Diagram.floorMargin_firstPositiveShift_not_floor; Diagram.floorMargin_gap_unbounded`. Actual three-row families have zeroth action equal to the floor but an arbitrarily large leftmost-action excess, with fixed support cardinality. |
| §9.4 | fingerprint is not equality | `subsec:fingerprint-not-classification` | ✅ Full — `Diagram.fingerprint_not_equality_certificate; Diagram.fingerprint_square_actions`. The actual strict-floor example has unequal Schur functions and the stated action tuple. |
| §A Rmk A.2 | higher strata | `rem:higher-strata` | ✅ Full — `Diagram.higherStratum_weight_forty_three; higherStratum_padded_incomparable; movingCap_actual_peels_incomparable`. Actual six-row residual strata and moving-cap peel witnesses have equal weights but incomparable index multisets. |
| §A Rmk A.5 | which floor | `rem:which-floor` | ✅ Full — `Diagram.ratio_shifted_floor`. The normalized and shifted minimizing pairs agree at base zero and differ at positive base. |
| §A eq. (A.1) | abstract prefix | `eq:abstract-prefix` | — Definition or genuine standing assumption; its consumers are graded above. |
| §A eq. (A.2) | abstract normalization | `eq:abstract-normalization` | — Definition or genuine standing assumption; its consumers are graded above. |
| §A Rmk A.7 | abstract family | `rem:abstract-family` | ✅ Full — `abstractFamily_witness; abstractFamily_no_common_sampling`. Actual polynomial boards have supported strictly-Monge entries and equal cofactor valuations but cannot be sampled from one such family. |
| §B Lem B.1 | starvation | `lem:starvation` | ✅ Full — `Diagram.passive_tail_starvation`. |
| §B eq. (B.1) | block det | `eq:block-det` | ✅ Full — `Diagram.passive_tail_block_factorization`. |

## Differences from the paper

`Diagram.ratio_virtual_minimizers_normalized` restricts the equality chain of actual single or double extensions to the original rows; the manuscript balances the virtual row directly.  `TwoSeries.coordinate_rows_det` extracts the surviving minor through the formalized generalized Laplace identity rather than deleting coordinate rows serially.  These routes preserve the stated hypotheses and conclusions.

## Dependencies

The development references shared modules from `_lean_shared/`; their sources are not duplicated in this directory.

| Component | Used by | Description |
|---|---|---|
| `Shields.Combinatorics.Young.LGVTableau` | `TableauBridge`, `RowMultisets` | Bounded skew-tableau sums and the unconditional Jacobi–Trudi theorem, shared with the Edrei formalizations. |
| `Vendor.AlgebraicCombinatorics.CauchyBinet` | `TwoSeriesReversal` | Generalized Laplace expansion and complementary minors from the same external algebraic-combinatorics project. |
| `Vendor.AlgebraicCombinatorics.DeterminantsBasic` | `MongeMinors` | Row-to-column determinant expansion from Fabian Gloeckle and the algebraic-combinatorics contributors, Meta Platforms. |
| `Vendor.AlgebraicCombinatorics.SymmetricFunctions.Definitions` | `SymmetricSpecialization` | Complete symmetric polynomial algebraic independence from the same external algebraic-combinatorics project. |

## License

The files in this directory are released under the MIT license; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the `LICENSE.txt` at the root of the repository.

The shared AlgebraicCombinatorics dependency retains its Creative Commons Attribution–NonCommercial 4.0 license and its upstream attribution.

## References

1. J. Shields, *Boundary reconstruction and cofactor rigidity for skew Schur functions*.
2. D. Grinberg, *An Introduction to Algebraic Combinatorics*, arXiv:2506.00738.  The shared formalization is [facebookresearch/algebraic-combinatorics](https://github.com/facebookresearch/algebraic-combinatorics).

Refer to the paper for references.
