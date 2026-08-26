/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Main
import CubicPochhammer.Multiplicity
import CubicPochhammer.Consequences
import CubicPochhammer.Differential

/-!
# Axiom regression guard

A build-time check that the development stays sorry-free and axiom-free.  Each
`#guard_msgs in #print axioms …` pins the axiom footprint of one result to
Lean's three standard axioms `[propext, Classical.choice, Quot.sound]` and
nothing else.  If a `sorry` or a stray `axiom` ever enters a dependency, the
reported footprint changes and `#guard_msgs` turns the mismatch into a build
error — so `lake build` fails rather than silently degrading the claims in
`README.md`.

The guard binds in both directions: a footprint that grows fails the build, and
so does one that shrinks, since the pinned string no longer matches either way.
So a result whose proof stops depending on something cannot pass silently -- the
table has to be brought back into agreement with what the build reports.

The expected strings are copied from the build's own output.  `#print axioms`
sorts the list, and a project axiom would print unqualified inside
`namespace CubicPochhammer`, so it would appear inside the three standard names
rather than after them.

## Implementation notes

The guarded results are grouped by the part of the paper they belong to, with a
`/-! ### -/` header per group; the groups follow the order of
`shields-2026-cubic-pochhammer.tex`.

## References

* `shields-2026-cubic-pochhammer.tex`, and `lean/README.md`, whose per-item
  status table this file pins.
-/

namespace CubicPochhammer

/-! ### Deep combinatorial core -/

/-- info: 'CubicPochhammer.snj_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms snj_nonneg

/-- info: 'CubicPochhammer.three_residueSum_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_residueSum_closed

/-- info: 'CubicPochhammer.three_snj_table_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_snj_table_zero

/-- info: 'CubicPochhammer.three_snj_table_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_snj_table_one

/-- info: 'CubicPochhammer.three_snj_table_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_snj_table_two

/-- info: 'CubicPochhammer.three_snj_table_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_snj_table_three

/-- info: 'CubicPochhammer.three_snj_table_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_snj_table_four

/-- info: 'CubicPochhammer.three_snj_table_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_snj_table_five

/-- info: 'CubicPochhammer.snj_delta_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms snj_delta_lower

/-- info: 'CubicPochhammer.snj_two_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms snj_two_eq

/-- info: 'CubicPochhammer.snj_two_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms snj_two_pos

/-- info: 'CubicPochhammer.bcoeff_two_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bcoeff_two_eq

/-- info: 'CubicPochhammer.bcoeff_two_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bcoeff_two_pos

/-! ### `eq:P-coeff`: the Bernstein transform and the two revision
identities, and the certificate they carry -/

/-- info: 'CubicPochhammer.bernstein_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bernstein_reconstruction

/-- info: 'CubicPochhammer.revision_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms revision_one

/-- info: 'CubicPochhammer.revision_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms revision_two

/-- info: 'CubicPochhammer.three_jm_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_jm_monomial

/-- info: 'CubicPochhammer.pcoef_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pcoef_transform

/-- info: 'CubicPochhammer.jm_bernstein' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jm_bernstein

/-- info: 'CubicPochhammer.jm_eq_bcoeff_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jm_eq_bcoeff_sum

/-- info: 'CubicPochhammer.jm_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jm_pos

/-! ### The weighting principle (`lem:weighting`) -/

/-- info: 'CubicPochhammer.sum_weighted_abel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_weighted_abel

/-- info: 'CubicPochhammer.sum_weighted_nonneg_iff_tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_weighted_nonneg_iff_tails

/-- info: 'CubicPochhammer.sum_weighted_pos_of_tails_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_weighted_pos_of_tails_pos

/-- info: 'CubicPochhammer.sum_weighted_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_weighted_nonneg

/-- info: 'CubicPochhammer.sum_weighted_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_weighted_pos

/-! ### The pairing reindexing and the single sign change of the blocks -/

/-- info: 'CubicPochhammer.sum_weighted_aterm_eq_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_weighted_aterm_eq_blocks

/-- info: 'CubicPochhammer.sum_blocks_eq_jm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_blocks_eq_jm

/-- info: 'CubicPochhammer.block_sign_change' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms block_sign_change

/-- info: 'CubicPochhammer.bblock_top_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bblock_top_pos

/-! ### `eq:J-weighted` and `thm:kernel` -/

/-- info: 'CubicPochhammer.gmw_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gmw_proj

/-- info: 'CubicPochhammer.gmwNum_deriv_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gmwNum_deriv_key

/-- info: 'CubicPochhammer.hasDerivAt_gmw_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_gmw_proj

/-- info: 'CubicPochhammer.jmw_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jmw_nonneg

/-- info: 'CubicPochhammer.jmw_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jmw_pos

/-- info: 'CubicPochhammer.gmw_monotoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gmw_monotoneOn

/-- info: 'CubicPochhammer.gmw_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gmw_strictMonoOn

/-! ### `lem:central-products` and its chain `eq:central-products` -/

/-- info: 'CubicPochhammer.centralProducts_of_logConcave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms centralProducts_of_logConcave

/-- info: 'CubicPochhammer.centralProducts_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms centralProducts_chain

/-- info: 'CubicPochhammer.centralProducts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms centralProducts_iff

/-! ### The endpoint identity, the parameter symmetry, and the nonnegativity
`thm:main`'s boundary cases consume -/

/-- info: 'CubicPochhammer.cmw_right_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmw_right_zero

/-- info: 'CubicPochhammer.cmf_right_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmf_right_zero

/-- info: 'CubicPochhammer.cmw_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmw_symm

/-- info: 'CubicPochhammer.cmw_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmw_nonneg

/-! ### `lem:beta-order`, `eq:C-beta-binomial` and the beta-binomial
reduction `eq:C-beta` -/

/-- info: 'CubicPochhammer.gmw_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gmw_symm

/-- info: 'CubicPochhammer.bmom_eq_Gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bmom_eq_Gamma

/-- info: 'CubicPochhammer.bmom_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bmom_shift

/-- info: 'CubicPochhammer.cosh_ratio_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosh_ratio_cross

/-- info: 'CubicPochhammer.foldKer_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms foldKer_cross

/-- info: 'CubicPochhammer.integral_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_fold

/-- info: 'CubicPochhammer.beta_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms beta_order

/-- info: 'CubicPochhammer.aint_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aint_eq

/-! ### `cor:C-schur` at the weights `eq:w-from-f` -/

/-- info: 'CubicPochhammer.cmw_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmw_balance

/-- info: 'CubicPochhammer.cmw_antitone_imbalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmw_antitone_imbalance

/-- info: 'CubicPochhammer.cmw_schur_of_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmw_schur_of_kernel

/-! ### Main theorem (fixed-sum Schur-concavity) and its Turanian
specialization -/

/-- info: 'CubicPochhammer.schur_coeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms schur_coeff_nonneg

/-- info: 'CubicPochhammer.turan_coeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms turan_coeff_nonneg

/-- info: 'CubicPochhammer.turan_coeff_nonneg_of_logConcave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms turan_coeff_nonneg_of_logConcave

/-! ### `lem:beta-order`'s strict clause, and the strict results it carries -/

/-- info: 'CubicPochhammer.beta_order_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms beta_order_strict

/-- info: 'CubicPochhammer.cmw_strictAntiOn_imbalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmw_strictAntiOn_imbalance

/-! ### `cor:strict` `eq:delta-C`, both halves, and at `thm:main`'s own hypothesis -/

/-- info: 'CubicPochhammer.cmf_delta_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmf_delta_pos_iff

/-- info: 'CubicPochhammer.turan_delta_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms turan_delta_pos_iff

/-- info: 'CubicPochhammer.cmf_delta_pos_iff_of_logConcave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmf_delta_pos_iff_of_logConcave

/-- info: 'CubicPochhammer.turan_delta_pos_iff_of_logConcave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms turan_delta_pos_iff_of_logConcave

/-! ### `prop:kernel-exact`, the converse direction and the equivalence -/

/-- info: 'CubicPochhammer.gmw_monotoneOn_of_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gmw_monotoneOn_of_schur

/-- info: 'CubicPochhammer.kernel_exact_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel_exact_iff

/-! ### `sec:threshold`: `eq:r-degree-three`, `eq:r-central-slope` and the minimality clauses -/

/-- info: 'CubicPochhammer.twoTerm_degreeThree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoTerm_degreeThree

/-- info: 'CubicPochhammer.twoTerm_degreeThree_neg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoTerm_degreeThree_neg_iff

/-- info: 'CubicPochhammer.ghat_central_slope_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ghat_central_slope_three

/-- info: 'CubicPochhammer.degreeTwo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms degreeTwo_nonneg

/-- info: 'CubicPochhammer.onePoint_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms onePoint_nonneg

/-! ### `cor:multiplicity`, unconditional -- the `r = 2` case is proven here rather than cited -/

/-- info: 'CubicPochhammer.universalLogConcave_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms universalLogConcave_two

/-- info: 'CubicPochhammer.universalLogConcave_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms universalLogConcave_three

/-- info: 'CubicPochhammer.not_universalLogConcave_of_four_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_universalLogConcave_of_four_le

/-- info: 'CubicPochhammer.multiplicity_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multiplicity_classification

/-! ### `cor:ordinary`, and the general concavity step behind it -/

/-- info: 'CubicPochhammer.cor_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cor_ordinary

/-- info: 'CubicPochhammer.strictConcaveOn_of_midpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strictConcaveOn_of_midpoint

/-! ### `cor:differential`, the part that is proven -/

/-- info: 'CubicPochhammer.dcoeff_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dcoeff_at_zero

/-- info: 'CubicPochhammer.dcoeff_eq_zero_of_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dcoeff_eq_zero_of_weights

/-- info: 'CubicPochhammer.dcoeff_at_zero_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dcoeff_at_zero_pos_iff

/-- info: 'CubicPochhammer.dcoeff_tsum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dcoeff_tsum_eq

/-- info: 'CubicPochhammer.hasDerivAt_fser' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_fser

/-- info: 'CubicPochhammer.hasDerivAt_deriv_fser' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_deriv_fser

/-- info: 'CubicPochhammer.psiD2_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms psiD2_at_zero

/-- info: 'CubicPochhammer.dcoeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dcoeff_nonneg

/-- info: 'CubicPochhammer.dcoeff_nonneg_of_logConcave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dcoeff_nonneg_of_logConcave

/-- info: 'CubicPochhammer.pochD_sq_sub_mul_pochD2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pochD_sq_sub_mul_pochD2

/-- info: 'CubicPochhammer.dcoeff_two_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dcoeff_two_pos_iff

end CubicPochhammer
