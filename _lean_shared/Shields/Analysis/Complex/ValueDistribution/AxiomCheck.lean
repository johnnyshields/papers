/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Complex.ValueDistribution.OddPart

/-!
# Axiom footprint of the value-distribution modules

Every result in `Shields.Analysis.Complex.ValueDistribution` depends on exactly Mathlib's ambient
footprint `[propext, Classical.choice, Quot.sound]`, or on a shorter one where the proof needs no
choice.  A `sorry` anywhere in a dependency chain makes `#print axioms` report `sorryAx`,
`#guard_msgs` then errors, and `lake build` fails.  These guards pin the actual footprint of each
result rather than the ambient one, so a shorter proof that inflates the axiom set is caught.
-/

namespace Shields

/-! ## Transfer of a bound off an exceptional set of finite measure -/

/-- info: 'Shields.exists_good_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_good_radius

/-- info: 'Shields.isBigO_rpow_of_monotoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isBigO_rpow_of_monotoneOn

/-! ## Exponent of convergence -/

/-- info: 'Shields.expConvergence_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expConvergence_le

/-- info: 'Shields.log_le_rpow_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log_le_rpow_div

/-- info: 'Shields.logCounting_le_const_mul_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logCounting_le_const_mul_rpow

/-- info: 'Shields.summable_rpow_of_summable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms summable_rpow_of_summable_zero

/-! ## Order of growth -/

/-- info: 'Shields.order_le_of_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms order_le_of_isBigO

/-- info: 'Shields.order_eq_zero_of_forall_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms order_eq_zero_of_forall_pos

/-! ## Nevanlinna's theorem -/

/-- info: 'Shields.posLog_le_mul_add_posLog_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms posLog_le_mul_add_posLog_inv

/-- info: 'Shields.characteristic_isBigO_rpow_of_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms characteristic_isBigO_rpow_of_summable

/-- info: 'Shields.order_le_expConvergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms order_le_expConvergence

/-! ## Growth exponents -/

/-- info: 'Shields.isBigO_rpow_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isBigO_rpow_rpow

/-- info: 'Shields.isBigO_rpow_of_order_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isBigO_rpow_of_order_lt

/-! ## From the characteristic to the maximum modulus -/

/-- info: 'Shields.poissonKernel_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms poissonKernel_nonneg

/-- info: 'Shields.poissonKernel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms poissonKernel_le

/-- info: 'Shields.re_le_circleAverage_posPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms re_le_circleAverage_posPart

/-- info: 'Shields.proximity_exp_eq_circleAverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms proximity_exp_eq_circleAverage

/-- info: 'Shields.logCounting_exp_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logCounting_exp_top

/-- info: 'Shields.characteristic_exp_eq_proximity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms characteristic_exp_eq_proximity

/-- info: 'Shields.re_le_characteristic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms re_le_characteristic

/-! ## Polynomial growth -/

/-- info: 'Shields.iteratedDeriv_eq_zero_of_re_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iteratedDeriv_eq_zero_of_re_growth

/-- info: 'Shields.eq_quadratic_of_re_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_quadratic_of_re_growth

/-- info: 'Shields.odd_eq_linear_of_re_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_eq_linear_of_re_growth

/-- info: 'Shields.odd_eq_linear_of_order_lt_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_eq_linear_of_order_lt_three

/-- info: 'Shields.odd_eq_linear_of_order_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_eq_linear_of_order_le_two

/-- info: 'Shields.odd_eq_linear_of_expConvergence_lt_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_eq_linear_of_expConvergence_lt_three

/-- info: 'Shields.odd_eq_linear_of_expConvergence_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_eq_linear_of_expConvergence_le_two


/-! ## Jensen's inequality and the Borel converse -/

/-- info: 'Shields.sum_le_counting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_le_counting

/-- info: 'Shields.dyadic_shell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dyadic_shell

/-- info: 'Shields.summable_rpow_of_counting_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms summable_rpow_of_counting_le

/-- info: 'Shields.counting_le_log_div_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counting_le_log_div_log_two

/-- info: 'Shields.norm_le_re_of_nonneg_coeffs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_le_re_of_nonneg_coeffs

/-- info: 'Shields.norm_le_norm_ofReal_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_le_norm_ofReal_norm

/-- info: 'Shields.summable_rpow_divisor_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms summable_rpow_divisor_of_growth

/-! ## The odd part of a real entire exponent -/

/-- info: 'Shields.im_eq_zero_of_exp_im_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms im_eq_zero_of_exp_im_eq_zero

/-- info: 'Shields.deriv_im_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deriv_im_eq_zero

/-- info: 'Shields.oddPart_eq_of_expConvergence_lt_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_expConvergence_lt_three

/-- info: 'Shields.oddPart_eq_of_expConvergence_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_expConvergence_le_two

/-- info: 'Shields.oddPart_eq_of_summable_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_summable_rpow

/-- info: 'Shields.oddPart_eq_of_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_summable

/-- info: 'Shields.im_eq_zero_of_hasSum_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms im_eq_zero_of_hasSum_real

/-- info: 'Shields.oddPart_eq_of_hasSum_of_summable_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_hasSum_of_summable_rpow

/-- info: 'Shields.oddPart_eq_of_hasSum_of_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_hasSum_of_summable

/-- info: 'Shields.divisor_negOne_eq_divisor_evenPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms divisor_negOne_eq_divisor_evenPart

/-- info: 'Shields.divisor_posPart_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms divisor_posPart_eq_self

/-- info: 'Shields.oddPart_eq_of_hasSum_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_hasSum_of_growth

end Shields
