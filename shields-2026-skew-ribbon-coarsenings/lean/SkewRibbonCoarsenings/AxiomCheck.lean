/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Assembly
import SkewRibbonCoarsenings.ParityExample
import SkewRibbonCoarsenings.SubsetDP
import SkewRibbonCoarsenings.Nonlinear
import SkewRibbonCoarsenings.LogarithmicCutoff
import SkewRibbonCoarsenings.ClassInclusion

/-!
# Axiom regression guard

Each `#guard_msgs in #print axioms …` pins the axiom footprint of one headline result to Lean's
three standard axioms `[propext, Classical.choice, Quot.sound]`.  A `sorry` or a stray `axiom` in any
dependency changes the reported footprint and turns into a build error.  The guard binds in both
directions: a footprint that shrinks fails too, and is brought back into agreement deliberately.
The expected strings are copied from the build's own output.
-/

namespace SkewRibbonCoarsenings

/-- info: 'SkewRibbonCoarsenings.thm_main_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thm_main_structure

/-- info: 'SkewRibbonCoarsenings.eq_congruence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_congruence

/-- info: 'SkewRibbonCoarsenings.eq_REV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_REV

/-- info: 'SkewRibbonCoarsenings.eq_two_factor_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_two_factor_cancel

/-- info: 'SkewRibbonCoarsenings.thm_main_recognition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thm_main_recognition

/-- info: 'SkewRibbonCoarsenings.eq_main_modular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_main_modular

/-- info: 'SkewRibbonCoarsenings.thm_main_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thm_main_depth

/-- info: 'SkewRibbonCoarsenings.thm_main_depth_modular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thm_main_depth_modular

/-- info: 'SkewRibbonCoarsenings.cor_odd_characteristic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cor_odd_characteristic

/-- info: 'SkewRibbonCoarsenings.localAlternativeB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms localAlternativeB

/-- info: 'SkewRibbonCoarsenings.localAlternativeOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms localAlternativeOmega

/-- info: 'SkewRibbonCoarsenings.supportSeparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supportSeparation

/-- info: 'SkewRibbonCoarsenings.nested_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_identity

/-- info: 'SkewRibbonCoarsenings.thm_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thm_lift

/-- info: 'SkewRibbonCoarsenings.termination_common_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms termination_common_factor

/-- info: 'SkewRibbonCoarsenings.packing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms packing

/-- info: 'SkewRibbonCoarsenings.propagation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms propagation

/-- info: 'SkewRibbonCoarsenings.ribbon_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ribbon_expansion

/-- info: 'SkewRibbonCoarsenings.ribbon_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ribbon_eq_iff

/-- info: 'SkewRibbonCoarsenings.prop_unsigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prop_unsigned

/-- info: 'SkewRibbonCoarsenings.inner_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inner_derivative

/-- info: 'SkewRibbonCoarsenings.normalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normalization

/-- info: 'SkewRibbonCoarsenings.low_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms low_order

/-- info: 'SkewRibbonCoarsenings.labeled_count_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms labeled_count_eq

/-- info: 'SkewRibbonCoarsenings.arithmetic_optimization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arithmetic_optimization

/-- info: 'SkewRibbonCoarsenings.parity_weight_seventeen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parity_weight_seventeen

/-- info: 'SkewRibbonCoarsenings.antichain_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms antichain_cancellation

/-- info: 'SkewRibbonCoarsenings.reversal_suffices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reversal_suffices

/-- info: 'SkewRibbonCoarsenings.Psi_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Psi_G

/-- info: 'SkewRibbonCoarsenings.outer_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms outer_recovery

/-- info: 'SkewRibbonCoarsenings.inner_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inner_recovery

/-- info: 'SkewRibbonCoarsenings.two_factor_cancel_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_factor_cancel_forward

/-- info: 'SkewRibbonCoarsenings.depth_cancel_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms depth_cancel_int

/-- info: 'SkewRibbonCoarsenings.prop_coordinates_automorphism' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prop_coordinates_automorphism

/-- info: 'SkewRibbonCoarsenings.uBound_le_cumDepth'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms uBound_le_cumDepth'

/-- info: 'SkewRibbonCoarsenings.arithBound_le_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arithBound_le_logb

/-- info: 'SkewRibbonCoarsenings.literal_factor_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_factor_iff

/-- info: 'SkewRibbonCoarsenings.color_disconnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms color_disconnected

/-- info: 'SkewRibbonCoarsenings.positive_equilibrium' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms positive_equilibrium

/-- info: 'SkewRibbonCoarsenings.mask_periodic_of_four_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mask_periodic_of_four_vanish

/-- info: 'SkewRibbonCoarsenings.bottom_probes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bottom_probes

/-- info: 'SkewRibbonCoarsenings.selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selection

/-- info: 'SkewRibbonCoarsenings.fiber_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fiber_period

/-- info: 'SkewRibbonCoarsenings.four_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms four_identity

/-- info: 'SkewRibbonCoarsenings.nonlinear_G_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nonlinear_G_combination

/-- info: 'SkewRibbonCoarsenings.odd_characteristic_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_characteristic_prime

/-- info: 'SkewRibbonCoarsenings.exact_scope_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exact_scope_signed

/-- info: 'SkewRibbonCoarsenings.subset_dp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subset_dp

/-- info: 'SkewRibbonCoarsenings.lift_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lift_extraction

/-- info: 'SkewRibbonCoarsenings.class_supset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms class_supset

/-- info: 'SkewRibbonCoarsenings.oldInclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oldInclusion

/-- info: 'SkewRibbonCoarsenings.cor_class_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cor_class_unconditional

/-- info: 'SkewRibbonCoarsenings.prop_normalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prop_normalization

/-- info: 'SkewRibbonCoarsenings.thm_coarse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thm_coarse

/-- info: 'SkewRibbonCoarsenings.prop_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prop_budget

/-- info: 'SkewRibbonCoarsenings.cor_modular_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cor_modular_budget

/-- info: 'SkewRibbonCoarsenings.rem_shallow_induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rem_shallow_induction

end SkewRibbonCoarsenings
