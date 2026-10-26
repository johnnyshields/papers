/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.NoBackflowMargin
import SkewSchurReconstruction.MonomialPrefix
import SkewSchurReconstruction.ValuedMonge
import SkewSchurReconstruction.PassiveTail
import SkewSchurReconstruction.CaterpillarMinors
import SkewSchurReconstruction.ElbowWitness
import SkewSchurReconstruction.TwoCapExclusion
import SkewSchurReconstruction.ShiftedFloor
import SkewSchurReconstruction.MongeInitialCoefficients
import SkewSchurReconstruction.LocusFamily
import SkewSchurReconstruction.MajorizationWitnesses
import SkewSchurReconstruction.AbstractFamilyWitness
import SkewSchurReconstruction.FactorwiseCensus
import SkewSchurReconstruction.ScopeWitnesses
import SkewSchurReconstruction.StaircasePairCount
import SkewSchurReconstruction.StaircaseBoundary
import SkewSchurReconstruction.RadixSeparation
import SkewSchurReconstruction.StaircaseBoundaryWitness

/-!
# Headline axiom footprints

These guards pin the observed kernel footprints of the manuscript results.
The module imports their minimal producer cover directly to avoid a reexport cycle.
-/

/-- info: 'SkewSchurReconstruction.Diagram.boundary_reconstruction_deletion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.boundary_reconstruction_deletion

/-- info: 'SkewSchurReconstruction.Diagram.boundary_reconstruction_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.boundary_reconstruction_extension

/-- info: 'SkewSchurReconstruction.Diagram.two_positive_extensions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.two_positive_extensions

/-- info: 'SkewSchurReconstruction.monge_minor_initialForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.monge_minor_initialForm

/-- info: 'SkewSchurReconstruction.Diagram.cofactor_initialForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.cofactor_initialForm

/-- info: 'SkewSchurReconstruction.Diagram.parentAction_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.parentAction_recurrence

/-- info: 'SkewSchurReconstruction.Diagram.parentAction_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.parentAction_zero

/-- info: 'SkewSchurReconstruction.Diagram.rowLength_cofactor_scalar_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.rowLength_cofactor_scalar_recovery

/-- info: 'SkewSchurReconstruction.Diagram.parentAction_synchronized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.parentAction_synchronized

/-- info: 'SkewSchurReconstruction.Diagram.first_split_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.first_split_anchor

/-- info: 'SkewSchurReconstruction.Diagram.defect_no_backflow_square_margin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.defect_no_backflow_square_margin

/-- info: 'SkewSchurReconstruction.Diagram.cap_fixed_minimizers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.cap_fixed_minimizers

/-- info: 'SkewSchurReconstruction.Diagram.equal_pair_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.equal_pair_rigidity

/-- info: 'SkewSchurReconstruction.Diagram.cap_fixed_monomial_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.cap_fixed_monomial_prefix

/-- info: 'SkewSchurReconstruction.terminal_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.terminal_gap

/-- info: 'SkewSchurReconstruction.Diagram.gridDefect_terminal_of_top_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.gridDefect_terminal_of_top_lt

/-- info: 'SkewSchurReconstruction.Diagram.ratioIdentity_fixes_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.ratioIdentity_fixes_cap

/-- info: 'SkewSchurReconstruction.Diagram.ratio_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.ratio_rigidity

/-- info: 'SkewSchurReconstruction.Diagram.ratio_square_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.ratio_square_gap

/-- info: 'SkewSchurReconstruction.Diagram.ratio_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.ratio_floor

/-- info: 'SkewSchurReconstruction.caterpillar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.caterpillar

/-- info: 'SkewSchurReconstruction.Diagram.cap_fixed_boundary_response' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.cap_fixed_boundary_response

/-- info: 'SkewSchurReconstruction.Diagram.cap_fixed_ratio_response' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.cap_fixed_ratio_response

/-- info: 'SkewSchurReconstruction.elbowVector_ratioIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.elbowVector_ratioIdentity

/-- info: 'SkewSchurReconstruction.elbowWitness_actions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.elbowWitness_actions

/-- info: 'SkewSchurReconstruction.Diagram.first_split_majorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.first_split_majorization

/-- info: 'SkewSchurReconstruction.Diagram.cap_fixed_comparability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.cap_fixed_comparability

/-- info: 'SkewSchurReconstruction.ValuedMongeFamily.abstract_monge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.ValuedMongeFamily.abstract_monge

/-- info: 'SkewSchurReconstruction.Diagram.passive_tail_both_passive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.passive_tail_both_passive

/-- info: 'SkewSchurReconstruction.Diagram.passive_tail_block_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.passive_tail_block_factorization

/-- info: 'SkewSchurReconstruction.Diagram.two_cap_exclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.two_cap_exclusion

/-- info: 'SkewSchurReconstruction.Diagram.ratio_floor_supplies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.ratio_floor_supplies

/-- info: 'SkewSchurReconstruction.Diagram.double_cap_kills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.double_cap_kills

/-- info: 'SkewSchurReconstruction.Diagram.unique_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.unique_ratio

/-- info: 'SkewSchurReconstruction.TwoSeries.wordMatrix_det_reversal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.TwoSeries.wordMatrix_det_reversal

/-- info: 'SkewSchurReconstruction.TwoSeries.wordMatrix_det_coefficientMinor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.TwoSeries.wordMatrix_det_coefficientMinor

/-- info: 'SkewSchurReconstruction.factorwise_schur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.factorwise_schur_eq

/-- info: 'SkewSchurReconstruction.Diagram.ratio_shifted_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.ratio_shifted_floor

/-- info: 'SkewSchurReconstruction.monge_minor_initial_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.monge_minor_initial_coefficient

/-- info: 'SkewSchurReconstruction.Diagram.translationEquivalent_of_cofactorTuple_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.translationEquivalent_of_cofactorTuple_eq

/-- info: 'SkewSchurReconstruction.staircase_ratioIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.staircase_ratioIdentity

/-- info: 'SkewSchurReconstruction.staircase_schurFunction_ne_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.staircase_schurFunction_ne_reverse

/-- info: 'SkewSchurReconstruction.locusFamily_defect_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.locusFamily_defect_support

/-- info: 'SkewSchurReconstruction.locusFamily_leading_valuations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.locusFamily_leading_valuations

/-- info: 'SkewSchurReconstruction.locusFamily_floor_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.locusFamily_floor_gap

/-- info: 'SkewSchurReconstruction.locusFamily_positive_support_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.locusFamily_positive_support_card

/-- info: 'SkewSchurReconstruction.Diagram.one_extension_insufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.one_extension_insufficient

/-- info: 'SkewSchurReconstruction.Diagram.equalChain_square_actions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.equalChain_square_actions

/-- info: 'SkewSchurReconstruction.formalTerminalVector_not_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.formalTerminalVector_not_actual

/-- info: 'SkewSchurReconstruction.Diagram.higherStratum_weight_forty_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.higherStratum_weight_forty_three

/-- info: 'SkewSchurReconstruction.movingCap_actual_peels_incomparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.movingCap_actual_peels_incomparable

/-- info: 'SkewSchurReconstruction.abstractFamily_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.abstractFamily_witness

/-- info: 'SkewSchurReconstruction.abstractFamily_no_common_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.abstractFamily_no_common_sampling

/-- info: 'SkewSchurReconstruction.factorwise_census_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.factorwise_census_minimal

/-- info: 'SkewSchurReconstruction.factorwise_census_four_at_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.factorwise_census_four_at_nine

/-- info: 'SkewSchurReconstruction.nonpalindromic_reversal_pairs_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.nonpalindromic_reversal_pairs_card

/-- info: 'SkewSchurReconstruction.Diagram.cofactor_radixCollapse_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.cofactor_radixCollapse_eq_iff

/-- info: 'SkewSchurReconstruction.Diagram.floorMargin_gap_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.floorMargin_gap_unbounded

/-- info: 'SkewSchurReconstruction.Diagram.fingerprint_not_equality_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.Diagram.fingerprint_not_equality_certificate

/-- info: 'SkewSchurReconstruction.staircase_boundary_three_ratio_exclusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.staircase_boundary_three_ratio_exclusion

/-- info: 'SkewSchurReconstruction.endpointThreeWitness_residual_initialForm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.endpointThreeWitness_residual_initialForm

/-- info: 'SkewSchurReconstruction.cap_shift_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewSchurReconstruction.cap_shift_square
