/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.FactorRecovery
import SkewMarkedFactor.PeriodTest
import SkewMarkedFactor.CommonPeriodTransport
import SkewMarkedFactor.SchurPrimitive
import SkewMarkedFactor.RibbonDeletion
import SkewMarkedFactor.TwoRowFormulas
import SkewMarkedFactor.ExampleConsequences
import SkewMarkedFactor.WeightedOperator
import SkewMarkedFactor.MixedTerminal
import SkewMarkedFactor.RibbonNonvanishing
import SkewMarkedFactor.MixedExample
import SkewMarkedFactor.WeightedJacobiTrudi
import SkewMarkedFactor.ModifiedMap
import SkewMarkedFactor.MixedExampleMap
import SkewMarkedFactor.GeneratorSpan
import SkewMarkedFactor.TriangularReadout
import SkewMarkedFactor.JtRotation
import SkewMarkedFactor.WeightedMN
import SkewMarkedFactor.CaseDNorthwest
import SkewMarkedFactor.CaseDRemainder
import SkewMarkedFactor.CaseDWeighted
import SkewMarkedFactor.RowUnions
import SkewMarkedFactor.MixedCovariance
import SkewMarkedFactor.AllTypeNormalization
import SkewMarkedFactor.WeightedHomogeneity
import SkewMarkedFactor.MixedChain
import SkewMarkedFactor.MixedReadout
import SkewMarkedFactor.TwoSidedWeighted
import SkewMarkedFactor.OrdinaryWeighted
import SkewMarkedFactor.Covariance

/-!
# Observed headline axiom footprints

Generated guards for the compiled mathematical assemblies.  Producer modules
are imported directly, never through the public root.
-/

/-- info: 'SkewMarkedFactor.factor_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.factor_recovery

/-- info: 'SkewMarkedFactor.factor_recovery_empty_vertical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.factor_recovery_empty_vertical

/-- info: 'SkewMarkedFactor.period_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.period_test

/-- info: 'SkewMarkedFactor.common_period_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.common_period_transport

/-- info: 'SkewMarkedFactor.two_row_common_period_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.two_row_common_period_transport

/-- info: 'SkewMarkedFactor.coefficient_one_minimum_cell_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.coefficient_one_minimum_cell_schur

/-- info: 'SkewMarkedFactor.ribbon_deletion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.ribbon_deletion

/-- info: 'SkewMarkedFactor.twoRow_formulas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.twoRow_formulas

/-- info: 'SkewMarkedFactor.example_derivative_tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.example_derivative_tails

/-- info: 'SkewMarkedFactor.example_outer_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.example_outer_readout

/-- info: 'SkewMarkedFactor.gaugeExample_vertical_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.gaugeExample_vertical_readout

/-- info: 'SkewMarkedFactor.mixed_excludes_ordinary_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_excludes_ordinary_multiple

/-- info: 'SkewMarkedFactor.wDeriv_pPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_pPoly

/-- info: 'SkewMarkedFactor.wDeriv_schurInvolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_schurInvolution

/-- info: 'SkewMarkedFactor.mixedOp_hPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedOp_hPos

/-- info: 'SkewMarkedFactor.mixedOp_elem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedOp_elem

/-- info: 'SkewMarkedFactor.mixedOp_iterate_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedOp_iterate_terminal

/-- info: 'SkewMarkedFactor.mixedExampleMark_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedExampleMark_legal

/-- info: 'SkewMarkedFactor.mixedExampleParent_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedExampleParent_schur

/-- info: 'SkewMarkedFactor.mixedExampleMark_normalizers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedExampleMark_normalizers

/-- info: 'SkewMarkedFactor.mixedExample_weighted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedExample_weighted_tail

/-- info: 'SkewMarkedFactor.mixedExample_outer_operators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedExample_outer_operators

/-- info: 'SkewMarkedFactor.wDeriv_jtDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_jtDet

/-- info: 'SkewMarkedFactor.intertwine_of_generators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.intertwine_of_generators

/-- info: 'SkewMarkedFactor.mixedExample_Phi_h2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedExample_Phi_h2

/-- info: 'SkewMarkedFactor.mixedExample_Phi_e2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedExample_Phi_e2

/-- info: 'SkewMarkedFactor.mixedExample_readout_h2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedExample_readout_h2

/-- info: 'SkewMarkedFactor.mixedExample_terminal_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedExample_terminal_quotient

/-- info: 'SkewMarkedFactor.mixedExample_wDeriv_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedExample_wDeriv_inner

/-- info: 'SkewMarkedFactor.wDeriv_cellSchur_of_span_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_cellSchur_of_span_le

/-- info: 'SkewMarkedFactor.wDeriv_normalizers_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_normalizers_eq_zero

/-- info: 'SkewMarkedFactor.word_pProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.word_pProd

/-- info: 'SkewMarkedFactor.readout_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.readout_injective

/-- info: 'SkewMarkedFactor.minContent_rowMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.minContent_rowMove

/-- info: 'SkewMarkedFactor.sum_column_moves_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.sum_column_moves_weighted

/-- info: 'SkewMarkedFactor.wDeriv_cellSchur_of_rowMoveSum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_cellSchur_of_rowMoveSum_eq_zero

/-- info: 'SkewMarkedFactor.rowMoveSum_eq_zero_of_terms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowMoveSum_eq_zero_of_terms

/-- info: 'SkewMarkedFactor.sum_column_moves_unweighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.sum_column_moves_unweighted

/-- info: 'SkewMarkedFactor.ribbon_powerSumSpecialize_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.ribbon_powerSumSpecialize_ne_zero

/-- info: 'SkewMarkedFactor.diagLo_rowPower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.diagLo_rowPower

/-- info: 'SkewMarkedFactor.nwBit_rowPower_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.nwBit_rowPower_pos

/-- info: 'SkewMarkedFactor.nwBit_rowPower_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.nwBit_rowPower_zero

/-- info: 'SkewMarkedFactor.rowPower_nw_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_nw_word

/-- info: 'SkewMarkedFactor.rowPower_nw_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_nw_start

/-- info: 'SkewMarkedFactor.rowPower_leftRibbons_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_leftRibbons_subset

/-- info: 'SkewMarkedFactor.rowPower_ribbonSum_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_ribbonSum_zero

/-- info: 'SkewMarkedFactor.rowPower_weighted_ribbonSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_weighted_ribbonSum

/-- info: 'SkewMarkedFactor.rowMove_sum_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowMove_sum_rotate

/-- info: 'SkewMarkedFactor.rowMoveSum_eq_zero_of_rightRibbons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowMoveSum_eq_zero_of_rightRibbons

/-- info: 'SkewMarkedFactor.wDeriv_rowPower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_rowPower

/-- info: 'SkewMarkedFactor.mem_hatMiddleFin_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mem_hatMiddleFin_cell

/-- info: 'SkewMarkedFactor.mem_hatMarkFin_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mem_hatMarkFin_cell

/-- info: 'SkewMarkedFactor.mem_rowPower_cell'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mem_rowPower_cell'

/-- info: 'SkewMarkedFactor.rowPower_strip_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_strip_eq

/-- info: 'SkewMarkedFactor.rowPower_strip_cellSchur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_strip_cellSchur

/-- info: 'SkewMarkedFactor.rowPower_strip_height' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_strip_height

/-- info: 'SkewMarkedFactor.rowPower_strip_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_strip_sign

/-- info: 'SkewMarkedFactor.rowPower_strip_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_strip_signed

/-- info: 'SkewMarkedFactor.mixed_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_covariance

/-- info: 'SkewMarkedFactor.mixed_covariance_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_covariance_d

/-- info: 'SkewMarkedFactor.mixed_generator_intertwining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_generator_intertwining

/-- info: 'SkewMarkedFactor.wDeriv_period_inner_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_period_inner_mixed

/-- info: 'SkewMarkedFactor.wDeriv_rowComposite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_rowComposite

/-- info: 'SkewMarkedFactor.rowPower_segment_mem_leftRibbons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.rowPower_segment_mem_leftRibbons

/-- info: 'SkewMarkedFactor.compositionMap_cellSchur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.compositionMap_cellSchur

/-- info: 'SkewMarkedFactor.compositionMap_cellSchur_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.compositionMap_cellSchur_ordinary

/-- info: 'SkewMarkedFactor.compositionMap_cellSchur_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.compositionMap_cellSchur_c

/-- info: 'SkewMarkedFactor.compositionMap_cellSchur_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.compositionMap_cellSchur_d

/-- info: 'SkewMarkedFactor.algHom_cellSchur_eq_of_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.algHom_cellSchur_eq_of_kernel

/-- info: 'SkewMarkedFactor.wDeriv_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_homogeneous

/-- info: 'SkewMarkedFactor.mixedWord_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixedWord_homogeneous

/-- info: 'SkewMarkedFactor.weighted_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.weighted_chain

/-- info: 'SkewMarkedFactor.mixed_terminal_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_terminal_data

/-- info: 'SkewMarkedFactor.mixed_terminal_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_terminal_readout

/-- info: 'SkewMarkedFactor.mixed_terminal_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_terminal_evaluation

/-- info: 'SkewMarkedFactor.mixed_inner_readout_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_inner_readout_general

/-- info: 'SkewMarkedFactor.mixed_factor_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_factor_recovery

/-- info: 'SkewMarkedFactor.outer_proportional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.outer_proportional

/-- info: 'SkewMarkedFactor.phase_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.phase_unique

/-- info: 'SkewMarkedFactor.wDeriv_cellSchur_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_cellSchur_skew

/-- info: 'SkewMarkedFactor.wDeriv_cellSchur_young' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_cellSchur_young

/-- info: 'SkewMarkedFactor.wDeriv_rowComposite_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_rowComposite_a

/-- info: 'SkewMarkedFactor.ordinary_hall_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.ordinary_hall_covariance

/-- info: 'SkewMarkedFactor.ordinary_weighted_covariance_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.ordinary_weighted_covariance_a

/-- info: 'SkewMarkedFactor.compositionMap_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.compositionMap_anti

/-- info: 'SkewMarkedFactor.readout_hall_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.readout_hall_covariance

/-- info: 'SkewMarkedFactor.readout_weighted_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.readout_weighted_covariance

/-- info: 'SkewMarkedFactor.wDeriv_period_inner_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.wDeriv_period_inner_ordinary

/-- info: 'SkewMarkedFactor.ordTheta_eq_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.ordTheta_eq_phases

/-- info: 'SkewMarkedFactor.ordTheta_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.ordTheta_bound

/-- info: 'SkewMarkedFactor.mixed_hall_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_hall_zero

/-- info: 'SkewMarkedFactor.readoutMap_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.readoutMap_outer

/-- info: 'SkewMarkedFactor.ordinary_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.ordinary_covariance

/-- info: 'SkewMarkedFactor.mixed_covariance_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.mixed_covariance_full

/-- info: 'SkewMarkedFactor.cellSchur_rowUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.cellSchur_rowUnion

/-- info: 'SkewMarkedFactor.intertwine_of_generators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewMarkedFactor.intertwine_of_generators
