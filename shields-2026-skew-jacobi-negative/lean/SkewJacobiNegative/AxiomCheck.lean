/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.NegativeInvariants
import SkewJacobiNegative.MinimumRowInvariant
import SkewJacobiNegative.GammaEncoding
import SkewJacobiNegative.FullBoardReadings
import SkewJacobiNegative.SmallRowRigidity
import SkewJacobiNegative.ConnectedBorderRigidity
import SkewJacobiNegative.ContactQuadraticOperator
import SkewJacobiNegative.HomogeneousIrreducibility
import SkewJacobiNegative.SaturatedColumnGeometry
import SkewJacobiNegative.ThreeVariableRatio
import SkewJacobiNegative.LowNegativeRigidity
import SkewJacobiNegative.EndpointLeaders
import SkewJacobiNegative.StaircasePrimitives
import SkewJacobiNegative.AlternantRatioBridge
import SkewJacobiNegative.SingletonLift
import SkewJacobiNegative.StaircaseSafeCuts
import SkewJacobiNegative.NegativePartitionExample
import SkewJacobiNegative.ContentUniqueness
import SkewJacobiNegative.NonDenseResonance
import SkewJacobiNegative.RibbonMinimumSixExample
import SkewJacobiNegative.DenseFourRemainder
import SkewJacobiNegative.DenseThreeComponentPlacements
import SkewJacobiNegative.FiveOpeningComparisons
import SkewJacobiNegative.OneNegativeThreeComponentPlacements
import SkewJacobiNegative.ThreeComponentForms
import SkewJacobiNegative.NegativeThreshold
import SkewJacobiNegative.FiveNegativeClassification
import SkewJacobiNegative.ConstantGapFiveClassification
import SkewJacobiNegative.StaircaseFirstJets
import SkewJacobiNegative.ExceptionalFiveResponses
import SkewJacobiNegative.TenClassification
import SkewJacobiNegative.TenBorderRigidity
import SkewJacobiNegative.SmallNegativeSingletons
import SkewJacobiNegative.SquareDegreeExample
import SkewJacobiNegative.StaircaseCubicMatching
import SkewJacobiNegative.StaircaseQuarticAlgebra
import SkewJacobiNegative.StaircaseSquareInitial
import SkewJacobiNegative.StaircaseDeletedRowInitial
import SkewJacobiNegative.StaircaseQuadraticSwap
import SkewJacobiNegative.StaircaseIntervalSwap
import SkewJacobiNegative.StaircaseNoRowReadings
import SkewJacobiNegative.StaircaseResidualMatching
import SkewJacobiNegative.StaircaseFivePlacements
import SkewJacobiNegative.ClassificationThroughSix
import SkewJacobiNegative.StaircaseContactMinors
import SkewJacobiNegative.StaircaseMixedStratum
import SkewJacobiNegative.NonDenseQuartetBridge
import SkewJacobiNegative.MinimumCutInventory
import SkewJacobiNegative.NonHessenbergJoinExample
import SkewJacobiNegative.SaturatedColumnContext
import SkewJacobiNegative.FourRowClasses
import SkewJacobiNegative.TenCompositionCells
import SkewJacobiNegative.SixNegativePartitions
import SkewJacobiNegative.FiveEndpointLeader
import SkewJacobiNegative.TwoComponentLift
import SkewJacobiNegative.FiveSingletonRigidity
import SkewJacobiNegative.ThreeComponentContexts
import SkewJacobiNegative.LowNegativeShapeDichotomy
import SkewJacobiNegative.SixNegativeMinimum
import SkewJacobiNegative.FourRowBorders
import SkewJacobiNegative.TenNegativeBorders

/-!
# Axiom footprints of the proved negative-count results

Every expected message is generated from the elaborated declarations.
-/

/-- info: 'SkewJacobiNegative.BetaDiagram.negativeCount_eq_of_schur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.negativeCount_eq_of_schur_eq

/-- info: 'SkewJacobiNegative.BetaDiagram.minimumRealizingRows_eq_of_schur_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.minimumRealizingRows_eq_of_schur_eq

/-- info: 'SkewJacobiNegative.minimumRealizingRows_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.minimumRealizingRows_isLeast

/-- info: 'SkewJacobiNegative.BetaDiagram.gamma_schur_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.gamma_schur_encoding

/-- info: 'SkewJacobiNegative.BetaDiagram.gamma_schur_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.gamma_schur_eq_iff

/-- info: 'SkewJacobiNegative.BetaDiagram.gamma_translation_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.gamma_translation_iff

/-- info: 'SkewJacobiNegative.BetaDiagram.gamma_rotation_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.gamma_rotation_iff

/-- info: 'SkewJacobiNegative.BetaDiagram.minimum_ordinary_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.minimum_ordinary_degree

/-- info: 'SkewJacobiNegative.BetaDiagram.zeroFree_of_schur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.zeroFree_of_schur_eq

/-- info: 'SkewJacobiNegative.BetaDiagram.small_rows_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.small_rows_rigidity

/-- info: 'SkewJacobiNegative.BetaDiagram.connected_border_rigidity_same_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.connected_border_rigidity_same_order

/-- info: 'SkewJacobiNegative.BetaDiagram.homSchur_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.homSchur_irreducible

/-- info: 'SkewJacobiNegative.BetaDiagram.homSchur_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.homSchur_eq_iff

/-- info: 'SkewJacobiNegative.BetaDiagram.saturated_column_core_connected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.saturated_column_core_connected

/-- info: 'SkewJacobiNegative.BetaDiagram.maximal_cofactor_nine_inventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.maximal_cofactor_nine_inventory

/-- info: 'SkewJacobiNegative.BetaDiagram.maximal_cofactor_ten_inventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.maximal_cofactor_ten_inventory

/-- info: 'SkewJacobiNegative.ContactQuadraticOperator.contact_blind_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.ContactQuadraticOperator.contact_blind_injective

/-- info: 'SkewJacobiNegative.ContactQuadraticOperator.strict_boundary_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.ContactQuadraticOperator.strict_boundary_counterexample

/-- info: 'SkewJacobiNegative.ThreeVariableRatio.alternant_ratio_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.ThreeVariableRatio.alternant_ratio_injective

/-- info: 'SkewJacobiNegative.BetaDiagram.one_negative_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.one_negative_rigidity

/-- info: 'SkewJacobiNegative.BetaDiagram.one_negative_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.one_negative_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.endpoint_top_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.endpoint_top_dense

/-- info: 'SkewJacobiNegative.BetaDiagram.endpoint_top_one_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.endpoint_top_one_negative

/-- info: 'SkewJacobiNegative.BetaDiagram.endpoint_top_two_negative_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.endpoint_top_two_negative_four

/-- info: 'SkewJacobiNegative.BetaDiagram.endpoint_top_small_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.endpoint_top_small_negative

/-- info: 'SkewJacobiNegative.Staircase.primitive_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.primitive_irreducible

/-- info: 'SkewJacobiNegative.BetaDiagram.threeVariable_endpointDifference_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.threeVariable_endpointDifference_ne_zero

/-- info: 'SkewJacobiNegative.threeSchur_ratio_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.threeSchur_ratio_injective

/-- info: 'SkewJacobiNegative.BetaDiagram.singletonContext_rotationRigid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.singletonContext_rotationRigid

/-- info: 'SkewJacobiNegative.BetaDiagram.singletonContext_rotationRigid_of_dense' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.singletonContext_rotationRigid_of_dense

/-- info: 'SkewJacobiNegative.Staircase.minimum_cut_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.minimum_cut_product

/-- info: 'SkewJacobiNegative.Staircase.minimum_highest_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.minimum_highest_layer

/-- info: 'SkewJacobiNegative.Staircase.minimum_degree_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.minimum_degree_exact

/-- info: 'SkewJacobiNegative.Staircase.erase_restriction_at_gap_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.erase_restriction_at_gap_ne_zero

/-- info: 'SkewJacobiNegative.BetaDiagram.connected_border_endpoint_isolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.connected_border_endpoint_isolation

/-- info: 'SkewJacobiNegative.NegativePartitionExample.negative_partition_not_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.NegativePartitionExample.negative_partition_not_invariant

/-- info: 'SkewJacobiNegative.NonDenseResonance.resonance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.NonDenseResonance.resonance

/-- info: 'SkewJacobiNegative.NonDenseResonance.fixed_leader_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.NonDenseResonance.fixed_leader_coefficient

/-- info: 'SkewJacobiNegative.NonDenseResonance.lower_remainder_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.NonDenseResonance.lower_remainder_ne_zero

/-- info: 'SkewJacobiNegative.NonDenseResonance.corner_actual_singletons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.NonDenseResonance.corner_actual_singletons

/-- info: 'SkewJacobiNegative.RibbonMinimumSixExample.schur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.RibbonMinimumSixExample.schur_eq

/-- info: 'SkewJacobiNegative.RibbonMinimumSixExample.different_rotation_orbits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.RibbonMinimumSixExample.different_rotation_orbits

/-- info: 'SkewJacobiNegative.RibbonMinimumSixExample.outside_minimum_seven' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.RibbonMinimumSixExample.outside_minimum_seven

/-- info: 'SkewJacobiNegative.Staircase.staircase_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.staircase_content

/-- info: 'SkewJacobiNegative.Staircase.two_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.two_content

/-- info: 'SkewJacobiNegative.Staircase.three_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.three_content

/-- info: 'SkewJacobiNegative.Staircase.four_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.four_content

/-- info: 'SkewJacobiNegative.Staircase.staircase_content_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.staircase_content_unique

/-- info: 'SkewJacobiNegative.SixRowBoundary.Parameters.six_row_quartets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.SixRowBoundary.Parameters.six_row_quartets

/-- info: 'SkewJacobiNegative.SixRowBoundary.Parameters.minimum_actual_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.SixRowBoundary.Parameters.minimum_actual_rows

/-- info: 'SkewJacobiNegative.SixRowBoundary.Parameters.source_component_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.SixRowBoundary.Parameters.source_component_rows

/-- info: 'SkewJacobiNegative.SixRowBoundary.Parameters.source_component_lengths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.SixRowBoundary.Parameters.source_component_lengths

/-- info: 'SkewJacobiNegative.SixRowBoundary.Parameters.coreSeven_schur_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.SixRowBoundary.Parameters.coreSeven_schur_eq

/-- info: 'SkewJacobiNegative.NonDenseResonance.quartet_core_rotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.NonDenseResonance.quartet_core_rotation

/-- info: 'SkewJacobiNegative.NonDenseResonance.quartet_corner_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.NonDenseResonance.quartet_corner_coefficient

/-- info: 'SkewJacobiNegative.NonDenseResonance.quartet_component_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.NonDenseResonance.quartet_component_orders

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_four_top_and_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_four_top_and_remainder

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_four_coefficient_specialization_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_four_coefficient_specialization_ne_zero

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_cross_resonance_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_cross_resonance_one

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_cross_resonance_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_cross_resonance_two

/-- info: 'SkewJacobiNegative.Staircase.minimum_cut_inventory_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.minimum_cut_inventory_matching

/-- info: 'SkewJacobiNegative.GeneralHessenberg.schur_join_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.GeneralHessenberg.schur_join_formula

/-- info: 'SkewJacobiNegative.GeneralHessenberg.joining_inequalities' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.GeneralHessenberg.joining_inequalities

/-- info: 'SkewJacobiNegative.NonHessenbergJoinExample.joined_formula_fails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.NonHessenbergJoinExample.joined_formula_fails

/-- info: 'SkewJacobiNegative.BetaDiagram.saturated_column_context_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.saturated_column_context_data

/-- info: 'SkewJacobiNegative.FourRowClasses.four_rows_schur_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FourRowClasses.four_rows_schur_eq_iff

/-- info: 'SkewJacobiNegative.FourRowClasses.four_rows_complete_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FourRowClasses.four_rows_complete_class

/-- info: 'SkewJacobiNegative.FourRowClasses.familyF_arbitrary_full_mate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FourRowClasses.familyF_arbitrary_full_mate

/-- info: 'SkewJacobiNegative.BetaDiagram.four_two_negative_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.four_two_negative_rigidity

/-- info: 'SkewJacobiNegative.TenCells.hypothesis_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenCells.hypothesis_one

/-- info: 'SkewJacobiNegative.TenCells.separated_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenCells.separated_diagonal

/-- info: 'SkewJacobiNegative.TenCells.delete_ne_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenCells.delete_ne_connected

/-- info: 'SkewJacobiNegative.TenCells.delete_sw_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenCells.delete_sw_connected

/-- info: 'SkewJacobiNegative.TenCells.hypothesis_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenCells.hypothesis_four

/-- info: 'SkewJacobiNegative.TenCells.attachment_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenCells.attachment_c

/-- info: 'SkewJacobiNegative.TenCells.outer_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenCells.outer_connected

/-- info: 'SkewJacobiNegative.TenCells.outer_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenCells.outer_proper

/-- info: 'SkewJacobiNegative.TenCells.compositionC_eq_betaCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenCells.compositionC_eq_betaCells

/-- info: 'SkewJacobiNegative.self_conjugate_six_eq_staircase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.self_conjugate_six_eq_staircase

/-- info: 'SkewJacobiNegative.BetaDiagram.six_partition_low_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.six_partition_low_minimum

/-- info: 'SkewJacobiNegative.BetaDiagram.symmetric_negative_partition_self_conjugate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.symmetric_negative_partition_self_conjugate

/-- info: 'SkewJacobiNegative.BetaDiagram.six_negative_minimum_not_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.six_negative_minimum_not_symmetric

/-- info: 'SkewJacobiNegative.BetaDiagram.endpointLeader_five_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.endpointLeader_five_negative

/-- info: 'SkewJacobiNegative.FiveEndpoint.CriticalData.diagram_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveEndpoint.CriticalData.diagram_leader

/-- info: 'SkewJacobiNegative.FiveEndpoint.CriticalData.shifted_determinant_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveEndpoint.CriticalData.shifted_determinant_difference

/-- info: 'SkewJacobiNegative.BetaDiagram.twoComponentContext_rotationRigid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.twoComponentContext_rotationRigid

/-- info: 'SkewJacobiNegative.BetaDiagram.twoComponentContext_rotationRigid_of_dense' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.twoComponentContext_rotationRigid_of_dense

/-- info: 'SkewJacobiNegative.BetaDiagram.singleton_five_rotationRigid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.singleton_five_rotationRigid

/-- info: 'SkewJacobiNegative.BetaDiagram.singleton_five_first_cut_rigidity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.singleton_five_first_cut_rigidity

/-- info: 'SkewJacobiNegative.BetaDiagram.threeEndContext_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.threeEndContext_schur

/-- info: 'SkewJacobiNegative.BetaDiagram.threeMiddleContext_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.threeMiddleContext_schur

/-- info: 'SkewJacobiNegative.BetaDiagram.three_cuts_of_factor_inventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.three_cuts_of_factor_inventory

/-- info: 'SkewJacobiNegative.BetaDiagram.two_negative_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.two_negative_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.column_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.column_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.square_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.square_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.hook_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.hook_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.small_negative_shape_dichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.small_negative_shape_dichotomy

/-- info: 'SkewJacobiNegative.BetaDiagram.saturated_column_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.saturated_column_rigidity

/-- info: 'SkewJacobiNegative.BetaDiagram.saturated_column_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.saturated_column_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.six_negative_minimum_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.six_negative_minimum_classification

/-- info: 'SkewJacobiNegative.BetaDiagram.six_negative_minimum_full_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.six_negative_minimum_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.low_negative_complete_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.low_negative_complete_class

/-- info: 'SkewJacobiNegative.BetaDiagram.three_negative_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.three_negative_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.small_negative_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.small_negative_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.three_corners_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.three_corners_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.small_negative_endpoint_rigidity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.small_negative_endpoint_rigidity

/-- info: 'SkewJacobiNegative.BetaDiagram.four_endpoint_equality_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.four_endpoint_equality_symmetric

/-- info: 'SkewJacobiNegative.FourRowBorders.four_border_exclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FourRowBorders.four_border_exclusion

/-- info: 'SkewJacobiNegative.TenParameters.universalBorder_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.universalBorder_separator

/-- info: 'SkewJacobiNegative.TenParameters.tiedBorder_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.tiedBorder_separator

/-- info: 'SkewJacobiNegative.TenParameters.tiedBorder_schur_ne_including_units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.tiedBorder_schur_ne_including_units

/-- info: 'SkewJacobiNegative.TenParameters.endpoint_not_translation_exceptional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.endpoint_not_translation_exceptional

/-- info: 'SkewJacobiNegative.TenParameters.endpoint_not_rotation_exceptional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.endpoint_not_rotation_exceptional

/-- info: 'SkewJacobiNegative.TenParameters.exceptional_endpoint_ne_including_units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.exceptional_endpoint_ne_including_units

/-- info: 'SkewJacobiNegative.TenParameters.gamma_tiedBorder_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.gamma_tiedBorder_schur

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_three_context_arbitrary_mate_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_three_context_arbitrary_mate_recovery

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_threeEndContext_orientation_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_threeEndContext_orientation_ne

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_threeMiddleContext_orientation_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_threeMiddleContext_orientation_ne

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_threeComponentU_negativeCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_threeComponentU_negativeCount

/-- info: 'SkewJacobiNegative.FiveNegative.five_base_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveNegative.five_base_pair

/-- info: 'SkewJacobiNegative.FiveNegative.five_base_complete_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveNegative.five_base_complete_class

/-- info: 'SkewJacobiNegative.FiveNegative.same_opening_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveNegative.same_opening_rigidity

/-- info: 'SkewJacobiNegative.FiveNegative.exceptional_member_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveNegative.exceptional_member_unique

/-- info: 'SkewJacobiNegative.BetaDiagram.fourPlacementSource_context_rotationRigid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.fourPlacementSource_context_rotationRigid

/-- info: 'SkewJacobiNegative.BetaDiagram.three_component_cofactor_rotationRigid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.three_component_cofactor_rotationRigid

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_threeEndContext_rotationRigid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_threeEndContext_rotationRigid

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_threeMiddleContext_rotationRigid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_threeMiddleContext_rotationRigid

/-- info: 'SkewJacobiNegative.BetaDiagram.one_negative_threeEndContext_rotationRigid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.one_negative_threeEndContext_rotationRigid

/-- info: 'SkewJacobiNegative.BetaDiagram.one_negative_threeMiddleContext_rotationRigid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.one_negative_threeMiddleContext_rotationRigid

/-- info: 'SkewJacobiNegative.BetaDiagram.threeEndContext_literal_aligned_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.threeEndContext_literal_aligned_recovery

/-- info: 'SkewJacobiNegative.BetaDiagram.negative_threshold_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.negative_threshold_rigidity

/-- info: 'SkewJacobiNegative.BetaDiagram.negative_threshold_full_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.negative_threshold_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.ten_negative_high_minimum_rigidity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ten_negative_high_minimum_rigidity

/-- info: 'SkewJacobiNegative.BetaDiagram.ten_negative_high_minimum_full_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ten_negative_high_minimum_full_class

/-- info: 'SkewJacobiNegative.TenParameters.negative_threshold_sharpness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.negative_threshold_sharpness

/-- info: 'SkewJacobiNegative.negative_threshold_sharpness_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.negative_threshold_sharpness_exists

/-- info: 'SkewJacobiNegative.BetaDiagram.dense_three_component_source_forms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.dense_three_component_source_forms

/-- info: 'SkewJacobiNegative.BetaDiagram.five_negative_full_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.five_negative_full_classification

/-- info: 'SkewJacobiNegative.BetaDiagram.five_exceptional_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.five_exceptional_full_class

/-- info: 'SkewJacobiNegative.FiveExceptional.five_endpoint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.five_endpoint_iff

/-- info: 'SkewJacobiNegative.FiveExceptional.exceptional_borders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.exceptional_borders

/-- info: 'SkewJacobiNegative.FiveExceptional.universal_border_separator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.universal_border_separator

/-- info: 'SkewJacobiNegative.FiveExceptional.tiedBorder_schur_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.tiedBorder_schur_ne

/-- info: 'SkewJacobiNegative.FiveExceptional.five_higher_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.five_higher_full_class

/-- info: 'SkewJacobiNegative.ConstantGapFiveClassification.constant_gap_full_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.ConstantGapFiveClassification.constant_gap_full_class

/-- info: 'SkewJacobiNegative.ConstantGapFiveClassification.ribbon_five_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.ConstantGapFiveClassification.ribbon_five_classification

/-- info: 'SkewJacobiNegative.ConstantGapFiveClassification.endpoint_reading' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.ConstantGapFiveClassification.endpoint_reading

/-- info: 'SkewJacobiNegative.Staircase.staircase_first_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.staircase_first_jet

/-- info: 'SkewJacobiNegative.Staircase.minimumPolynomial_coeff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.minimumPolynomial_coeff_one

/-- info: 'SkewJacobiNegative.Staircase.four_marked_coeff_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.four_marked_coeff_two

/-- info: 'SkewJacobiNegative.Staircase.four_marked_coeff_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.four_marked_coeff_three

/-- info: 'SkewJacobiNegative.FiveExceptional.response_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.response_table

/-- info: 'SkewJacobiNegative.FiveExceptional.coreCandidate_endpoint_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.coreCandidate_endpoint_separation

/-- info: 'SkewJacobiNegative.FiveExceptional.response_double_top_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.response_double_top_ne_zero

/-- info: 'SkewJacobiNegative.BetaDiagram.ten_seven_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ten_seven_classification

/-- info: 'SkewJacobiNegative.BetaDiagram.ten_exceptional_gamma_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ten_exceptional_gamma_iff

/-- info: 'SkewJacobiNegative.BetaDiagram.ten_complete_exceptional_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ten_complete_exceptional_class

/-- info: 'SkewJacobiNegative.FiveExceptional.four_core_context_equality_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.four_core_context_equality_iff

/-- info: 'SkewJacobiNegative.FiveExceptional.exceptional_singleton_complete_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.exceptional_singleton_complete_class

/-- info: 'SkewJacobiNegative.FiveExceptional.exceptional_singleton_rotationRigid_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.FiveExceptional.exceptional_singleton_rotationRigid_iff

/-- info: 'SkewJacobiNegative.BetaDiagram.ten_negative_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ten_negative_classification

/-- info: 'SkewJacobiNegative.BetaDiagram.ten_negative_rotationRigid_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ten_negative_rotationRigid_iff

/-- info: 'SkewJacobiNegative.BetaDiagram.ten_higher_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ten_higher_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.ten_seven_endpoint_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ten_seven_endpoint_eq_iff

/-- info: 'SkewJacobiNegative.TenParameters.endpoint_rotationRigid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.endpoint_rotationRigid

/-- info: 'SkewJacobiNegative.TenParameters.cross_orbit_borders_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.cross_orbit_borders_ne

/-- info: 'SkewJacobiNegative.TenParameters.positiveBorder_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.TenParameters.positiveBorder_full_class

/-- info: 'SkewJacobiNegative.BetaDiagram.singletonContext_rotationRigid_of_two_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.singletonContext_rotationRigid_of_two_negative

/-- info: 'SkewJacobiNegative.BetaDiagram.singletonContext_rotationRigid_of_one_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.singletonContext_rotationRigid_of_one_negative

/-- info: 'SkewJacobiNegative.SquareDegreeExample.corner_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.SquareDegreeExample.corner_factorization

/-- info: 'SkewJacobiNegative.SquareDegreeExample.corner_totalDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.SquareDegreeExample.corner_totalDegree

/-- info: 'SkewJacobiNegative.SquareDegreeExample.corner_layers_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.SquareDegreeExample.corner_layers_nonzero

/-- info: 'SkewJacobiNegative.Staircase.four_nonendpoint_cubic_necessity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.four_nonendpoint_cubic_necessity

/-- info: 'SkewJacobiNegative.Staircase.four_cubic_residual_match_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.four_cubic_residual_match_iff

/-- info: 'SkewJacobiNegative.Staircase.four_endpoint_supported_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.four_endpoint_supported_labels

/-- info: 'SkewJacobiNegative.Staircase.endpoint_unordered_ratio_reading' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.endpoint_unordered_ratio_reading

/-- info: 'SkewJacobiNegative.Staircase.restriction_second_index_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.restriction_second_index_eq

/-- info: 'SkewJacobiNegative.Staircase.four_quartic_signed_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.four_quartic_signed_parts

/-- info: 'SkewJacobiNegative.Staircase.restriction_square_initial_no_row_contact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.restriction_square_initial_no_row_contact

/-- info: 'SkewJacobiNegative.Staircase.restriction_rows_eq_of_no_row_contact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.restriction_rows_eq_of_no_row_contact

/-- info: 'SkewJacobiNegative.Staircase.restriction_middleB_initial_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.restriction_middleB_initial_negative

/-- info: 'SkewJacobiNegative.Staircase.restriction_middleC_initial_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.restriction_middleC_initial_negative

/-- info: 'SkewJacobiNegative.Staircase.restriction_BC_positive_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.restriction_BC_positive_initial

/-- info: 'SkewJacobiNegative.Staircase.barred_quadratic_swap_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.barred_quadratic_swap_key

/-- info: 'SkewJacobiNegative.Staircase.interval_last_swap_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.interval_last_swap_key

/-- info: 'SkewJacobiNegative.Staircase.actual_middle_swap_reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.actual_middle_swap_reading

/-- info: 'SkewJacobiNegative.Staircase.no_row_aligned_interval_reading' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.no_row_aligned_interval_reading

/-- info: 'SkewJacobiNegative.Staircase.no_row_contact_augmentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.no_row_contact_augmentation

/-- info: 'SkewJacobiNegative.Staircase.no_row_contact_status_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.no_row_contact_status_eq

/-- info: 'SkewJacobiNegative.Staircase.middle_row_contact_augmentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.middle_row_contact_augmentation

/-- info: 'SkewJacobiNegative.Staircase.middle_row_contact_status_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.middle_row_contact_status_eq

/-- info: 'SkewJacobiNegative.Staircase.four_quartic_inventory_necessity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.four_quartic_inventory_necessity

/-- info: 'SkewJacobiNegative.Staircase.four_quartic_residual_necessity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.four_quartic_residual_necessity

/-- info: 'SkewJacobiNegative.Staircase.four_quartic_residual_match_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.four_quartic_residual_match_iff

/-- info: 'SkewJacobiNegative.Staircase.staircase_residual_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.Staircase.staircase_residual_matching

/-- info: 'SkewJacobiNegative.StaircaseFivePlacements.thick_five_full_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseFivePlacements.thick_five_full_class

/-- info: 'SkewJacobiNegative.StaircaseFivePlacements.thick_five_scheme_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseFivePlacements.thick_five_scheme_class

/-- info: 'SkewJacobiNegative.StaircaseFivePlacements.Scheme.at_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseFivePlacements.Scheme.at_injective

/-- info: 'SkewJacobiNegative.StaircaseFivePlacements.Scheme.gamma_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseFivePlacements.Scheme.gamma_at

/-- info: 'SkewJacobiNegative.StaircaseFivePlacements.Scheme.ungamma_of_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseFivePlacements.Scheme.ungamma_of_member

/-- info: 'SkewJacobiNegative.StaircaseFivePlacements.Scheme.member_ungamma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseFivePlacements.Scheme.member_ungamma

/-- info: 'SkewJacobiNegative.StaircaseFivePlacements.Scheme.intersection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseFivePlacements.Scheme.intersection

/-- info: 'SkewJacobiNegative.StaircaseFivePlacements.five_endpoint_rotate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseFivePlacements.five_endpoint_rotate

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.staircase_mate_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.staircase_mate_closure

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.zeroFree_endpoint_symmetry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.zeroFree_endpoint_symmetry

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.b_border_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.b_border_separation

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.contact_border_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.contact_border_separation

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.staircase_base_arbitrary_mate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.staircase_base_arbitrary_mate

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.staircase_scheme_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.staircase_scheme_complete

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.staircase_scheme_fiber_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.staircase_scheme_fiber_four

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.staircase_minimum_realizing_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.staircase_minimum_realizing_rows

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.scheme_border_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.scheme_border_separation

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.zeroFree_six_row_rigidity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.zeroFree_six_row_rigidity

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.zeroFree_higher_row_rigidity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.zeroFree_higher_row_rigidity

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.partition_higher_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.partition_higher_rows

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.staircase_partition_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.staircase_partition_base

/-- info: 'SkewJacobiNegative.StaircaseHigherRows.staircase_base_four_upper_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseHigherRows.staircase_base_four_upper_bound

/-- info: 'SkewJacobiNegative.BetaDiagram.classification_through_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.classification_through_six

/-- info: 'SkewJacobiNegative.StaircaseContactMinors.a1F_schur_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseContactMinors.a1F_schur_reduction

/-- info: 'SkewJacobiNegative.StaircaseContactMinors.a1H_schur_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseContactMinors.a1H_schur_reduction

/-- info: 'SkewJacobiNegative.StaircaseContactMinors.a2F_schur_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseContactMinors.a2F_schur_reduction

/-- info: 'SkewJacobiNegative.StaircaseContactMinors.a2H_schur_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseContactMinors.a2H_schur_reduction

/-- info: 'SkewJacobiNegative.StaircaseContactMinors.toeplitz_submatrices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseContactMinors.toeplitz_submatrices

/-- info: 'SkewJacobiNegative.StaircaseContactMinors.contact_minor_correspondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseContactMinors.contact_minor_correspondence

/-- info: 'SkewJacobiNegative.StaircaseContactMinors.contact_coefficients_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseContactMinors.contact_coefficients_unique

/-- info: 'SkewJacobiNegative.StaircaseContactMinors.contact_localization_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseContactMinors.contact_localization_injective

/-- info: 'SkewJacobiNegative.StaircaseMixedStratum.mixed_stratum_example' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.StaircaseMixedStratum.mixed_stratum_example
