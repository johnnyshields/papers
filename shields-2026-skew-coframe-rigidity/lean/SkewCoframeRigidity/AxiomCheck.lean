/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.ClippedOperator
import SkewCoframeRigidity.RowDegree
import SkewCoframeRigidity.RowDegreeCoherent
import SkewCoframeRigidity.RowDegreeFractionField
import SkewCoframeRigidity.SpliceExample
import SkewCoframeRigidity.Coframe.CoequalData
import SkewCoframeRigidity.CapRecognition
import SkewCoframeRigidity.FixedCap
import SkewCoframeRigidity.UnitRestoration.Linearized
import SkewCoframeRigidity.UnitRestoration.SpliceNonzeroMain
import SkewCoframeRigidity.UnitRestoration.AdjugateOrderMain
import SkewCoframeRigidity.UnitRestoration.AdjugateSharp
import SkewCoframeRigidity.UnitRestoration.ZeroFree
import SkewCoframeRigidity.Stationary
import SkewCoframeRigidity.Unshifted

/-!
# Axiom regression guard

Pins the axiom footprint of each headline result to Lean's three standard axioms.
-/



/-- info: 'SkewCoframeRigidity.clippedOp_X_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.clippedOp_X_mul

/-- info: 'SkewCoframeRigidity.BetaDiagram.rowDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.BetaDiagram.rowDegree

/-- info: 'SkewCoframeRigidity.BetaDiagram.connected_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.BetaDiagram.connected_irreducible

/-- info: 'SkewCoframeRigidity.hooks_schur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.hooks_schur_eq

/-- info: 'SkewCoframeRigidity.cellSplice_schur_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.cellSplice_schur_ne

/-- info: 'SkewCoframeRigidity.Coframe.atlasCoords_algebraicIndependent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.atlasCoords_algebraicIndependent

/-- info: 'SkewCoframeRigidity.Coframe.coframe_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.coframe_irreducible

/-- info: 'SkewCoframeRigidity.Coframe.eq_of_coframe_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.eq_of_coframe_eq

/-- info: 'SkewCoframeRigidity.Coframe.coequal_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.coequal_data

/-- info: 'SkewCoframeRigidity.Coframe.coequal_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.coequal_distinct

/-- info: 'SkewCoframeRigidity.CapRecognition.WeakCap.numerator_irreducible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.CapRecognition.WeakCap.numerator_irreducible

/-- info: 'SkewCoframeRigidity.CapRecognition.WeakCap.ratio_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.CapRecognition.WeakCap.ratio_injective

/-- info: 'SkewCoframeRigidity.FixedCap.fixed_cap_rigidity_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.FixedCap.fixed_cap_rigidity_unconditional

/-- info: 'SkewCoframeRigidity.FixedCap.schurOf_splice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.FixedCap.schurOf_splice

/-- info: 'SkewCoframeRigidity.Coframe.finite_injectivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.finite_injectivity

/-- info: 'SkewCoframeRigidity.Coframe.finite_injectivity_unitFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.finite_injectivity_unitFree

/-- info: 'SkewCoframeRigidity.UnitRestoration.coequal_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.UnitRestoration.coequal_core

/-- info: 'SkewCoframeRigidity.UnitRestoration.linearized_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.UnitRestoration.linearized_cap

/-- info: 'SkewCoframeRigidity.UnitRestoration.splice_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.UnitRestoration.splice_nonzero

/-- info: 'SkewCoframeRigidity.Coframe.component_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.component_remainder

/-- info: 'SkewCoframeRigidity.Coframe.top_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.top_support

/-- info: 'SkewCoframeRigidity.Coframe.top_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.top_matching

/-- info: 'SkewCoframeRigidity.Coframe.positive_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.positive_power

/-- info: 'SkewCoframeRigidity.Coframe.hooks_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.hooks_defect

/-- info: 'SkewCoframeRigidity.Coframe.stationary_field_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.stationary_field_descent

/-- info: 'SkewCoframeRigidity.Unshifted.unshifted_exclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Unshifted.unshifted_exclusion

/-- info: 'SkewCoframeRigidity.Coframe.cohSchur_posRowDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.cohSchur_posRowDegree

/-- info: 'SkewCoframeRigidity.Coframe.not_theta_dvd_cohSchur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.not_theta_dvd_cohSchur

/-- info: 'SkewCoframeRigidity.Coframe.cohSchur_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.cohSchur_irreducible

/-- info: 'SkewCoframeRigidity.Coframe.cohSchur_isRelPrime_cohCorner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.cohSchur_isRelPrime_cohCorner

/-- info: 'SkewCoframeRigidity.Coframe.cohSchur_eq_of_schur_eq'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.cohSchur_eq_of_schur_eq'

/-- info: 'SkewCoframeRigidity.UnitRestoration.adjugate_difference_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.UnitRestoration.adjugate_difference_order

/-- info: 'SkewCoframeRigidity.UnitRestoration.contraction_order_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.UnitRestoration.contraction_order_ge

/-- info: 'SkewCoframeRigidity.Coframe.irreducible_map_of_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.irreducible_map_of_primitive

/-- info: 'SkewCoframeRigidity.Coframe.dvd_of_map_dvd_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.dvd_of_map_dvd_map

/-- info: 'SkewCoframeRigidity.Coframe.cohSchur_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.cohSchur_primitive

/-- info: 'SkewCoframeRigidity.Coframe.cohSchurFrac_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.cohSchurFrac_irreducible

/-- info: 'SkewCoframeRigidity.Coframe.cohSchurFrac_isRelPrime_cohCornerFrac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.Coframe.cohSchurFrac_isRelPrime_cohCornerFrac

/-- info: 'SkewCoframeRigidity.UnitRestoration.adjDifference_unit_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.UnitRestoration.adjDifference_unit_exact

/-- info: 'SkewCoframeRigidity.UnitRestoration.adjDifference_core_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.UnitRestoration.adjDifference_core_exact

/-- info: 'SkewCoframeRigidity.UnitRestoration.adjDifference_self_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.UnitRestoration.adjDifference_self_exact

/-- info: 'SkewCoframeRigidity.UnitRestoration.contraction_unit_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.UnitRestoration.contraction_unit_exact

/-- info: 'SkewCoframeRigidity.UnitRestoration.contraction_core_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCoframeRigidity.UnitRestoration.contraction_core_exact
