/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewCornerDescent.Matrix.Witnesses
import SkewCornerDescent.Matrix.CornerCofactor
import SkewCornerDescent.Matrix.GeneratorSpan
import SkewGluing.Composition
import SkewGluing.DiagramSchur
import SkewGluing.InteriorProfile
import SkewGluing.FieldIrreducibility
import SkewGluing.CofactorAssembly
import SkewGluing.CapSchur
import SkewGluing.PeriodicHat
import SkewGluing.EmptyRowErosion
import SkewGluing.RowNormalization
import SkewGluing.TransportCoefficient
import SkewGluing.DiscreteInterior
import SkewCornerDescent.BetaReduction
import SkewCornerDescent.PeriodTests
import SkewGluing.AlphaRowCandidate
import SkewCornerDescent.Matrix.SelectedCoordinate
import SkewCornerDescent.Matrix.SharedCore
import SkewCornerDescent.Matrix.SelectedCommonCore
import SkewCornerDescent.Matrix.OriginalWindowGeometricResidue
import SkewCornerDescent.Matrix.AdjugateMinors
import SkewCornerDescent.Matrix.ComponentInverseVectors
import SkewCornerDescent.CyclicWindows
import SkewCornerDescent.Matrix.ComponentPivot
import SkewCornerDescent.Matrix.ComponentRegularity
import SkewCornerDescent.BinaryTransitions
import SkewCornerDescent.SinglePositive
import SkewCornerDescent.SignedSupportDetector
import SkewCornerDescent.Matrix.ComponentIntervals
import SkewCornerDescent.Matrix.Hessenberg
import SkewCornerDescent.PhaseInventory
import SkewCornerDescent.Matrix.ComponentDenominators
import SkewCornerDescent.Matrix.ProtectedGenerator
import SkewCornerDescent.Matrix.OrderedResponses
import SkewCornerDescent.Matrix.ResidueProtectedGenerator
import SkewCornerDescent.Matrix.ComponentRegularMatrices
import SkewCornerDescent.Matrix.InteriorBlockAxioms
/-!
# Axiom footprints for original matrix and derivative primitives

The guards pin the observed footprints of these primitives in both directions.
-/

/--
info: 'SkewCornerDescent.Matrix.entryDeriv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.entryDeriv

/--
info: 'SkewCornerDescent.Matrix.entryDeriv_add' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.entryDeriv_add

/--
info: 'SkewCornerDescent.Matrix.entryDeriv_sub' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.entryDeriv_sub

/--
info: 'SkewCornerDescent.Matrix.entryDeriv_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.entryDeriv_one

/--
info: 'SkewCornerDescent.Matrix.entryDeriv_mul' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.entryDeriv_mul

/--
info: 'SkewCornerDescent.Matrix.retainedResponse' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.retainedResponse

/--
info: 'SkewCornerDescent.Matrix.det_eq_removed_mul_response' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.det_eq_removed_mul_response

/--
info: 'SkewCornerDescent.Matrix.entryDeriv_invOf' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.entryDeriv_invOf

/--
info: 'SkewCornerDescent.Matrix.entryDeriv_retainedResponse' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.entryDeriv_retainedResponse

/--
info: 'SkewCornerDescent.Matrix.actualField' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualField

/--
info: 'SkewCornerDescent.Matrix.originalMap' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalMap

/--
info: 'SkewCornerDescent.Matrix.originalMap_injective' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalMap_injective

/--
info: 'SkewCornerDescent.Matrix.originalMap_eq_zero' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalMap_eq_zero

/--
info: 'SkewCornerDescent.Matrix.polynomialJet' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.polynomialJet

/--
info: 'SkewCornerDescent.Matrix.rationalJet' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.rationalJet

/--
info: 'SkewCornerDescent.Matrix.rationalJet_originalMap' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.rationalJet_originalMap

/--
info: 'SkewCornerDescent.Matrix.rationalJet_fst' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.rationalJet_fst

/--
info: 'SkewCornerDescent.Matrix.rationalJetAlgHom' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.rationalJetAlgHom

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_originalMap' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_originalMap

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_X' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_X

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_hh' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_hh

/--
info: 'SkewCornerDescent.Matrix.originalMatrix' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalMatrix

/--
info: 'SkewCornerDescent.Matrix.det_originalMatrix' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.det_originalMatrix

/--
info: 'SkewCornerDescent.Matrix.splitOriginalMatrix' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.splitOriginalMatrix

/--
info: 'SkewCornerDescent.Matrix.det_splitOriginalMatrix' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.det_splitOriginalMatrix

/--
info: 'SkewCornerDescent.Matrix.original_det_eq_removed_mul_response' depends on axioms:
[propext,  Classical.choice,  Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.original_det_eq_removed_mul_response

/--
info: 'SkewCornerDescent.Matrix.entryDeriv_originalMatrix' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.entryDeriv_originalMatrix

/--
info: 'SkewCornerDescent.Matrix.endpointProfile' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.endpointProfile

/--
info: 'SkewCornerDescent.Matrix.ordinaryEndpointProfile' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.ordinaryEndpointProfile

/--
info: 'SkewCornerDescent.Matrix.toLaurent_ordinaryEndpointProfile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.toLaurent_ordinaryEndpointProfile

/--
info: 'SkewCornerDescent.Matrix.endpointProfile_eq_toLaurent_of_nonneg' depends on axioms:
[propext,  Classical.choice,  Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.endpointProfile_eq_toLaurent_of_nonneg

/--
info: 'SkewCornerDescent.Matrix.endpointProfile_mul_coeff' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.endpointProfile_mul_coeff

/--
info: 'SkewCornerDescent.Matrix.intervalMatrix' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.intervalMatrix

/--
info: 'SkewCornerDescent.Matrix.intervalIncoming' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.intervalIncoming

/--
info: 'SkewCornerDescent.Matrix.intervalOutgoing' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.intervalOutgoing

/--
info: 'SkewCornerDescent.Matrix.intervalResponse' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.intervalResponse

/--
info: 'SkewCornerDescent.Matrix.leftEndpointProfile' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.leftEndpointProfile

/--
info: 'SkewCornerDescent.Matrix.rightEndpointProfile' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.rightEndpointProfile

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_intervalResponse' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_intervalResponse

/--
info: 'SkewCornerDescent.Matrix.affineCoordinate' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.affineCoordinate

/--
info: 'SkewCornerDescent.Matrix.normalDeriv' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.normalDeriv

/--
info: 'SkewCornerDescent.Matrix.fixedNormalDeriv' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.fixedNormalDeriv

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_affineCoordinate' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_affineCoordinate

/--
info: 'SkewCornerDescent.Matrix.normalDeriv_affineCoordinate' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.normalDeriv_affineCoordinate

/--
info: 'SkewCornerDescent.Matrix.fixedNormalDeriv_affineCoordinate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.fixedNormalDeriv_affineCoordinate

/--
info: 'SkewCornerDescent.Matrix.normalDeriv_X_of_ne' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.normalDeriv_X_of_ne

/--
info: 'SkewCornerDescent.Matrix.fixedNormalDeriv_X_of_ne' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.fixedNormalDeriv_X_of_ne

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_eq_fixed_add_normal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_eq_fixed_add_normal

/--
info: 'SkewCornerDescent.Matrix.mul_normalDeriv' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.mul_normalDeriv

/--
info: 'SkewCornerDescent.Matrix.normalDeriv_intervalResponse' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.normalDeriv_intervalResponse

/--
info: 'SkewCornerDescent.Matrix.fixedNormalDeriv_intervalResponse' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.fixedNormalDeriv_intervalResponse

/--
info: 'SkewCornerDescent.Matrix.hook_original_det_ne_zero' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.hook_original_det_ne_zero

/--
info: 'SkewCornerDescent.Matrix.hook_original_det_isUnit' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.hook_original_det_isUnit

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_hook' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_hook

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_hook_inverse_ne_zero' depends on axioms:
[propext,  Classical.choice,  Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_hook_inverse_ne_zero

/--
info: 'SkewCornerDescent.Matrix.h0_pivot_matrix' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.h0_pivot_matrix

/--
info: 'SkewCornerDescent.Matrix.h0_midpoint_response' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.h0_midpoint_response

/--
info: 'SkewCornerDescent.Matrix.h0_midpoint_derivative' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.h0_midpoint_derivative

/--
info: 'SkewCornerDescent.Matrix.fixed_normal_coordinate_witness' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.fixed_normal_coordinate_witness

/--
info: 'SkewCornerDescent.Matrix.tied_nonrow_profiles_not_literal' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.tied_nonrow_profiles_not_literal

/--
info: 'SkewCornerDescent.Matrix.negative_endpoint_profile_not_ordinary' depends on axioms:
[propext,  Classical.choice,  Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.negative_endpoint_profile_not_ordinary

/--
info: 'SkewCornerDescent.Matrix.zero_slope_normal_coordinate' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.zero_slope_normal_coordinate

/--
info: 'SkewCornerDescent.Matrix.entryDeriv_originalMatrix_top' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.entryDeriv_originalMatrix_top

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_originalSchur_top' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_originalSchur_top

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_originalSchur_of_gt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_originalSchur_of_gt

/--
info: 'SkewCornerDescent.Matrix.det_deletedTopRightOriginalMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.det_deletedTopRightOriginalMatrix

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_originalSchur_top_eq_deletedMinor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_originalSchur_top_eq_deletedMinor

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_originalSchur_top_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_originalSchur_top_ne_zero

/--
info: 'SkewCornerDescent.Matrix.polynomialSpan_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.polynomialSpan_mul

/--
info: 'SkewGluing.MarkedInner.span_compose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.span_compose


/--
info: 'SkewGluing.Profile.presentation_sigma_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.Profile.presentation_sigma_unique

/--
info: 'SkewGluing.cellSchur_eq_profile' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.cellSchur_eq_profile

/--
info: 'SkewGluing.connectedSchur_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.connectedSchur_translate

/--
info: 'SkewGluing.irreducible_cellSchur' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.irreducible_cellSchur

/--
info: 'SkewGluing.interior_component_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.interior_component_bounds

/--
info: 'SkewGluing.interior_eq_translate_minorCells' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.interior_eq_translate_minorCells

/--
info: 'SkewGluing.cellSchur_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.cellSchur_translate

/--
info: 'SkewGluing.integralCellSchur_primitive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.integralCellSchur_primitive

/--
info: 'SkewGluing.irreducible_integralConnectedSchur' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.irreducible_integralConnectedSchur

/--
info: 'SkewGluing.Profile.minorDet_eq_interiorSchur' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.Profile.minorDet_eq_interiorSchur

/--
info: 'SkewGluing.Profile.integralSchur_corner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.Profile.integralSchur_corner

/--
info: 'SkewGluing.polynomialSpan_cellSchur' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.polynomialSpan_cellSchur

/--
info: 'SkewGluing.cellSchur_corner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.cellSchur_corner

/--
info: 'SkewGluing.interiorSchur_eq_of_cellSchur_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.interiorSchur_eq_of_cellSchur_eq

/--
info: 'SkewGluing.irreducible_integralCellSchur' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.irreducible_integralCellSchur

/--
info: 'SkewGluing.MarkedInner.IsLegal.middle_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.middle_subsingleton

/--
info: 'SkewGluing.MarkedInner.IsLegal.private_lower_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.private_lower_subsingleton

/--
info: 'SkewGluing.MarkedInner.IsLegal.private_upper_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.private_upper_subsingleton

/--
info: 'SkewGluing.MarkedInner.IsLegal.interior_eq_caps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.interior_eq_caps

/--
info: 'SkewGluing.MarkedInner.IsLegal.interiorSchur_eq_caps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.interiorSchur_eq_caps

/--
info: 'SkewGluing.MarkedInner.IsLegal.capTheta_span_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.capTheta_span_le

/--
info: 'SkewGluing.MarkedInner.IsLegal.middleCofactor_span_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.middleCofactor_span_le

/--
info: 'SkewGluing.MarkedInner.IsLegal.private_lower_eq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.private_lower_eq_singleton

/--
info: 'SkewGluing.MarkedInner.IsLegal.private_upper_eq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.private_upper_eq_singleton

/--
info: 'SkewGluing.MarkedInner.IsLegal.interior_windowCells' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.interior_windowCells

/--
info: 'SkewGluing.MarkedInner.IsLegal.hatMarkWindow_eq_caps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.hatMarkWindow_eq_caps

/--
info: 'SkewGluing.MarkedInner.IsLegal.isSkew_hatMarkWindow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.isSkew_hatMarkWindow

/--
info: 'SkewGluing.MarkedInner.IsLegal.hatMarkWindow_span_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.hatMarkWindow_span_le

/--
info: 'SkewGluing.MarkedInner.IsLegal.markA_span_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.markA_span_le

/--
info: 'SkewGluing.MarkedInner.IsLegal.hatMarkB_span_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.hatMarkB_span_le

/--
info: 'SkewGluing.MarkedInner.IsLegal.mem_hatMark_iff_window' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.mem_hatMark_iff_window

/--
info: 'SkewGluing.MarkedInner.IsLegal.hatMark_eq_caps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.hatMark_eq_caps

/--
info: 'SkewGluing.MarkedInner.compose_horizontalRow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.compose_horizontalRow

/--
info: 'SkewGluing.MarkedInner.IsLegal.interior_rowCopies_all' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.interior_rowCopies_all

/--
info: 'SkewGluing.MarkedInner.IsLegal.interior_compose_horizontalRow_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.interior_compose_horizontalRow_all

/--
info: 'SkewGluing.cellSchur_biUnion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.cellSchur_biUnion

/--
info: 'SkewGluing.MarkedInner.IsLegal.isConnectedSkew_rowCopies_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.isConnectedSkew_rowCopies_all

/--
info: 'SkewGluing.MarkedInner.IsLegal.interiorSchur_row_normalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.interiorSchur_row_normalization

/--
info: 'SkewGluing.MarkedInner.IsLegal.interiorSchur_compose_row_normalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.interiorSchur_compose_row_normalization

/--
info: 'SkewGluing.MarkedInner.IsLegal.normal_mark_spans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.normal_mark_spans

/--
info: 'SkewGluing.MarkedInner.IsLegal.normalTheta_span_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.normalTheta_span_le

/--
info: 'SkewGluing.MarkedInner.IsLegal.normalC_span_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.normalC_span_le

/--
info: 'SkewGluing.interiorSchur_mem_below' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.interiorSchur_mem_below

/--
info: 'SkewGluing.pderiv_cellSchur_corner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.pderiv_cellSchur_corner

/--
info: 'SkewGluing.MarkedInner.IsLegal.modifiedCompositionMap_mem_below' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.modifiedCompositionMap_mem_below

/--
info: 'SkewGluing.MarkedInner.IsLegal.coefficient_transport_substitution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.coefficient_transport_substitution

/--
info: 'GluingCore.Plan.exists_legalComposition_algHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GluingCore.Plan.exists_legalComposition_algHom

/--
info: 'SkewGluing.MarkedInner.IsLegal.modifiedCompositionMap_cellSchur' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.modifiedCompositionMap_cellSchur

/--
info: 'SkewGluing.MarkedInner.IsLegal.normalized_cofactor_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.normalized_cofactor_transport

/--
info: 'SkewGluing.MarkedInner.IsLegal.modifiedCompositionMap_component_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.modifiedCompositionMap_component_product

/--
info: 'SkewGluing.MarkedInner.IsLegal.corner_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.corner_transport

/--
info: 'SkewGluing.MarkedInner.IsLegal.highSpan_factor_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.highSpan_factor_iff

/--
info: 'SkewGluing.MarkedInner.IsLegal.highSpan_multiplicity_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.highSpan_multiplicity_count

/--
info: 'SkewGluing.MarkedInner.IsLegal.child_span_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.child_span_descent

/--
info: 'SkewGluing.MarkedInner.IsLegal.child_card_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.child_card_descent

/--
info: 'SkewGluing.MarkedInner.IsLegal.child_at_minimum_span' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.child_at_minimum_span

/--
info: 'GluingCore.Chart.IsSourceMinimal.outer_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GluingCore.Chart.IsSourceMinimal.outer_independent

/--
info: 'GluingCore.Chart.IsSourceMinimal.period_eq_of_line' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GluingCore.Chart.IsSourceMinimal.period_eq_of_line

/--
info: 'GluingCore.PeriodFailure.discrete_of_least_span' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GluingCore.PeriodFailure.discrete_of_least_span

/--
info: 'GluingCore.sourceMinimal_periods_iff_discrete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GluingCore.sourceMinimal_periods_iff_discrete

/--
info: 'GluingCore.Chart.IsSourceMinimal.beta_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GluingCore.Chart.IsSourceMinimal.beta_reduction

/--
info: 'SkewGluing.cellSchur_eq_of_associated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.cellSchur_eq_of_associated

/--
info: 'SkewGluing.MarkedInner.IsLegal.period_tests' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.period_tests

/--
info: 'SkewGluing.MarkedInner.IsLegal.candidate_sum_eq_interior_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.candidate_sum_eq_interior_span

/--
info: 'SkewGluing.MarkedInner.IsLegal.parent_div_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.parent_div_mod

/--
info: 'SkewGluing.MarkedInner.IsLegal.alpha_row_candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.alpha_row_candidate

/--
info: 'SkewGluing.Profile.gaps_eq_one_of_discrete_row_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.Profile.gaps_eq_one_of_discrete_row_count

/--
info: 'SkewGluing.polynomialSpan_cellSchur_lt_of_orders' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.polynomialSpan_cellSchur_lt_of_orders

/--
info: 'SkewCornerDescent.Matrix.exists_selectedCoordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.exists_selectedCoordinate

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.interval_derivative_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.interval_derivative_identities

/--
info: 'SkewCornerDescent.Matrix.commonCore_cross_difference_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.commonCore_cross_difference_dvd

/-- info: 'SkewCornerDescent.Matrix.singularCore_zero_column_at'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.singularCore_zero_column_at

/-- info: 'SkewCornerDescent.Matrix.borderedCoreMatrix_det_of_zero_column'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.borderedCoreMatrix_det_of_zero_column

/-- info: 'SkewCornerDescent.Matrix.commonCore_cross_difference_of_singular'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.commonCore_cross_difference_of_singular

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_commonCore_cross_difference_dvd'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selected_commonCore_cross_difference_dvd

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCorner_residue_singular'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCorner_residue_singular

/-- info: 'SkewCornerDescent.Matrix.borderedCoreMatrix_of_zero_rectangles'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.borderedCoreMatrix_of_zero_rectangles

/-- info: 'SkewCornerDescent.Matrix.det_commonCoreFramePerm'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.det_commonCoreFramePerm

/-- info: 'SkewCornerDescent.Matrix.commonCore_cross_difference_column_orientation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.commonCore_cross_difference_column_orientation

/-- info: 'SkewCornerDescent.Matrix.det_commonCoreFiniteFrame'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.det_commonCoreFiniteFrame

/-- info: 'SkewCornerDescent.Matrix.det_originalProfileFrame'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.det_originalProfileFrame

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLowerWindow_frame_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLowerWindow_frame_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalUpperWindow_frame_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalUpperWindow_frame_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_frame_zeros'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_frame_zeros

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLowerWindow_frame_core'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLowerWindow_frame_core

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalUpperWindow_frame_core'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalUpperWindow_frame_core

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_frame_core'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_frame_core

/-- info: 'SkewCornerDescent.Matrix.originalProfileFrame_entry_of_val'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalProfileFrame_entry_of_val

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_zeta_alignment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_zeta_alignment

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLowerWindow_frame_last'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLowerWindow_frame_last

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalUpperWindow_frame_first'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalUpperWindow_frame_first

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_frame_left'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_frame_left

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_frame_upper_core'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_frame_upper_core

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_frame_right'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_frame_right

/-- info: 'SkewCornerDescent.Matrix.originalWindow_frame_cross_difference_dvd'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalWindow_frame_cross_difference_dvd

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_cross_difference_dvd'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_cross_difference_dvd

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_residue_cross_identity'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_residue_cross_identity

/--
info: 'SkewCornerDescent.CyclicWindows.sum_windowSum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.sum_windowSum

/--
info: 'SkewCornerDescent.CyclicWindows.periodic_gcd' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.periodic_gcd

/--
info: 'SkewCornerDescent.CyclicWindows.windows_constant_of_maximum_eq_average' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.windows_constant_of_maximum_eq_average

/--
info: 'SkewCornerDescent.CyclicWindows.inverseWindowSum_mul_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.inverseWindowSum_mul_add

/--
info: 'SkewCornerDescent.CyclicWindows.zmod_sum_inverse_full_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.zmod_sum_inverse_full_cycle

/--
info: 'SkewCornerDescent.Matrix.componentResponse_eq_normal_quotient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.componentResponse_eq_normal_quotient

/--
info: 'SkewCornerDescent.Matrix.generatorDeriv_componentResponse_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_componentResponse_top

/--
info: 'SkewCornerDescent.Matrix.not_dvd_distinct_component' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.not_dvd_distinct_component

/--
info: 'SkewCornerDescent.Matrix.not_dvd_complementary_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.not_dvd_complementary_product

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_coefficient

/--
info: 'SkewCornerDescent.BinaryTransitions.cyclic_curvature_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.BinaryTransitions.cyclic_curvature_ne_zero

/--
info: 'SkewCornerDescent.SinglePositive.strict_single_positive_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.SinglePositive.strict_single_positive_support

/--
info: 'SkewCornerDescent.Matrix.componentInterval_triangular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.componentInterval_triangular

/--
info: 'SkewCornerDescent.Matrix.componentResponse_eq_intervalResponse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.componentResponse_eq_intervalResponse

/--
info: 'SkewCornerDescent.Matrix.componentInterval_profiles_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.componentInterval_profiles_ordinary

/--
info: 'SkewCornerDescent.Matrix.intervalResponse_triangular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.intervalResponse_triangular

/--
info: 'SkewCornerDescent.Matrix.hessenberg_det_constant_subdiagonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.hessenberg_det_constant_subdiagonal

/--
info: 'SkewCornerDescent.Matrix.mapped_hessenberg_det' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.mapped_hessenberg_det

/--
info: 'SkewCornerDescent.PhaseInventory.omitted_phase_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.PhaseInventory.omitted_phase_defect

/--
info: 'SkewCornerDescent.PhaseInventory.no_two_full_defect_classes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.PhaseInventory.no_two_full_defect_classes

/--
info: 'SkewCornerDescent.Matrix.componentInterval_inverse_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.componentInterval_inverse_lower

/--
info: 'SkewCornerDescent.Matrix.original_inverse_regular_denominator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.original_inverse_regular_denominator

/--
info: 'SkewCornerDescent.Matrix.original_inverse_span_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.original_inverse_span_bound

/--
info: 'SkewCornerDescent.Matrix.original_generator_transcendental' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.original_generator_transcendental

/--
info: 'SkewCornerDescent.Matrix.triangular_quotient_transcendental' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.triangular_quotient_transcendental

/--
info: 'SkewCornerDescent.Matrix.triangular_ne_of_top_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.triangular_ne_of_top_lt

/--
info: 'SkewCornerDescent.Matrix.componentResponse_transcendental' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.componentResponse_transcendental

/--
info: 'SkewCornerDescent.Matrix.protected_pole_detector_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.protected_pole_detector_ne_zero

/--
info: 'SkewCornerDescent.RationalPoles.scaled_pole_sum_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.RationalPoles.scaled_pole_sum_ne_zero

/--
info: 'SkewCornerDescent.Matrix.inverseContraction_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.inverseContraction_interval

/--
info: 'SkewCornerDescent.Matrix.orderedIntervalInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.orderedIntervalInverse

/--
info: 'SkewCornerDescent.Matrix.intervalResponse_ordered_restriction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.intervalResponse_ordered_restriction

/--
info: 'SkewCornerDescent.Matrix.ordered_intervalResponse_triangular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.ordered_intervalResponse_triangular

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalChart_prime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.normalChart_prime

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalFieldMap_prime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.normalFieldMap_prime

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalChart_coeff_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.normalChart_coeff_zero_iff

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.regularEmbedding_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.regularEmbedding_injective

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.regularResidue_fraction_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.regularResidue_fraction_eq_zero_iff

/--
info: 'SkewCornerDescent.Matrix.residue_generator_transcendental' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residue_generator_transcendental

/--
info: 'SkewCornerDescent.Matrix.residue_triangular_quotient_transcendental' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residue_triangular_quotient_transcendental

/--
info: 'SkewCornerDescent.Matrix.map_retainedResponse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.map_retainedResponse

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.local_det_eq_removed_mul_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.local_det_eq_removed_mul_response

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.localRetainedResponse_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.localRetainedResponse_residue

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.localRetainedResponse_embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.localRetainedResponse_embedding

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_selectedMinor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_selectedMinor

/-- info: 'SkewCornerDescent.Matrix.adjugate_fin_two_minor_dvd' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.adjugate_fin_two_minor_dvd

/-- info: 'SkewCornerDescent.Matrix.invOf_row_exists_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.invOf_row_exists_ne_zero

/-- info: 'SkewCornerDescent.Matrix.invOf_col_exists_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.invOf_col_exists_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_inverse_row_exists_ne_zero' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_inverse_row_exists_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_inverse_col_exists_ne_zero' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_inverse_col_exists_ne_zero

/-- info: 'SkewCornerDescent.SinglePositive.finite_mean_signed_detector' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SinglePositive.finite_mean_signed_detector
