/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.NonnegativeRigidity
import SkewCofactorIndependence.SymmetricCofactors
import SkewCofactorIndependence.IntegralPrimitiveBridge
import SkewCofactorIndependence.FirstVariations
import SkewCofactorIndependence.DisjointAlphabet
import SkewCofactorIndependence.WordPeriods
import SkewCofactorIndependence.ResidueSpaces
import SkewCofactorIndependence.DenseDilation
import SkewCofactorIndependence.SymmetricUnitCoordinates
import SkewCofactorIndependence.DilationRay
import SkewCofactorIndependence.RestorationRigidity
import SkewCofactorIndependence.UnitDegrees
import SkewCofactorIndependence.BetaProfiles
import SkewCofactorIndependence.RestorationWitnesses
import SkewCofactorIndependence.KernelRigidity

/-!
# Observed proof footprints

These guards pin the observed footprints of the compiled assemblies and their
mathematical producers.  The guard imports producers directly, never the root.
-/

/-- info: 'SkewCofactorIndependence.BetaDiagram.nonnegative_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCofactorIndependence.BetaDiagram.nonnegative_rigidity

/-- info: 'SkewCofactorIndependence.BetaDiagram.schur_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCofactorIndependence.BetaDiagram.schur_irreducible

/-- info: 'SkewCofactorIndependence.symmetric_cofactor_relations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCofactorIndependence.symmetric_cofactor_relations

/-- info: 'SkewCofactorIndependence.BetaDiagram.schur_totalDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCofactorIndependence.BetaDiagram.schur_totalDegree

/-- info: 'SkewCofactorIndependence.BetaDiagram.unitVariation_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCofactorIndependence.BetaDiagram.unitVariation_endpoint

/-- info: 'SkewCofactorIndependence.disjointAlphabet_independence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCofactorIndependence.disjointAlphabet_independence

/-- info: 'SkewCofactorIndependence.WordPeriod.gcd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewCofactorIndependence.WordPeriod.gcd

/-- info: 'SkewCofactorIndependence.offGrid_dimension_modulus_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCofactorIndependence.offGrid_dimension_modulus_one

/-- info: 'SkewCofactorIndependence.irreducible_integer_of_integerLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCofactorIndependence.irreducible_integer_of_integerLift

/-- info: 'SkewCofactorIndependence.BetaDiagram.nonsymmetric_cofactor_relations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.nonsymmetric_cofactor_relations

/-- info: 'SkewCofactorIndependence.BetaDiagram.integerSchur_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.integerSchur_irreducible

/-- info: 'SkewCofactorIndependence.BetaDiagram.dense_nonsymmetric_dilation_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.dense_nonsymmetric_dilation_kernel

/-- info: 'SkewCofactorIndependence.BetaDiagram.symmetric_unitKernel_eq_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.symmetric_unitKernel_eq_span

/-- info: 'SkewCofactorIndependence.BetaDiagram.dilation_nullity_increment_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.dilation_nullity_increment_general

/-- info: 'SkewCofactorIndependence.dilationRayKernelBasis_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCofactorIndependence.dilationRayKernelBasis_apply

/-- info: 'SkewCofactorIndependence.BetaDiagram.independent_restorations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.independent_restorations

/-- info: 'SkewCofactorIndependence.BetaDiagram.restoration_path_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.restoration_path_expansion

/-- info: 'SkewCofactorIndependence.BetaDiagram.restoration_first_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.restoration_first_coefficients

/-- info: 'SkewCofactorIndependence.BetaDiagram.restoration_lowest_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.restoration_lowest_nonzero

/-- info: 'SkewCofactorIndependence.BetaDiagram.unitVariation_index_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.unitVariation_index_homogeneous

/-- info: 'SkewCofactorIndependence.BetaDiagram.unitVariation_ordinary_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.unitVariation_ordinary_component

/-- info: 'SkewCofactorIndependence.BetaDiagram.translationEquivalent_iff_profile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.translationEquivalent_iff_profile

/-- info: 'SkewCofactorIndependence.restoration_components_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.restoration_components_eq

/-- info: 'SkewCofactorIndependence.restorationZ_separator_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.restorationZ_separator_coefficient

/-- info: 'SkewCofactorIndependence.restorationW_separator_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.restorationW_separator_coefficient

/-- info: 'SkewCofactorIndependence.restoration_full_schur_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.restoration_full_schur_ne

/-- info: 'SkewCofactorIndependence.symmetricDouble_relation_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.symmetricDouble_relation_kernel

/-- info: 'SkewCofactorIndependence.symmetricDouble_relation_not_inherited_sup_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.symmetricDouble_relation_not_inherited_sup_arithmetic

/-- info: 'SkewCofactorIndependence.BetaDiagram.symmetric_unitKernel_eq_bot_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.symmetric_unitKernel_eq_bot_iff

/-- info: 'SkewCofactorIndependence.BetaDiagram.dense_double_unitKernel_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.dense_double_unitKernel_eq_bot

/-- info: 'SkewCofactorIndependence.BetaDiagram.dense_double_independent_restorations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCofactorIndependence.BetaDiagram.dense_double_independent_restorations
