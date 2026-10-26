/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SharpInflation

/-!
# Exact FactorGeneration axiom footprints

Every expected message is the observed kernel footprint of the declaration it guards.
-/

/-- info: 'SkewClassInflation.integerLift_ribbonParts_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.integerLift_ribbonParts_word

/-- info: 'SkewClassInflation.compose_eq_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compose_eq_flatten

/-- info: 'SkewClassInflation.factorReversal_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.factorReversal_of_witness

/-- info: 'SkewClassInflation.factorReversal_of_ribbon_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.factorReversal_of_ribbon_eq

/-- info: 'SkewClassInflation.ribbonClass_eq_factorReversal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonClass_eq_factorReversal

/-- info: 'SkewClassInflation.ThinParameters.inflation_class_generated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflation_class_generated

/-- info: 'SkewClassInflation.ThinParameters.sharp_inflation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.sharp_inflation

/-- info: 'SkewRibbonCoarsenings.localAlternativeOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewRibbonCoarsenings.localAlternativeOmega

/-- info: 'SkewRibbonCoarsenings.G_eq_iff_factorWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewRibbonCoarsenings.G_eq_iff_factorWitness
