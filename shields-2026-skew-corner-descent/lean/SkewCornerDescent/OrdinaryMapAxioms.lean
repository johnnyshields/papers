/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.GeometricCompositionMap

/-!
# Ordinary composition orientation axiom guard

Pins the positive-sign geometric homomorphism for both ordinary attachment readings.
-/

/-- info: 'SkewGluing.MarkedInner.IsLegal.modifiedCompositionMap_cellSchur_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.IsLegal.modifiedCompositionMap_cellSchur_ordinary
