/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TransportSign

/-!
# Axiom guards for coefficient transport

Guards the component product and the exact signed coefficient identity in
`shields-2026-skew-corner-descent.tex` (`sec:transport`, `eq:coefficient-transport`).
-/

/--
info: 'SkewGluing.MarkedInner.IsLegal.modifiedCompositionMap_interior_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.modifiedCompositionMap_interior_product

/--
info: 'SkewGluing.MarkedInner.IsLegal.coefficient_transport_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.coefficient_transport_signed
