/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.InteriorWindowPeriod

/-!
# Axiom guards for actual periodic windows and whole private components

Every guarded statement uses only the documented standard Lean axioms.
-/

namespace SkewCornerDescent


/-- info: 'SkewCornerDescent.literalWindow_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literalWindow_step

/-- info: 'SkewCornerDescent.literalWindow_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literalWindow_iterate

/-- info: 'SkewCornerDescent.literalWindow_cell_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literalWindow_cell_reconstruction

/-- info: 'SkewCornerDescent.literalWindow_band_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literalWindow_band_eq

/-- info: 'SkewCornerDescent.literalWindow_cells_eq_prefix_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literalWindow_cells_eq_prefix_copies

/-- info: 'SkewCornerDescent.interior_content_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_content_filter

/-- info: 'SkewCornerDescent.interior_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_translate

/-- info: 'SkewCornerDescent.literalWindow_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literalWindow_interior

/-- info: 'SkewCornerDescent.privateDiagonal_avoids_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms privateDiagonal_avoids_interior

/-- info: 'SkewCornerDescent.connected_subdiagram_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms connected_subdiagram_gap

/-- info: 'SkewCornerDescent.privateDiagonal_component_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms privateDiagonal_component_side

/-- info: 'SkewCornerDescent.privateDiagonal_component_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms privateDiagonal_component_prefix

end SkewCornerDescent
