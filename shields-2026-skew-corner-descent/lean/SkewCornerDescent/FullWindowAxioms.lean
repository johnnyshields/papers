/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FullWindowProper

/-!
# Full-window boundary axiom guards

Guards literal cell tiling, connected first-band geometry, both ordinary root directions,
and the actual proper nonline root for `lem:boundary-full-window`.
-/

namespace SkewCornerDescent

/--
info: 'SkewCornerDescent.content_add_zsmul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms content_add_zsmul

/--
info: 'SkewCornerDescent.fullWindow_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fullWindow_step

/--
info: 'SkewCornerDescent.fullWindow_iterate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fullWindow_iterate

/--
info: 'SkewCornerDescent.fullWindow_cells_eq_copies' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fullWindow_cells_eq_copies

/--
info: 'SkewCornerDescent.firstContentBand_hasDiagonalShape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms firstContentBand_hasDiagonalShape

/--
info: 'SkewCornerDescent.firstContentBand_isConnectedSkew' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms firstContentBand_isConnectedSkew

/--
info: 'SkewCornerDescent.firstContentBand_contents' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms firstContentBand_contents

/--
info: 'SkewCornerDescent.firstContentBand_span' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms firstContentBand_span

/--
info: 'SkewCornerDescent.mem_verticalColumn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mem_verticalColumn

/--
info: 'SkewCornerDescent.verticalColumn_isConnectedSkew' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms verticalColumn_isConnectedSkew

/--
info: 'SkewCornerDescent.emptyMarkH_origin_verticalColumn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms emptyMarkH_origin_verticalColumn

/--
info: 'SkewCornerDescent.compose_empty_verticalColumn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms compose_empty_verticalColumn

/--
info: 'SkewCornerDescent.firstContentBand_extreme_contents' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms firstContentBand_extreme_contents

/--
info: 'SkewCornerDescent.adjacent_empty_displacement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms adjacent_empty_displacement

/--
info: 'SkewCornerDescent.fullWindow_firstBand_interior_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fullWindow_firstBand_interior_nonempty

/--
info: 'SkewCornerDescent.fullWindow_boundary_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fullWindow_boundary_root

/--
info: 'SkewCornerDescent.horizontalRow_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms horizontalRow_card

/--
info: 'SkewCornerDescent.verticalColumn_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms verticalColumn_card

/--
info: 'SkewCornerDescent.interior_nonempty_proper_cells' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms interior_nonempty_proper_cells

/--
info: 'SkewCornerDescent.fullWindow_boundary_proper_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fullWindow_boundary_proper_root

end SkewCornerDescent
