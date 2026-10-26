/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalFullWindowCancellation

/-!
# Literal full-window inventory and removed-factor axiom guards

Pins the elaborated footprints of the actual overlap, closure and full-factor producers.
-/

/-- info: 'SkewCornerDescent.cellSchur_complete_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.cellSchur_complete_overlap

/-- info: 'SkewCornerDescent.literalOverlap_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.literalOverlap_interior

/-- info: 'SkewCornerDescent.literalOverlap_interior_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.literalOverlap_interior_intersection

/-- info: 'SkewCornerDescent.literalOverlap_interior_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.literalOverlap_interior_separated

/-- info: 'SkewCornerDescent.literalOverlap_corner_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.literalOverlap_corner_product

/-- info: 'SkewCornerDescent.literalOverlap_corner_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.literalOverlap_corner_power

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalFullWindow_removed_cancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalFullWindow_removed_cancel

/-- info: 'SkewCornerDescent.Matrix.originalEmptyHorizontal_corner_inventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.originalEmptyHorizontal_corner_inventory

/-- info: 'SkewCornerDescent.Matrix.originalEmptyHorizontal_profile_inventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.originalEmptyHorizontal_profile_inventory
