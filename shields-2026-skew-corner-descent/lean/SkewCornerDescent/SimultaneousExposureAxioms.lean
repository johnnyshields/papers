/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ActualTwoChambers
import SkewCornerDescent.ExposureLabels

/-!
# Simultaneous exposure axiom guards

Guards the real-specialization bridge, simultaneous actual chambers, cap positivity,
and extreme-anchor exposure for `lem:exposure`.
-/

namespace SkewCornerDescent

/--
info: 'SkewCornerDescent.exists_simultaneous_rational_roots' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_simultaneous_rational_roots

/--
info: 'SkewCornerDescent.rational_roots_ne_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rational_roots_ne_iff

/--
info: 'SkewCornerDescent.rational_root_separation_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rational_root_separation_open

/--
info: 'SkewCornerDescent.simultaneous_root_signs_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms simultaneous_root_signs_open

/--
info: 'SkewCornerDescent.signed_cap_product_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms signed_cap_product_pos

/--
info: 'SkewCornerDescent.normalizedAnchorLabel_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms normalizedAnchorLabel_lt_iff

/--
info: 'SkewCornerDescent.anchor_response_eq_normalized_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms anchor_response_eq_normalized_difference

/--
info: 'SkewCornerDescent.constant_active_label_extremes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms constant_active_label_extremes

/--
info: 'SkewCornerDescent.Matrix.real_fraction_eq_of_fraction_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matrix.real_fraction_eq_of_fraction_eq

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_simultaneous_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Matrix.SelectedCoordinate.originalResponses_simultaneous_roots

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_simultaneous_chambers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Matrix.SelectedCoordinate.originalResponses_simultaneous_chambers

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_cap_product_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Matrix.SelectedCoordinate.simultaneousActualChamber_cap_product_pos

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_roots_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Matrix.SelectedCoordinate.simultaneousActualChamber_roots_injective

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_exposed_extreme' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Matrix.SelectedCoordinate.simultaneousActualChamber_exposed_extreme

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalTrueCaps_below_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Matrix.SelectedCoordinate.originalTrueCaps_below_closure

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_two_exposure_chambers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Matrix.SelectedCoordinate.originalResponses_two_exposure_chambers

end SkewCornerDescent
