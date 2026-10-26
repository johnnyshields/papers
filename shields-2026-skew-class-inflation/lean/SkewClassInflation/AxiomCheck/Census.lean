/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.UnboundedSplitting
import SkewClassInflation.ClassCountExamples

/-!
# Exact binary-family census axiom footprints

Every expected message is the observed kernel footprint of the declaration it guards.
-/

/-- info: 'SkewClassInflation.composition_ext_of_blocks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.composition_ext_of_blocks

/-- info: 'SkewClassInflation.composition_one_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.composition_one_blocks

/-- info: 'SkewClassInflation.binaryRibbon_census' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbon_census

/-- info: 'SkewClassInflation.binaryRibbon_class_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbon_class_eq

/-- info: 'SkewClassInflation.binaryRibbon_class_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbon_class_card

/-- info: 'SkewClassInflation.splittingSource_class_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splittingSource_class_card

/-- info: 'SkewClassInflation.splittingSource_image_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splittingSource_image_card

/-- info: 'SkewClassInflation.splittingSource_image_class_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splittingSource_image_class_count

/-- info: 'SkewClassInflation.outer_one_two_class_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.outer_one_two_class_card

/-- info: 'SkewClassInflation.threshold_two_class_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_two_class_card

/-- info: 'SkewClassInflation.threshold_two_class_card_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_two_class_card_one

/-- info: 'SkewClassInflation.threshold_two_class_card_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_two_class_card_two

/-- info: 'SkewClassInflation.splitting_two_source_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splitting_two_source_card

/-- info: 'SkewClassInflation.splitting_two_image_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splitting_two_image_card

/-- info: 'SkewClassInflation.splitting_two_class_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splitting_two_class_count

/-- info: 'SkewClassInflation.asymmetric_inner_class_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.asymmetric_inner_class_card

/-- info: 'SkewClassInflation.symmetric_inner_class_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.symmetric_inner_class_card
