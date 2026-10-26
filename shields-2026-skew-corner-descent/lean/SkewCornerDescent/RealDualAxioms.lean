/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.SubfieldDualNonvanishing
import SkewCornerDescent.RealTrueCapDualNonvanishing
import SkewCornerDescent.SubfieldWindowDualNonvanishing
import SkewCornerDescent.CyclicAutomaticInventory
import SkewCornerDescent.SubfieldExposureInventories

/-!
# Axiom guards for real and subfield dual nonvanishing

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-general`).
These guards pin the complete real peeling and coefficient-extension assemblies.
Sorry-free.
-/

/-- info: 'SkewCornerDescent.realChamber_active_extreme_is_omitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.realChamber_active_extreme_is_omitted

/-- info: 'SkewCornerDescent.realActiveLabels_dual_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.realActiveLabels_dual_nonvanishing

/-- info: 'SkewCornerDescent.subfieldActiveLabels_dual_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.subfieldActiveLabels_dual_nonvanishing

/-- info: 'SkewCornerDescent.realTrueCaps_dual_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.realTrueCaps_dual_nonvanishing

/-- info: 'SkewCornerDescent.simultaneousRealChamber_open_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.simultaneousRealChamber_open_nonempty

/-- info: 'SkewCornerDescent.realTrueCaps_windowDefect_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.realTrueCaps_windowDefect_nonvanishing

/-- info: 'SkewCornerDescent.subfieldTrueCaps_windowDefect_nonvanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.subfieldTrueCaps_windowDefect_nonvanishing

/-- info: 'SkewCornerDescent.CyclicWindows.one_position_windowDefect_short_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.one_position_windowDefect_short_zero

/-- info: 'SkewCornerDescent.CyclicWindows.one_position_windowDefect_full_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.one_position_windowDefect_full_zero

/-- info: 'SkewCornerDescent.subfieldExposure_inventories_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.subfieldExposure_inventories_nonvanishing

/-- info: 'SkewCornerDescent.CyclicWindows.windowDefect_eq_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.windowDefect_eq_last
