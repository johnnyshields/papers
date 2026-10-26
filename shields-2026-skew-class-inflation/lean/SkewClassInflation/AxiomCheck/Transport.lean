/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileWords
import SkewClassInflation.CellInflation
import SkewClassInflation.InflateConnected

/-!
# Exact Transport axiom footprints

Erosion, exact zero-free class transport, membership words and cell inflation are guarded at
their observed kernel footprints.
-/

/-- info: 'SkewClassInflation.erosion_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.erosion_lowering

/-- info: 'SkewClassInflation.mem_erodeCells_profileCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.mem_erodeCells_profileCells

/-- info: 'SkewClassInflation.card_erodeCells_profileCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.card_erodeCells_profileCells

/-- info: 'SkewClassInflation.erodedSchur_eq_of_profileSchur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.erodedSchur_eq_of_profileSchur_eq

/-- info: 'SkewClassInflation.erodedSchur_eq_deflate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.erodedSchur_eq_deflate

/-- info: 'SkewClassInflation.hOne_mul_shiftDown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.hOne_mul_shiftDown

/-- info: 'SkewClassInflation.det_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.det_shift

/-- info: 'SkewClassInflation.Profile.negOneCount_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.negOneCount_eq_zero_iff

/-- info: 'SkewClassInflation.Profile.negOneCount_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.negOneCount_eq_sum

/--
info: 'SkewClassInflation.Profile.negOneCount_eq_of_profileSchur_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewClassInflation.Profile.negOneCount_eq_of_profileSchur_eq

/-- info: 'SkewClassInflation.Profile.canDeflate_one_of_zeroFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.canDeflate_one_of_zeroFree

/-- info: 'SkewClassInflation.Profile.negOneCount_deflate_of_zeroFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.negOneCount_deflate_of_zeroFree

/--
info: 'SkewClassInflation.Profile.profileSchur_inflate_one_of_negOneCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewClassInflation.Profile.profileSchur_inflate_one_of_negOneCount

/-- info: 'SkewClassInflation.Profile.profileSchur_inflate_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.profileSchur_inflate_one_eq

/-- info: 'SkewClassInflation.Profile.deflate_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.deflate_rotate

/-- info: 'SkewClassInflation.zeroFree_class_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zeroFree_class_transport

/-- info: 'SkewClassInflation.inflateCells_profileCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inflateCells_profileCells

/-- info: 'SkewClassInflation.inflateCells_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inflateCells_translate

/-- info: 'SkewClassInflation.inflateCells_biUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inflateCells_biUnion

/-- info: 'SkewClassInflation.compose_inflateMarked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compose_inflateMarked

/-- info: 'SkewClassInflation.compose_empty_inflateMarked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compose_empty_inflateMarked

/-- info: 'SkewClassInflation.Profile.wordA_inflate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.wordA_inflate

/-- info: 'SkewClassInflation.Profile.wordB_inflate_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.wordB_inflate_one

/-- info: 'SkewClassInflation.Profile.wordH_inflate_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.wordH_inflate_one

/-- info: 'SkewClassInflation.Profile.zeroFree_inflate_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.zeroFree_inflate_one_iff

/--
info: 'SkewClassInflation.Profile.zeroIdxCount_eq_of_profileSchur_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewClassInflation.Profile.zeroIdxCount_eq_of_profileSchur_eq

/-- info: 'SkewClassInflation.Profile.zeroFree_iff_zeroIdxCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.zeroFree_iff_zeroIdxCount

/-- info: 'SkewClassInflation.Profile.zeroFree_of_profileSchur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.zeroFree_of_profileSchur_eq

/-- info: 'SkewClassInflation.mem_inflateCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.mem_inflateCells

/-- info: 'SkewClassInflation.inflateCells_diagonals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inflateCells_diagonals

/-- info: 'SkewClassInflation.isConnectedSkew_inflateCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.isConnectedSkew_inflateCells
