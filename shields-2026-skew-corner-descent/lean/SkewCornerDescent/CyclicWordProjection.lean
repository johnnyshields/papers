/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicFiniteIntervals

/-!
# Cyclic words induced by a shorter complete positional cycle

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). Divisible word
lengths permit the cyclic projection, so all periods and wrapped sums follow from the
indexed finite word correspondence. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- Finite positional correspondence identifies the complete cyclic projection. -/
theorem cyclicWord_eq_projection {α : Type*} {B r : ℕ} [NeZero B]
    (word : Fin B → α) (cycle : ZMod r → α) (hrB : r ∣ B)
    (hw : ∀ i, word i = cycle (i.val : ZMod r)) (z : ZMod B) :
    word ((ZMod.finEquiv B).symm z) = cycle (ZMod.castHom hrB (ZMod r) z) := by
  rw [hw]
  congr 1
  have he := congrArg (ZMod.castHom hrB (ZMod r))
    (finEquiv_eq_natCast ((ZMod.finEquiv B).symm z))
  rw [(ZMod.finEquiv B).apply_symm_apply, map_natCast] at he
  exact he.symm

/-- The complete cyclic word inherits the period equal to the shorter cycle length. -/
theorem cyclicWord_period_of_projection {α : Type*} {B r : ℕ} [NeZero B]
    (word : Fin B → α) (cycle : ZMod r → α) (hrB : r ∣ B)
    (hw : ∀ i, word i = cycle (i.val : ZMod r)) :
    Function.Periodic (fun z => word ((ZMod.finEquiv B).symm z)) (r : ZMod B) := by
  intro z
  dsimp only
  rw [cyclicWord_eq_projection word cycle hrB hw,
    cyclicWord_eq_projection word cycle hrB hw, map_add, map_natCast,
    ZMod.natCast_self, add_zero]

/-- Projected positional windows retain every wrap and have the same exact sum. -/
theorem cyclicWord_windowSum_projection {R : Type*} [AddCommMonoid R]
    {B r : ℕ} [NeZero B] (word : Fin B → R) (cycle : ZMod r → R) (hrB : r ∣ B)
    (hw : ∀ i, word i = cycle (i.val : ZMod r)) (j : ℕ) :
    windowSum (fun z => word ((ZMod.finEquiv B).symm z)) 1 j 0 =
      windowSum cycle 1 j 0 := by
  unfold windowSum
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [cyclicWord_eq_projection word cycle hrB hw]
  simp only [map_add, map_zero, map_nsmul, map_one]

end SkewCornerDescent.CyclicWindows
