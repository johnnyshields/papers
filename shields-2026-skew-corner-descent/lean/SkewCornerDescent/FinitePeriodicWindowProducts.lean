/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FinitePeriodicWords
import SkewCornerDescent.CyclicPeriodicProducts
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite overlap products with complete inverse weights

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual finite overlap periods produce the window multiplicities and full
period powers, including repeated wraps and empty-window boundaries.
Sorry-free.
-/

namespace SkewCornerDescent
open scoped BigOperators
open CyclicWindows

/-- Actual finite overlap words supply the complete period power for every
window start, without nonzero-letter or division assumptions. -/
theorem finite_periodic_window_product {R : Type*} [CommMonoid R]
    {L r : ℕ} [NeZero r] (word : Fin L → R) (hr : r ≤ L)
    (hp : ∀ i j : Fin L, j.val = i.val + r → word i = word j)
    (d s : ℕ) (hbound : s + d * r ≤ L) :
    (∏ k : Fin (d * r), word ⟨s + k.val, by have := k.isLt; omega⟩) =
      (∏ k : Fin r, word ⟨k.val, k.isLt.trans_le hr⟩)^d := by
  classical
  let f := finiteWordCycle word hr
  have hperiod : Function.Periodic f (r : ZMod r) := by
    intro z
    simp
  have h := windowProduct_of_zmod_period_multiple f r hperiod d (s : ZMod r)
  have hleft : (∏ k : Fin (d * r), word ⟨s + k.val, by have := k.isLt; omega⟩) =
      windowProduct f 1 (d * r) (s : ZMod r) := by
    unfold windowProduct
    simp only [nsmul_eq_mul, mul_one, Finset.prod_range]
    apply Finset.prod_congr rfl
    intro k _
    have he := finiteWordCycle_eq word hr hp
      ⟨s + k.val, by have := k.isLt; omega⟩
    simpa only [f, Nat.cast_add] using he
  have hbase : (∏ k : Fin r, word ⟨k.val, k.isLt.trans_le hr⟩) =
      windowProduct f 1 r 0 := by
    unfold windowProduct
    simp only [nsmul_eq_mul, mul_one, zero_add, Finset.prod_range]
    apply Finset.prod_congr rfl
    intro k _
    simp only [f, finiteWordCycle, ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt]
  exact hleft.trans (h.trans (congrArg (fun x : R => x^d) hbase.symm))

/-- The first actual letter remains after a complete finite period power. -/
theorem finite_periodic_window_product_succ {R : Type*} [CommMonoid R]
    {L r : ℕ} [NeZero r] (word : Fin L → R) (hr : r ≤ L)
    (hp : ∀ i j : Fin L, j.val = i.val + r → word i = word j)
    (d s : ℕ) (hbound : s + (d * r + 1) ≤ L) :
    (∏ k : Fin (d * r + 1), word ⟨s + k.val, by have := k.isLt; omega⟩) =
      (∏ k : Fin r, word ⟨k.val, k.isLt.trans_le hr⟩)^d *
        word ⟨s, by omega⟩ := by
  rw [Fin.prod_univ_succ]
  have hp' : ∀ i j : Fin L, j.val = i.val + r → word i = word j := hp
  have h := finite_periodic_window_product word hr hp' d (s + 1) (by omega)
  simp only [Fin.val_zero, add_zero, Fin.val_succ] at ⊢
  have he : (∏ i : Fin (d * r), word ⟨s + (i.val + 1), by have := i.isLt; omega⟩) =
      (∏ k : Fin r, word ⟨k.val, k.isLt.trans_le hr⟩)^d := by
    simpa only [Nat.add_assoc, Nat.add_comm 1] using h
  rw [he, mul_comm]

end SkewCornerDescent
