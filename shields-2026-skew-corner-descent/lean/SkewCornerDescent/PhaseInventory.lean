/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicWindows
import Mathlib.Tactic

/-!
# The omitted-phase inventory identity

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original coefficients»
(`sec:dual`, `lem:peeling`, `thm:dual-period`). Constant short-window counts give the
exact class exponent at the omitted position. Two distinct classes cannot both carry
the full defect there. This is the combinatorial closure, not the exposed-divisor
valuation argument. Sorry-free.
-/

namespace SkewCornerDescent.PhaseInventory

open CyclicWindows
open scoped BigOperators

/-- The class mask retains each actual position of the word. -/
def classMask {G α : Type*} [DecidableEq α] (word : G → α) (X : α) (i : G) : ℕ :=
  if word i = X then 1 else 0

/-- A constant short-window count has the exact reduced average after canceling the
positive multiplicity. No division convention at zero is used. -/
theorem reduced_constant_count {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r)
    (f : ZMod (r * d) → ℕ) (k : ℕ)
    (h : ∀ i, windowSum f 1 (r * s) i = k) :
    d * k = s * ∑ i, f i := by
  have he := constant_window_count f 1 (r * s) k h
  simp only [ZMod.card] at he
  have he' : r * (d * k) = r * (s * ∑ i, f i) := by
    simpa only [mul_assoc] using he
  exact mul_left_cancel₀ hr.ne' he'

/-- Removing the final position from a constant short window leaves precisely its
omitted-phase contribution in the signed inventory defect. -/
theorem omitted_phase_defect {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r) (hs : 0 < s)
    (f : ZMod (r * d) → ℕ) (k : ℕ)
    (h : ∀ i, windowSum f 1 (r * s) i = k) :
    (s : ℤ) * (∑ i, f i) - (d : ℤ) * windowSum f 1 (r * s - 1) 0 =
      (d : ℤ) * f ((r * s - 1 : ℕ) : ZMod (r * d)) := by
  have he := reduced_constant_count hr f k h
  have heZ : (d : ℤ) * k = (s : ℤ) * (∑ i, f i) := by exact_mod_cast he
  have hm : r * s - 1 + 1 = r * s := by have := Nat.mul_pos hr hs; omega
  have hw : windowSum f 1 (r * s) 0 =
      windowSum f 1 (r * s - 1) 0 + f ((r * s - 1 : ℕ) : ZMod (r * d)) := by
    unfold windowSum
    rw [← hm, Finset.sum_range_succ]
    simp only [zero_add, nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
  rw [h 0] at hw
  have hwZ : (k : ℤ) = ((windowSum f 1 (r * s - 1) 0 : ℕ) : ℤ) +
      f ((r * s - 1 : ℕ) : ZMod (r * d)) := by exact_mod_cast hw
  rw [← heZ, hwZ]
  ring

/-- The whole defect at a class with constant windows forces that class to occupy the
unique omitted position. -/
theorem class_at_omitted_phase {α : Type*} [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (word : ZMod (r * d) → α) (X : α) (k : ℕ)
    (h : ∀ i, windowSum (classMask word X) 1 (r * s) i = k)
    (he : (s : ℤ) * (∑ i, classMask word X i) -
      (d : ℤ) * windowSum (classMask word X) 1 (r * s - 1) 0 = d) :
    word ((r * s - 1 : ℕ) : ZMod (r * d)) = X := by
  rw [omitted_phase_defect hr hs _ k h] at he
  by_contra hn
  simp only [classMask, hn, ite_false, Nat.cast_zero, mul_zero] at he
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  omega

/-- Distinct exposed classes cannot both have constant windows and full defect.
The contradiction is one actual word position, not an independence assumption. -/
theorem no_two_full_defect_classes {α : Type*} [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (word : ZMod (r * d) → α) (X Y : α) (hne : X ≠ Y) (kX kY : ℕ)
    (hX : ∀ i, windowSum (classMask word X) 1 (r * s) i = kX)
    (hY : ∀ i, windowSum (classMask word Y) 1 (r * s) i = kY)
    (eX : (s : ℤ) * (∑ i, classMask word X i) -
      (d : ℤ) * windowSum (classMask word X) 1 (r * s - 1) 0 = d)
    (eY : (s : ℤ) * (∑ i, classMask word Y i) -
      (d : ℤ) * windowSum (classMask word Y) 1 (r * s - 1) 0 = d) : False := by
  have hx := class_at_omitted_phase hr hd hs word X kX hX eX
  have hy := class_at_omitted_phase hr hd hs word Y kY hY eY
  exact hne (hx.symm.trans hy)

end SkewCornerDescent.PhaseInventory
