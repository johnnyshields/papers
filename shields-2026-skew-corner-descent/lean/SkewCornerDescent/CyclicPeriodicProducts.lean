/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicGapPeriod

/-!
# Complete products of periodic cyclic windows

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every occurrence is retained, including repeated wraps. A full period product
is independent of its starting position, without an invertibility assumption
on individual letters or a shorter-than-cycle restriction.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- A cyclic overlap period makes each complete period product independent of
its actual start. Commutativity preserves the rotated endpoint occurrence. -/
theorem windowProduct_of_zmod_period {B : ℕ} [NeZero B] {R : Type*} [CommMonoid R]
    (f : ZMod B → R) (r : ℕ) (hp : Function.Periodic f (r : ZMod B)) (i : ZMod B) :
    windowProduct f 1 r i = windowProduct f 1 r 0 := by
  have hslide (s : ZMod B) : windowProduct f 1 r (s + 1) = windowProduct f 1 r s := by
    cases r with
    | zero => simp only [windowProduct, Finset.range_zero, Finset.prod_empty]
    | succ k =>
      unfold windowProduct
      rw [Finset.prod_range_succ, Finset.prod_range_succ']
      simp only [nsmul_eq_mul, mul_one, Nat.cast_zero, add_zero]
      have hshift (a : ℕ) : s + 1 + (a : ZMod B) = s + ((a + 1 : ℕ) : ZMod B) := by
        push_cast
        ring
      simp_rw [hshift]
      rw [hp s, mul_comm]
  have hn (k : ℕ) : windowProduct f 1 r (k : ZMod B) = windowProduct f 1 r 0 := by
    induction k with
    | zero => simp only [Nat.cast_zero]
    | succ k ih => rw [Nat.cast_succ, hslide, ih]
  simpa only [ZMod.natCast_zmod_val] using hn i.val

/-- Repeated full period windows retain the exact full product power, with
all occurrences and starting positions kept. -/
theorem windowProduct_of_zmod_period_multiple {B : ℕ} [NeZero B] {R : Type*} [CommMonoid R]
    (f : ZMod B → R) (r : ℕ) (hp : Function.Periodic f (r : ZMod B)) (k : ℕ) (i : ZMod B) :
    windowProduct f 1 (k * r) i = windowProduct f 1 r 0 ^ k := by
  induction k generalizing i with
  | zero => simp only [zero_mul, windowProduct, Finset.range_zero, Finset.prod_empty, pow_zero]
  | succ k ih =>
    rw [Nat.succ_mul, windowProduct_add, ih,
      windowProduct_of_zmod_period f r hp (i + (k * r) • 1), pow_succ]

/-- One extra state contributes its actual first endpoint letter after the
complete period product. No cyclic position or repeated endpoint is dropped. -/
theorem windowProduct_of_zmod_period_multiple_succ {B : ℕ} [NeZero B]
    {R : Type*} [CommMonoid R] (f : ZMod B → R) (r : ℕ)
    (hp : Function.Periodic f (r : ZMod B)) (k : ℕ) (i : ZMod B) :
    windowProduct f 1 (k * r + 1) i = windowProduct f 1 r 0 ^ k * f i := by
  have hone (s : ZMod B) : windowProduct f 1 1 s = f s := by simp [windowProduct]
  rw [show k * r + 1 = 1 + k * r by omega, windowProduct_add, hone]
  simp only [one_nsmul]
  rw [windowProduct_of_zmod_period_multiple f r hp k (i + 1)]
  exact mul_comm _ _

end SkewCornerDescent.CyclicWindows
