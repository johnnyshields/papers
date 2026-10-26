/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicFiniteIntervals

/-!
# Exact window sums of periodic cyclic gap words

Supports `shields-2026-skew-corner-descent.tex`
(`lem:original-transfer`, `prop:normal-interface`).
Period sums retain all positions and do not divide by a possibly zero period.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- A cyclic period makes every window of that length have the same exact sum. -/
theorem windowSum_of_zmod_period {B : ℕ} [NeZero B] {R : Type*} [AddCommGroup R]
    (f : ZMod B → R) (r : ℕ) (hp : Function.Periodic f (r : ZMod B))
    (i : ZMod B) : windowSum f 1 r i = windowSum f 1 r 0 := by
  have hslide (s : ZMod B) : windowSum f 1 r (s + 1) = windowSum f 1 r s := by
    have hs := windowSum_slide f 1 r s
    simp only [nsmul_eq_mul, mul_one, hp s] at hs
    exact add_right_cancel hs
  have hn (n : ℕ) : windowSum f 1 r (n : ZMod B) = windowSum f 1 r 0 := by
    induction n with
    | zero => simp only [Nat.cast_zero]
    | succ n ih =>
      rw [Nat.cast_succ, hslide, ih]
  simpa only [ZMod.natCast_zmod_val] using hn i.val

/-- Every repeated period window is the exact multiple of one period sum, with
all wraps and all starting positions retained. -/
theorem windowSum_of_zmod_period_multiple {B : ℕ} [NeZero B] {R : Type*}
    [AddCommGroup R] (f : ZMod B → R) (r : ℕ)
    (hp : Function.Periodic f (r : ZMod B)) (k : ℕ) (i : ZMod B) :
    windowSum f 1 (k * r) i = k • windowSum f 1 r 0 := by
  induction k generalizing i with
  | zero => simp [windowSum]
  | succ k ih =>
    rw [Nat.succ_mul, windowSum_add, ih,
      windowSum_of_zmod_period f r hp (i + (k * r) • 1), succ_nsmul]

/-- A shorter complete window, even after adding the selected span, lies
strictly below a full period total. Every actual gap exceeds that span. -/
theorem windowSum_short_period_lt {B : ℕ} [NeZero B]
    (g : ZMod B → ℤ) (N r k length : ℕ)
    (hp : Function.Periodic g (r : ZMod B))
    (hg : ∀ i, (N : ℤ) < g i) (hlen : length < k * r) (i : ZMod B) :
    (N : ℤ) + windowSum g 1 length i < k • windowSum g 1 r 0 := by
  have hone (j : ZMod B) : windowSum g 1 1 j = g j := by simp [windowSum]
  have hstep := windowSum_add g 1 length 1 i
  rw [hone] at hstep
  have hsum := windowSum_of_zmod_period_multiple g r hp k i
  have hsplit : k * r = length + 1 + (k * r - length - 1) := by omega
  rw [hsplit, windowSum_add, hstep] at hsum
  have hrem : 0 ≤ windowSum g 1 (k * r - length - 1) (i + (length + 1) • 1) := by
    unfold windowSum
    apply Finset.sum_nonneg
    intro j _
    exact le_of_lt (lt_of_le_of_lt (Int.natCast_nonneg N) (hg _))
  have hlast := hg (i + length • 1)
  omega

end SkewCornerDescent.CyclicWindows
