/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicWindows

/-!
# Integer maximum-window averages and actual cyclic periods

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). All windows
retain their actual positions and repeated wraps. Equality of an integer maximum
with the average forces every window to attain it, and supplies the gcd period.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- An integer uniform upper window bound is at least the exact average. -/
theorem integer_inventory_le_of_window_bound (f : G → ℤ) (step : G) (j : ℕ) (M : ℤ)
    (h : ∀ i, windowSum f step j i ≤ M) :
    (j : ℤ) * ∑ i, f i ≤ (Fintype.card G : ℤ) * M := by
  calc
    _ = ∑ i, windowSum f step j i := by
      simpa only [nsmul_eq_mul] using (sum_windowSum f step j).symm
    _ ≤ ∑ _i : G, M := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

/-- Equality of an integer maximum and its exact average leaves no smaller window. -/
theorem integer_windows_constant_of_maximum_eq_average (f : G → ℤ) (step : G) (j : ℕ) (M : ℤ)
    (h : ∀ i, windowSum f step j i ≤ M)
    (he : (j : ℤ) * ∑ i, f i = (Fintype.card G : ℤ) * M) :
    ∀ i, windowSum f step j i = M := by
  have hs : (∑ i, windowSum f step j i) = ∑ _i : G, M := by
    rw [sum_windowSum]
    simpa only [nsmul_eq_mul, Finset.sum_const, Finset.card_univ] using he
  have hall := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => h i)).mp hs
  exact fun i => hall i (Finset.mem_univ i)

/-- The exact integer equality branch supplies the actual gcd period without
assuming periodicity of the gap word. -/
theorem integer_zmod_period_of_maximum_eq_average {B : ℕ} [NeZero B]
    (f : ZMod B → ℤ) (j : ℕ) (M : ℤ)
    (h : ∀ i, windowSum f 1 j i ≤ M)
    (he : (j : ℤ) * ∑ i, f i = (B : ℤ) * M) :
    Function.Periodic f (Nat.gcd j B : ZMod B) := by
  have hall := integer_windows_constant_of_maximum_eq_average f 1 j M h (by simpa using he)
  have hp := periodic_of_constant_windows f 1 j M hall
  have hp' : Function.Periodic f (j : ZMod B) := by
    simpa only [nsmul_eq_mul, mul_one] using hp
  exact zmod_periodic_gcd f hp'

end SkewCornerDescent.CyclicWindows
