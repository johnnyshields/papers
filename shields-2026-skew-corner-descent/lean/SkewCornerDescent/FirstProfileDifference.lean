/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Opposite first endpoint-profile differences

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Equal
product coefficients force the first two profile differences to be opposite;
only the coefficients strictly before that degree must agree. Sorry-free.
-/

namespace SkewCornerDescent

open scoped BigOperators

/-- At the first possible nonzero degree of one factor, convolution sees only
the constant coefficient of its other factor. -/
theorem first_nonzero_mul_coeff {F : Type*} [CommRing F]
    (f g : PowerSeries F) (w : ℕ)
    (hf : ∀ k < w, PowerSeries.coeff k f = 0) :
    PowerSeries.coeff w (f * g) = PowerSeries.coeff w f * PowerSeries.constantCoeff g := by
  classical
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (w, 0)]
  · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rintro ⟨i, j⟩ hij hne
    have hs := Finset.mem_antidiagonal.mp hij
    have hi : i < w := by
      by_contra h
      have he : i = w ∧ j = 0 := by omega
      exact hne (Prod.ext he.1 he.2)
    rw [hf i hi, zero_mul]
  · intro h
    exact (h (Finset.mem_antidiagonal.mpr (Nat.add_zero w))).elim

/-- Normalized endpoint profiles with identical earlier coefficients and the
same product at the first differing degree have opposite first differences. -/
theorem first_profile_differences_opposite {F : Type*} [CommRing F]
    (A B C D : PowerSeries F) (w : ℕ)
    (hA0 : PowerSeries.constantCoeff A = 1) (hD0 : PowerSeries.constantCoeff D = 1)
    (hleft : ∀ k < w, PowerSeries.coeff k A = PowerSeries.coeff k C)
    (hright : ∀ k < w, PowerSeries.coeff k B = PowerSeries.coeff k D)
    (hprod : PowerSeries.coeff w (A * B) = PowerSeries.coeff w (C * D)) :
    PowerSeries.coeff w (A - C) = -PowerSeries.coeff w (B - D) := by
  have hL : ∀ k < w, PowerSeries.coeff k (A - C) = 0 := by
    intro k hk
    rw [map_sub, hleft k hk, sub_self]
  have hR : ∀ k < w, PowerSeries.coeff k (B - D) = 0 := by
    intro k hk
    rw [map_sub, hright k hk, sub_self]
  have he : A * B - C * D = (A - C) * D + (B - D) * A := by ring
  have h := congrArg (PowerSeries.coeff w) he
  rw [map_sub, hprod, sub_self, map_add,
    first_nonzero_mul_coeff (A - C) D w hL,
    first_nonzero_mul_coeff (B - D) A w hR, hA0, hD0, mul_one, mul_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end SkewCornerDescent
