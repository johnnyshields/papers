/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.BinaryTransitions

/-!
# Exact energy of baseline-normalized binary profile coefficients

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
A common baseline cancels from cyclic differences. The complete squared
energy is the squared amplitude times the actual binary transition count;
the coprime weighted energy is nonzero for a nonconstant completed word.
Sorry-free.
-/

namespace SkewCornerDescent.BinaryTransitions
open scoped BigOperators

/-- Baseline-normalized binary differences give the exact cyclic square sum,
regardless of whether the physical baseline coefficient is zero. -/
theorem binary_profile_square_sum {F : Type*} [CommRing F] {n : ℕ} [NeZero n]
    (value : ZMod n → F) (base η : F) (bits : ZMod n → Bool)
    (hbits : ∀ i, value i - base = if bits i then η else 0) :
    ∑ i, (value i - value (i+1))^2 = η^2 * (transitionCount bits 1 : F) := by
  classical
  have he (i : ZMod n) : (value i - value (i+1))^2 =
      η^2 * (if bits i ≠ bits (i+1) then 1 else 0) := by
    have hd : value i - value (i+1) =
        (if bits i then η else 0) - (if bits (i+1) then η else 0) := by
      linear_combination hbits i - hbits (i+1)
    rw [hd]
    cases bits i <;> cases bits (i+1) <;> simp
  rw [Finset.sum_congr rfl (fun i _ => he i), ← Finset.mul_sum]
  congr 1
  simp [transitionCount, Nat.cast_sum]

/-- Coprimality and nonconstant completed bits rule out cancellation of the
weighted complete binary profile energy. No relation between the two words
and no extra nonconstancy assumption on the shorter word is needed. -/
theorem weighted_binary_profile_energy_ne_zero {F : Type*} [Field F] [CharZero F]
    {b d : ℕ} [NeZero b] [NeZero d] (hcop : Nat.Coprime b d)
    (P : ZMod d → Bool) (Q : ZMod b → Bool) (η : F) (hη : η ≠ 0)
    (hQ : ∃ i j, Q i ≠ Q j) :
    (1/2 : F) * η^2 *
      ((b : F) * transitionCount P 1 - (d : F) * transitionCount Q 1) ≠ 0 := by
  have hi := cyclic_curvature_ne_zero_of_nonconstant_closure hcop P Q hQ
  have hf : (b : F) * transitionCount P 1 - (d : F) * transitionCount Q 1 ≠ 0 := by
    exact_mod_cast hi
  exact mul_ne_zero (mul_ne_zero (div_ne_zero one_ne_zero (by norm_num))
    (pow_ne_zero 2 hη)) hf

end SkewCornerDescent.BinaryTransitions
