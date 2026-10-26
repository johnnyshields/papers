/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.CapRecognition.Main

/-!
# Support and corner data of the numerator

The `z`-support of the numerator is the set of column labels, its `h`-labels are bounded by
`X_1`, and the derivative in the top label is `± aux`.  These are the invariants from which a
scalar multiple of the numerator is read back to the cap.  Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence MvPolynomial

theorem coefZ_C_mul (q : ℚ) (k : ℕ) (p : J) : coefZ k (C q * p) = C q * coefZ k p := by
  have h : φ (C q : J) = Polynomial.C (C q : CompleteRing) := by
    have := φ.commutes q
    simpa [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] using this
  simp only [coefZ, map_mul, h, Polynomial.coeff_C_mul]

namespace WeakCap

section
variable {r : ℕ} (c : WeakCap r)

theorem coefZ_num_eq_zero {k : ℕ} (hk : ∀ p, k ≠ (c.cols p).toNat) : coefZ k c.num = 0 := by
  rw [num_eq_sum, coefZ_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [coefZ_zpow_mul]
  exact ite_eq_right_iff.mpr fun h => absurd h (hk p)

theorem support_num : (φ c.num).support = Finset.univ.image fun p => (c.cols p).toNat := by
  ext k
  rw [Polynomial.mem_support_iff, Finset.mem_image]
  constructor
  · intro h
    by_contra hne
    simp only [not_exists, not_and] at hne
    exact h (c.coefZ_num_eq_zero fun p => fun h => hne p (Finset.mem_univ p) h.symm)
  · rintro ⟨p, -, rfl⟩
    have := c.coefZ_num p
    simp only [coefZ] at this
    rw [this]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (c.minor_ne_zero p)

theorem card_support_num : (φ c.num).support.card = r + 1 := by
  rw [support_num, Finset.card_image_of_injective _ c.cols_toNat_injective]
  simp

end

theorem num_zero (c : WeakCap 0) : c.num = 1 := by
  unfold num
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_one]
  have h0 : (0 : Fin (0 + 1)) = Fin.last 0 := rfl
  rw [h0, Zb_last, cols_last]
  simp

theorem detA_zero (c : WeakCap 0) : c.detA = 1 := by
  unfold detA
  exact Matrix.det_isEmpty

variable {m : ℕ} (c : WeakCap (m + 1))

theorem pderiv_num {k : ℤ} (hk : 0 < k) (hkX : k = c.X 0) :
    pderiv (lvar k hk) c.num = (-1 : J) ^ (m + 1) * c.aux := by
  subst hkX
  have hsplit : c.num = c.rest +
      (-1 : J) ^ (m + 1) * MvPolynomial.X (lvar (c.X 0) hk) * c.aux := by
    rw [c.num_split, hJ_eq_X hk]
  rw [hsplit]
  exact pderiv_split _ (c.rest_noLabel.notMem hk) (c.aux_noLabel_X0.notMem hk)

theorem num_noLabel {k : ℤ} (hk : c.X 0 < k) : NoLabel c.num k := by
  refine Zb_det_noLabel _ _ fun i p => ?_
  have h1 : c.X i ≤ c.X 0 := c.X_anti.antitone (Fin.zero_le i)
  have := c.cols_nonneg p
  omega

end WeakCap

end SkewCoframeRigidity.CapRecognition
