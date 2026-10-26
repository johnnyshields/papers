/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.VacancyPulse

/-!
# Uniqueness of a vacancy-pulse tangent

A polynomial `R` over a field supported on the native columns `S` and the vacancies, with
`R_0 = 0`, `R` vanishing at every vacancy and `[U R]_{I i} = 0` at every proper row, is zero:
its native coefficients solve `T c = 0` for the invertible proper matrix `T`.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open Polynomial Matrix SkewCoframeRigidity.Coframe

variable {F : Type*} [Field F] {n m : ℕ}

/-- The coefficient of `[U R]` at `k` as a finite sum over the support of `R`. -/
theorem coeff_series_mul_poly (U : ℕ → F) (R : F[X]) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk U * (R : PowerSeries F)) =
      ∑ j ∈ R.support, R.coeff j * letterOf U ((k : ℤ) - j) := by
  conv_lhs => rw [R.as_sum_support]
  rw [show ((∑ j ∈ R.support, Polynomial.monomial j (R.coeff j) : F[X]) : PowerSeries F) =
    ∑ j ∈ R.support, ((Polynomial.monomial j (R.coeff j) : F[X]) : PowerSeries F) from
      map_sum (Polynomial.coeToPowerSeries.ringHom (R := F)) _ _, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, coeff_series_mul_C_monomial]

/-- **Uniqueness of the pulse tangent.** -/
theorem pulse_tangent_unique (U : ℕ → F) (I S : Fin n → ℕ) (hT : (properMat U I S).det ≠ 0)
    (hSinj : Function.Injective S) (bpos : Fin m → ℕ) (R : F[X])
    (hRsupp : ∀ j, R.coeff j ≠ 0 → (∃ s, j = S s) ∨ ∃ v, j = bpos v)
    (hRb : ∀ v, R.coeff (bpos v) = 0)
    (hRrows : ∀ i, PowerSeries.coeff (I i) (PowerSeries.mk U * (R : PowerSeries F)) = 0) :
    R = 0 := by
  classical
  have hnat : ∀ j, R.coeff j ≠ 0 → ∃ s, j = S s := by
    intro j hj
    rcases hRsupp j hj with h | ⟨v, hv⟩
    · exact h
    · exact absurd (hv ▸ hRb v) hj
  set c : Fin n → F := fun s => R.coeff (S s) with hc
  have hsum : ∀ k : ℕ, PowerSeries.coeff k (PowerSeries.mk U * (R : PowerSeries F)) =
      ∑ s, c s * letterOf U ((k : ℤ) - S s) := by
    intro k
    rw [coeff_series_mul_poly]
    have : ∑ j ∈ R.support, R.coeff j * letterOf U ((k : ℤ) - j) =
        ∑ j ∈ Finset.univ.image S, R.coeff j * letterOf U ((k : ℤ) - j) := by
      refine Finset.sum_subset_zero_on_sdiff ?_ ?_ (fun _ _ => rfl)
      · intro j hj
        obtain ⟨s, rfl⟩ := hnat j (Polynomial.mem_support_iff.mp hj)
        exact Finset.mem_image_of_mem _ (Finset.mem_univ s)
      · intro j hj
        rw [Polynomial.notMem_support_iff.mp (Finset.mem_sdiff.mp hj).2, zero_mul]
    rw [this, Finset.sum_image (fun a _ b _ h => hSinj h)]
  have hTc : properMat U I S *ᵥ c = 0 := by
    funext i
    have := hRrows i
    rw [hsum] at this
    simp only [properMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hc0 := Matrix.eq_zero_of_mulVec_eq_zero hT hTc
  ext j
  rw [Polynomial.coeff_zero]
  by_contra hne
  obtain ⟨s, rfl⟩ := hnat j hne
  exact hne (congrFun hc0 s)

end SkewCoframeRigidity.UnitRestoration
