/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Noncancellation of exposed maximal poles

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original coefficients»
(`sec:dual`, `lem:peeling`). A real specialization of the actual polynomial ring detects the
leading cleared numerator. The terms attaining the largest pole have one sign; no independence
of the response coordinates is assumed. Sorry-free.
-/

namespace SkewCornerDescent

open scoped BigOperators

/-- Clearing a common maximal pole exponent retains every occurrence in the finite sum. -/
def clearedPoleSum {R ι : Type*} [CommRing R] (s : Finset ι) (p : R)
    (M : ℕ) (count : ι → ℕ) (u : ι → R) : R :=
  ∑ i ∈ s, p ^ (M - count i) * u i

/-- The cleared numerator is the exact original finite inverse-power sum, not a surrogate. -/
theorem clearedPoleSum_fraction {R F ι : Type*} [CommRing R] [Field F]
    (s : Finset ι) (p : R) (M : ℕ) (count : ι → ℕ) (u : ι → R)
    (φ : R →+* F) (hp : φ p ≠ 0) (hbound : ∀ i ∈ s, count i ≤ M) :
    φ (clearedPoleSum s p M count u) / φ p ^ M =
      ∑ i ∈ s, φ (u i) / φ p ^ count i := by
  rw [clearedPoleSum, map_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_pow, pow_sub₀ _ hp (hbound i hi)]
  field_simp [hp]

/-- At an exposed root, equally signed maximal terms cannot cancel. Specialization is applied
only to polynomials; no homomorphism from a rational function field into the reals is required. -/
theorem clearedPoleSum_eval_pos {R ι : Type*} [CommRing R] (s : Finset ι) (p : R)
    (M : ℕ) (count : ι → ℕ) (u : ι → R) (φ : R →+* ℝ) (σ : ℝ)
    (hp : φ p = 0) (hbound : ∀ i ∈ s, count i ≤ M)
    (hmax : ∃ i ∈ s, count i = M)
    (hsign : ∀ i ∈ s, count i = M → 0 < σ * φ (u i)) :
    0 < σ * φ (clearedPoleSum s p M count u) := by
  have hterm : ∀ i ∈ s, 0 ≤ σ * φ (p ^ (M - count i) * u i) := by
    intro i hi
    rw [map_mul, map_pow, hp]
    by_cases he : count i = M
    · simpa only [he, Nat.sub_self, pow_zero, one_mul] using (hsign i hi he).le
    · have hn : M - count i ≠ 0 := by have hb := hbound i hi; omega
      rw [zero_pow hn, zero_mul, mul_zero]
  obtain ⟨i, hi, hMi⟩ := hmax
  have hstrict : 0 < σ * φ (p ^ (M - count i) * u i) := by
    simpa only [map_mul, map_pow, hp, hMi, Nat.sub_self, pow_zero, one_mul]
      using hsign i hi hMi
  rw [clearedPoleSum, map_sum, Finset.mul_sum]
  exact Finset.sum_pos' hterm ⟨i, hi, hstrict⟩

/-- Every polynomial vanishing at the exposed root fails to divide the leading numerator. -/
theorem clearedPoleSum_not_dvd {R ι : Type*} [CommRing R] (s : Finset ι) (p : R)
    (M : ℕ) (count : ι → ℕ) (u : ι → R) (φ : R →+* ℝ) (σ : ℝ)
    (hp : φ p = 0) (hbound : ∀ i ∈ s, count i ≤ M)
    (hmax : ∃ i ∈ s, count i = M)
    (hsign : ∀ i ∈ s, count i = M → 0 < σ * φ (u i)) :
    ¬ p ∣ clearedPoleSum s p M count u := by
  have hpos := clearedPoleSum_eval_pos s p M count u φ σ hp hbound hmax hsign
  rintro ⟨a, ha⟩
  rw [ha, map_mul, hp, zero_mul, mul_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- The exposed leading numerator is nonzero even when its coefficients and responses depend
on one another in the original polynomial ring. -/
theorem clearedPoleSum_ne_zero {R ι : Type*} [CommRing R] (s : Finset ι) (p : R)
    (M : ℕ) (count : ι → ℕ) (u : ι → R) (φ : R →+* ℝ) (σ : ℝ)
    (hp : φ p = 0) (hbound : ∀ i ∈ s, count i ≤ M)
    (hmax : ∃ i ∈ s, count i = M)
    (hsign : ∀ i ∈ s, count i = M → 0 < σ * φ (u i)) :
    clearedPoleSum s p M count u ≠ 0 := by
  intro hzero
  exact clearedPoleSum_not_dvd s p M count u φ σ hp hbound hmax hsign (hzero ▸ dvd_zero p)

/-- Clearing the denominators of inverse response products gives a noncancelling leading
numerator in either exposure chamber. Equal residual lengths fix the negative-chamber sign. -/
theorem clearedInverseResponseSum_eval_pos {R ι κ : Type*} [CommRing R]
    (s : Finset ι) (t : Finset κ) (p a : R) (M L : ℕ) (count : ι → ℕ)
    (bound : κ → ℕ) (otherCount : ι → κ → ℕ) (num den : κ → R)
    (φ : R →+* ℝ) (sign : ℝ)
    (hp : φ p = 0) (ha : 0 < φ a)
    (hbound : ∀ i ∈ s, count i ≤ M) (hmax : ∃ i ∈ s, count i = M)
    (hnum : ∀ j ∈ t, 0 < sign * φ (num j))
    (hden : ∀ j ∈ t, 0 < φ (den j))
    (hlength : ∀ i ∈ s, count i = M → (∑ j ∈ t, (bound j - otherCount i j)) = L) :
    0 < sign ^ L * φ (clearedPoleSum s p M count
      (fun i => a ^ count i * ∏ j ∈ t, num j ^ (bound j - otherCount i j) *
        den j ^ otherCount i j)) := by
  apply clearedPoleSum_eval_pos s p M count _ φ (sign ^ L) hp hbound hmax
  intro i hi hMi
  have he : (∏ j ∈ t, (sign * φ (num j)) ^ (bound j - otherCount i j) *
      φ (den j) ^ otherCount i j) =
      sign ^ L * ∏ j ∈ t, φ (num j) ^ (bound j - otherCount i j) *
        φ (den j) ^ otherCount i j := by
    calc
      _ = ∏ j ∈ t, sign ^ (bound j - otherCount i j) *
          (φ (num j) ^ (bound j - otherCount i j) * φ (den j) ^ otherCount i j) := by
        apply Finset.prod_congr rfl
        intro j _
        rw [mul_pow]
        ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hlength i hi hMi]
  have hpos : 0 < φ a ^ count i *
      ∏ j ∈ t, (sign * φ (num j)) ^ (bound j - otherCount i j) *
        φ (den j) ^ otherCount i j :=
    mul_pos (pow_pos ha _) (Finset.prod_pos fun j hj =>
      mul_pos (pow_pos (hnum j hj) _) (pow_pos (hden j hj) _))
  rw [he] at hpos
  simpa only [map_mul, map_pow, map_prod, mul_left_comm] using hpos

/-- The signed specialization detects nondivisibility without independent response variables. -/
theorem clearedInverseResponseSum_not_dvd {R ι κ : Type*} [CommRing R]
    (s : Finset ι) (t : Finset κ) (p a : R) (M L : ℕ) (count : ι → ℕ)
    (bound : κ → ℕ) (otherCount : ι → κ → ℕ) (num den : κ → R)
    (φ : R →+* ℝ) (sign : ℝ)
    (hp : φ p = 0) (ha : 0 < φ a)
    (hbound : ∀ i ∈ s, count i ≤ M) (hmax : ∃ i ∈ s, count i = M)
    (hnum : ∀ j ∈ t, 0 < sign * φ (num j))
    (hden : ∀ j ∈ t, 0 < φ (den j))
    (hlength : ∀ i ∈ s, count i = M → (∑ j ∈ t, (bound j - otherCount i j)) = L) :
    ¬ p ∣ clearedPoleSum s p M count
      (fun i => a ^ count i * ∏ j ∈ t, num j ^ (bound j - otherCount i j) *
        den j ^ otherCount i j) := by
  have hpos := clearedInverseResponseSum_eval_pos s t p a M L count bound otherCount
    num den φ sign hp ha hbound hmax hnum hden hlength
  rintro ⟨a, ha⟩
  rw [ha, map_mul, hp, zero_mul, mul_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- The polynomial numerator used at an exposed root clears every response denominator of the
original inverse-product sum, including repeated factors and shared polynomial variables. -/
theorem clearedInverseResponseSum_fraction {R F ι κ : Type*} [CommRing R] [Field F]
    (s : Finset ι) (t : Finset κ) (p a : R) (M : ℕ) (count : ι → ℕ)
    (bound : κ → ℕ) (otherCount : ι → κ → ℕ) (num den : κ → R) (φ : R →+* F)
    (hp : φ p ≠ 0) (hnum : ∀ j ∈ t, φ (num j) ≠ 0)
    (hbound : ∀ i ∈ s, count i ≤ M)
    (hother : ∀ i ∈ s, ∀ j ∈ t, otherCount i j ≤ bound j) :
    φ (clearedPoleSum s p M count
      (fun i => a ^ count i * ∏ j ∈ t, num j ^ (bound j - otherCount i j) *
        den j ^ otherCount i j)) /
        (φ p ^ M * ∏ j ∈ t, φ (num j) ^ bound j) =
      ∑ i ∈ s, (φ a / φ p) ^ count i *
        ∏ j ∈ t, (φ (den j) / φ (num j)) ^ otherCount i j := by
  rw [div_mul_eq_div_div, clearedPoleSum_fraction s p M count _ φ hp hbound,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∏ j ∈ t, φ (num j) ^ (bound j - otherCount i j) *
      φ (den j) ^ otherCount i j) * (∏ j ∈ t, φ (num j) ^ bound j)⁻¹ =
      ∏ j ∈ t, (φ (den j) / φ (num j)) ^ otherCount i j := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [pow_sub₀ _ (hnum j hj) (hother i hi j hj), div_pow]
    field_simp [hnum j hj]
  simp only [map_mul, map_pow, map_prod]
  rw [div_pow]
  calc
    _ = (φ a ^ count i / φ p ^ count i) *
        ((∏ j ∈ t, φ (num j) ^ (bound j - otherCount i j) *
          φ (den j) ^ otherCount i j) * (∏ j ∈ t, φ (num j) ^ bound j)⁻¹) := by ring
    _ = _ := by rw [he]

/-- A regular rational response can be represented with a positive square denominator at a
real specialization. This changes neither the actual rational function nor its sign. -/
theorem normalizedResponseNumerator_pos {R : Type*} [CommRing R] (p q : R)
    (φ : R →+* ℝ) (sign : ℝ) (hq : φ q ≠ 0)
    (hs : 0 < sign * (φ p / φ q)) : 0 < sign * φ (p * q) := by
  have he : sign * φ (p * q) = φ q ^ 2 * (sign * (φ p / φ q)) := by
    rw [map_mul]
    field_simp [hq]
  rw [he]
  exact mul_pos (sq_pos_of_ne_zero hq) hs

end SkewCornerDescent
