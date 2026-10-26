/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalDerivative
import Mathlib.RingTheory.PowerSeries.Log

/-!
# Fresh-generator derivatives at the first normal order

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Earlier generator-independent coefficients remain independent under products.
At the first possible order, the complete convolution has only its two endpoint
contributions. No earlier product is replaced by its constant term without proof.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F M : Type*} [Field F] [Algebra ℚ F]
  [AddCommGroup M] [Module F M] [Module ℚ M]

/-- Product coefficients at a lower order contain no new generator derivative. -/
theorem coeff_deriv_mul_zero (D : Derivation ℚ F M) (p q : PowerSeries F) (n : ℕ)
    (hp : ∀ k, k ≤ n → D (PowerSeries.coeff k p) = 0)
    (hq : ∀ k, k ≤ n → D (PowerSeries.coeff k q) = 0) :
    D (PowerSeries.coeff n (p * q)) = 0 := by
  rw [PowerSeries.coeff_mul, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
  rw [Derivation.leibniz, hp j.1 (by omega), hq j.2 (by omega), smul_zero, smul_zero,
    add_zero]

/-- At the first generator-dependent order only the full endpoint factors contribute. -/
theorem coeff_deriv_mul_first (D : Derivation ℚ F M) (p q : PowerSeries F) (n : ℕ)
    (hp : ∀ k, k < n → D (PowerSeries.coeff k p) = 0)
    (hq : ∀ k, k < n → D (PowerSeries.coeff k q) = 0) :
    D (PowerSeries.coeff n (p * q)) =
      PowerSeries.constantCoeff p • D (PowerSeries.coeff n q) +
        PowerSeries.constantCoeff q • D (PowerSeries.coeff n p) := by
  rw [PowerSeries.coeff_mul, map_sum]
  simp only [Derivation.leibniz]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply Finset.sum_eq_single (0, n)
    · intro j hj hne
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
      have hk : j.2 < n := by
        by_contra h
        apply hne
        apply Prod.ext <;> omega
      rw [hq _ hk, smul_zero]
    · simp
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply Finset.sum_eq_single (n, 0)
    · intro j hj hne
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
      have hk : j.1 < n := by
        by_contra h
        apply hne
        apply Prod.ext <;> omega
      rw [hp _ hk, smul_zero]
    · simp

/-- Every coefficient through the given order of a complete finite product remains
generator-independent when its factors do. Repeated factors remain separate occurrences. -/
theorem coeff_deriv_prod_zero {ι : Type*} (D : Derivation ℚ F M)
    (s : Finset ι) (p : ι → PowerSeries F) (n : ℕ)
    (hp : ∀ i ∈ s, ∀ k, k ≤ n → D (PowerSeries.coeff k (p i)) = 0) :
    D (PowerSeries.coeff n (∏ i ∈ s, p i)) = 0 := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs <;> simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    apply coeff_deriv_mul_zero D _ _ n
    · exact hp i (Finset.mem_insert_self _ _)
    · intro k hk
      apply ih k
      intro j hj l hl
      exact hp j (Finset.mem_insert_of_mem hj) l (hl.trans hk)

/-- A finite product of generator-independent constants is generator-independent,
including repeated occurrences represented by distinct indices. -/
theorem deriv_prod_zero {ι : Type*} (D : Derivation ℚ F M)
    (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, D (f i) = 0) :
    D (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Derivation.leibniz,
      hf i (Finset.mem_insert_self _ _),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    simp

/-- With one potentially fresh occurrence, differentiation keeps the entire product
of all other occurrences. No diagonal response is canceled before normalization. -/
theorem deriv_prod_single {ι : Type*} [DecidableEq ι] (D : Derivation ℚ F M)
    (s : Finset ι) (f : ι → F) (i : ι) (hi : i ∈ s)
    (hf : ∀ k ∈ s, k ≠ i → D (f k) = 0) :
    D (∏ k ∈ s, f k) = (∏ k ∈ s.erase i, f k) • D (f i) := by
  classical
  rw [← Finset.mul_prod_erase s f hi, Derivation.leibniz,
    deriv_prod_zero D (s.erase i) f
      (fun k hk => hf k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)),
    smul_zero, zero_add]

/-- Powers preserve generator independence of every earlier coefficient. -/
theorem coeff_deriv_pow_zero (D : Derivation ℚ F M) (p : PowerSeries F) (n : ℕ)
    (hp : ∀ k, k ≤ n → D (PowerSeries.coeff k p) = 0) (a : ℕ) :
    D (PowerSeries.coeff n (p ^ a)) = 0 := by
  induction a generalizing n with
  | zero => simp only [pow_zero, PowerSeries.coeff_one]; split_ifs <;> simp
  | succ a ih =>
    rw [pow_succ]
    apply coeff_deriv_mul_zero D _ _ n
    · intro k hk
      exact ih k (fun l hl => hp l (hl.trans hk))
    · exact hp

/-- Higher powers of a zero-constant series cannot contribute the fresh derivative at its
first possible order. This is the nonlinear-term cancellation needed before logging. -/
theorem coeff_deriv_pow_first (D : Derivation ℚ F M) (p : PowerSeries F) (n : ℕ)
    (hn : 0 < n) (h0 : PowerSeries.constantCoeff p = 0)
    (hp : ∀ k, k < n → D (PowerSeries.coeff k p) = 0) (a : ℕ) :
    D (PowerSeries.coeff n (p ^ a)) = if a = 1 then D (PowerSeries.coeff n p) else 0 := by
  obtain (_ | _ | a) := a
  · simp [hn.ne']
  · simp
  · rw [pow_succ]
    rw [coeff_deriv_mul_first D _ _ n
      (fun k hk => coeff_deriv_pow_zero D p k (fun l hl => hp l (hl.trans_lt hk)) _) hp]
    simp [map_pow, h0]

end SkewCornerDescent.Matrix
