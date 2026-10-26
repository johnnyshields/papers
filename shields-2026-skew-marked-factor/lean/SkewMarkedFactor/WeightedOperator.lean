/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.PowerCoordinates

/-!
# The weighted derivations

«Weighted composition covariance» (`sec:weighted-action`,
`eq:weighted-operator`) of `shields-2026-skew-marked-factor.tex`.
The derivation `V_k = Σ_{j ≥ 1} j h_j ∂/∂h_{j+k}` is defined on the actual
polynomial ring `Λ = ℚ[h₁, h₂, …]` by its values on the generators, and its action on
the Newton power sums is computed from the generating-series relation.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

/-- The weighted derivation `V_k` (`eq:weighted-operator`): `V_k h_m = (m - k) h_{m-k}`,
so `V_k` kills `h_k` and every `h_m` with `m < k`. -/
def wDeriv (k : ℕ) : Derivation ℚ Lambda Lambda :=
  MvPolynomial.mkDerivation ℚ fun m : ℕ+ => C (((m : ℕ) : ℚ) - k) * hh ((m : ℤ) - k)

theorem wDeriv_X (k : ℕ) (m : ℕ+) :
    wDeriv k (X m) = C (((m : ℕ) : ℚ) - k) * hh ((m : ℤ) - k) := by
  unfold wDeriv
  exact MvPolynomial.mkDerivation_X ℚ _ m

theorem wDeriv_hPos (k : ℕ) {m : ℕ} (hm : 0 < m) :
    wDeriv k (hPos m) = if k < m then ((m : Lambda) - k) * hPos (m - k) else 0 := by
  have h1 : hPos m = (X (⟨m, hm⟩ : ℕ+) : Lambda) := hPos_pnat ⟨m, hm⟩
  rw [h1, wDeriv_X (m := ⟨m, hm⟩)]
  by_cases hk : k < m
  · simp only [hk, ↓reduceIte]
    have hc : ((m : ℤ) - k) = ((m - k : ℕ) : ℤ) := by omega
    simp only [PNat.mk_coe]
    rw [hc, hh_natCast]
    simp [map_sub]
  · simp only [hk, ↓reduceIte]
    by_cases hkm : k = m
    · subst hkm; simp
    · have : ((m : ℤ) - k) < 0 := by omega
      simp [hh_of_neg this]

theorem coeffDeriv_wDeriv_hSeries (k : ℕ) :
    coeffDeriv (wDeriv k) hSeries =
      PowerSeries.X ^ (k + 1) * PowerSeries.derivative hSeries := by
  ext n
  rw [coeff_coeffDeriv, PowerSeries.coeff_X_pow_mul']
  unfold hSeries
  rw [PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hPos, Derivation.map_one_eq_zero]
  · rw [wDeriv_hPos k hn]
    by_cases hkn : k + 1 ≤ n
    · simp only [hkn, (by omega : k < n), ↓reduceIte]
      rw [ PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
      have : n - (k + 1) + 1 = n - k := by omega
      rw [this]
      have e : ((n - (k + 1) : ℕ) : Lambda) + 1 = ((n : Lambda) - k) := by
        have : ((n - (k + 1) : ℕ) : Lambda) = (n : Lambda) - k - 1 := by
          rw [Nat.cast_sub hkn]; push_cast; ring
        rw [this]; ring
      rw [e, mul_comm]
    · have hnk : ¬ k < n := by omega
      simp [hkn, hnk]

/-- The action on the Newton power sums: `V_k p_n = n p_{n-k}` for `n > k`, and zero
otherwise. -/
theorem wDeriv_pPoly (k n : ℕ) :
    wDeriv k (pPoly n) = if k < n then (n : Lambda) * pPoly (n - k) else 0 := by
  have hH := coeffDeriv_wDeriv_hSeries k
  have hN := newtonSeries_mul_hSeries
  have h1 := congrArg (coeffDeriv (wDeriv k)) hN
  rw [coeffDeriv_mul, coeffDeriv_mul, coeffDeriv_X, mul_zero, add_zero,
    coeffDeriv_derivative, hH] at h1
  have hX : PowerSeries.X * PowerSeries.derivative hSeries = newtonSeries * hSeries := hN.symm
  have hD : PowerSeries.derivative (PowerSeries.X ^ (k + 1) * PowerSeries.derivative hSeries) =
      ((k + 1 : ℕ) : PowerSeries Lambda) * PowerSeries.X ^ k * PowerSeries.derivative hSeries +
        PowerSeries.X ^ (k + 1) * PowerSeries.derivative (PowerSeries.derivative hSeries) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_X]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
    simp only [Nat.add_sub_cancel]
    ring
  have hP := congrArg PowerSeries.derivative hN
  rw [Derivation.leibniz, Derivation.leibniz, PowerSeries.derivative_X] at hP
  simp only [smul_eq_mul, mul_one] at hP
  rw [hD] at h1
  have hWH : hSeries * (coeffDeriv (wDeriv k) newtonSeries -
      ((k : PowerSeries Lambda) * PowerSeries.X ^ k * newtonSeries +
      PowerSeries.X ^ (k + 1) * PowerSeries.derivative newtonSeries)) = 0 := by
    push_cast at h1
    linear_combination h1 - PowerSeries.X ^ (k + 1) * hP +
      (k : PowerSeries Lambda) * PowerSeries.X ^ k * hX
  have hE := eSeries_mul_hSeries
  have hW : coeffDeriv (wDeriv k) newtonSeries =
      (k : PowerSeries Lambda) * PowerSeries.X ^ k * newtonSeries +
      PowerSeries.X ^ (k + 1) * PowerSeries.derivative newtonSeries := by
    have := congrArg (fun x => eSeries * x) hWH
    simp only [← mul_assoc, hE, one_mul, mul_zero] at this
    exact sub_eq_zero.mp this
  have hc := congrArg (PowerSeries.coeff n) hW
  rw [coeff_coeffDeriv, mul_assoc, map_add, PowerSeries.coeff_natCast_mul] at hc
  rw [PowerSeries.coeff_X_pow_mul'] at hc
  have hd : ∀ j, PowerSeries.coeff j (PowerSeries.derivative newtonSeries) =
      pPoly (j + 1) * (j + 1 : ℕ) := by
    intro j; rw [PowerSeries.coeff_derivative]; simp [newtonSeries]
  rcases lt_trichotomy k n with hkn | rfl | hkn
  · have : PowerSeries.coeff n (PowerSeries.X ^ (k + 1) * PowerSeries.derivative newtonSeries)
        = (n - k : ℕ) * pPoly (n - k) := by
      rw [PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega), hd]
      have : n - (k + 1) + 1 = n - k := by omega
      rw [this, mul_comm]
    rw [this, ite_eq_left (le_of_lt hkn)] at hc
    simp only [newtonSeries, PowerSeries.coeff_mk] at hc
    rw [hc, ite_eq_left hkn, Nat.cast_sub hkn.le]
    ring
  · have h0 : pPoly 0 = 0 := by rw [pPoly]
    have : PowerSeries.coeff k (PowerSeries.X ^ (k + 1) * PowerSeries.derivative newtonSeries)
        = 0 := by
      rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
    rw [this] at hc
    simp only [newtonSeries, PowerSeries.coeff_mk, le_refl, ↓reduceIte, Nat.sub_self, h0] at hc
    simpa using hc
  · have : PowerSeries.coeff n (PowerSeries.X ^ (k + 1) * PowerSeries.derivative newtonSeries)
        = 0 := by
      rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
    rw [this, ite_eq_right (by omega)] at hc
    simp only [newtonSeries, PowerSeries.coeff_mk] at hc
    rw [ite_eq_right (by omega)]
    simpa using hc


theorem wDeriv_neg_one_pow (n k : ℕ) : wDeriv n ((-1 : Lambda) ^ k) = 0 := by
  rw [Derivation.leibniz_pow, map_neg, Derivation.map_one_eq_zero]; simp

theorem coeffDeriv_wDeriv_eSeries (k : ℕ) :
    coeffDeriv (wDeriv k) eSeries =
      PowerSeries.X ^ (k + 1) * PowerSeries.derivative eSeries := by
  have h1 := congrArg (coeffDeriv (wDeriv k)) eSeries_mul_hSeries
  rw [coeffDeriv_mul, coeffDeriv_one, coeffDeriv_wDeriv_hSeries] at h1
  have hEH := eSeries_mul_hSeries
  have hd := congrArg PowerSeries.derivative hEH
  rw [Derivation.leibniz, Derivation.map_one_eq_zero] at hd
  simp only [smul_eq_mul] at hd
  linear_combination eSeries * h1 + (-(coeffDeriv (wDeriv k) eSeries
    - PowerSeries.X ^ (k + 1) * PowerSeries.derivative eSeries)) * hEH
    - eSeries * PowerSeries.X ^ (k + 1) * hd

/-- `V_k e_m = (-1)^k (m - k) e_{m-k}` for `m > k`, and zero otherwise. -/
theorem wDeriv_elem (k m : ℕ) :
    wDeriv k (elem m) = if k < m then (-1) ^ k * ((m : Lambda) - k) * elem (m - k) else 0 := by
  have h := congrArg (PowerSeries.coeff m) (coeffDeriv_wDeriv_eSeries k)
  rw [coeff_coeffDeriv, PowerSeries.coeff_X_pow_mul'] at h
  unfold eSeries at h
  rw [PowerSeries.coeff_mk, Derivation.leibniz, wDeriv_neg_one_pow] at h
  simp only [smul_eq_mul, mul_zero, add_zero] at h
  have hsq : ((-1 : Lambda) ^ m) * (-1) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  by_cases hkm : k + 1 ≤ m
  · have hk : k < m := by omega
    simp only [hkm, hk, ↓reduceIte] at h ⊢
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk] at h
    have e : m - (k + 1) + 1 = m - k := by omega
    rw [e] at h
    have hc : ((m - (k + 1) : ℕ) : Lambda) + 1 = (m : Lambda) - k := by
      rw [Nat.cast_sub hkm]; push_cast; ring
    rw [hc] at h
    obtain ⟨j, rfl⟩ : ∃ j, m = k + j + 1 := ⟨m - k - 1, by omega⟩
    have e2 : k + j + 1 - k = j + 1 := by omega
    rw [e2] at h ⊢
    have hj : ((-1 : Lambda) ^ (j + 1)) * (-1) ^ (j + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    have hm : (-1 : Lambda) ^ (k + j + 1) = (-1) ^ k * (-1) ^ (j + 1) := by
      rw [← pow_add, add_assoc]
    rw [hm] at h hsq
    linear_combination ((-1 : Lambda) ^ k * (-1) ^ (j + 1)) * h
      - (wDeriv k (elem (k + j + 1))) * hsq
      + ((-1 : Lambda) ^ k * ((((k + j + 1 : ℕ) : Lambda) - k)) * elem (j + 1)) * hj
  · have hk : ¬ k < m := by omega
    simp only [hkm, hk, ↓reduceIte] at h ⊢
    linear_combination ((-1 : Lambda) ^ m) * h - (wDeriv k (elem m)) * hsq

theorem wDeriv_elem_pnat (k : ℕ) (i : ℕ+) :
    wDeriv k (elem i) = (-1) ^ k * C (((i : ℕ) : ℚ) - k) * schurInvolution (hh ((i : ℤ) - k)) := by
  rw [wDeriv_elem]
  by_cases hk : k < (i : ℕ)
  · have hc : ((i : ℤ) - k) = (((i : ℕ) - k : ℕ) : ℤ) := (Nat.cast_sub hk.le).symm
    rw [hc, hh_natCast, schurInvolution_hPos]
    simp only [hk, ↓reduceIte]
    have : (C (((i : ℕ) : ℚ) - k) : Lambda) = ((i : ℕ) : Lambda) - k := by
      simp [map_sub]
    rw [this]
  · simp only [hk, ↓reduceIte]
    rcases Nat.lt_or_ge (i : ℕ) k with h2 | h2
    · have hi : (i : ℤ) - k < 0 := by omega
      rw [hh_of_neg hi]; simp
    · have h3 : (i : ℕ) = k := by omega
      simp [h3]

/-- **`V_n ∘ ι = (-1)^n ι ∘ V_n`** (`eq:physical-operator-transport`). -/
theorem wDeriv_schurInvolution (n : ℕ) (f : Lambda) :
    wDeriv n (schurInvolution f) = (-1) ^ n * schurInvolution (wDeriv n f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h1 : schurInvolution (MvPolynomial.C a) = MvPolynomial.C a := by
      rw [← MvPolynomial.algebraMap_eq]; exact AlgHom.commutes _ a
    have h2 : wDeriv n (MvPolynomial.C a : Lambda) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ a
    rw [h1, h2, map_zero, mul_zero]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, map_add, hp, hq, mul_add]
  | mul_X p i hp =>
    rw [map_mul, schurInvolution_X, Derivation.leibniz, hp, wDeriv_elem_pnat,
      Derivation.leibniz, wDeriv_X]
    have hC : ∀ a : ℚ, schurInvolution (C a : Lambda) = C a := fun a => by
      rw [← MvPolynomial.algebraMap_eq]; exact AlgHom.commutes _ _
    simp only [smul_eq_mul, map_mul, map_add, schurInvolution_X, map_sub, hC]
    ring

/-- The operator `B_k = p V_k + ρ δ_k` of the mixed readout, for a period `p` and
phase difference `ρ`. -/
def mixedOp (p ρ : ℚ) (k : ℕ) : Derivation ℚ Lambda Lambda :=
  p • wDeriv k + ρ • pDeriv k

theorem mixedOp_apply (p ρ : ℚ) (k : ℕ) (f : Lambda) :
    mixedOp p ρ k f = C p * wDeriv k f + C ρ * pDeriv k f := by
  simp [mixedOp, MvPolynomial.smul_eq_C_mul]

/-- `B_k h_j = (p (j - k) + ρ) h_{j-k}` for `j ≥ k ≥ 1`, and zero for `j < k`. -/
theorem mixedOp_hPos (p ρ : ℚ) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    mixedOp p ρ k (hPos j) =
      if k ≤ j then C (p * ((j : ℚ) - k) + ρ) * hPos (j - k) else 0 := by
  rw [mixedOp_apply, pDeriv_hPos hk]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have : ¬ k ≤ 0 := by omega
    simp [hPos, this, Derivation.map_one_eq_zero]
  · rw [wDeriv_hPos k hj]
    by_cases hkj : k < j
    · simp only [hkj, hkj.le, ↓reduceIte]
      simp only [map_add, map_mul, map_sub, map_natCast]
      ring
    · by_cases hkj' : k = j
      · subst hkj'; simp [hPos]
      · simp [hkj, show ¬ k ≤ j by omega]

/-- `B_k e_j = (-1)^{k-1} (ρ - p (j - k)) e_{j-k}` for `j ≥ k ≥ 1`, and zero for `j < k`. -/
theorem mixedOp_elem (p ρ : ℚ) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    mixedOp p ρ k (elem j) =
      if k ≤ j then (-1) ^ (k - 1) * C (ρ - p * ((j : ℚ) - k)) * elem (j - k) else 0 := by
  rw [mixedOp_apply, pDeriv_elem hk, wDeriv_elem]
  by_cases hkj : k < j
  · simp only [hkj, hkj.le, ↓reduceIte]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, map_sub, map_mul, map_natCast, pow_succ]
    ring
  · by_cases hkj' : k = j
    · subst hkj'
      simp only [lt_irrefl, le_refl, ↓reduceIte]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [elem]
      exact mul_comm _ _
    · simp [hkj, show ¬ k ≤ j by omega]

end SkewMarkedFactor
