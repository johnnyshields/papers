-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/Involution.lean
import GluingCore.OlsonHarris.Plan.Defs

/-!
# The involution and the derivations `p_n^⊥`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the identity `ω(f[p_k]) = (-1)^{m(k-1)} ω(f)[p_k]` used in
thesis Thm. 5.4.9 (`OlsonHarris2024HopfApplications`), in the form
`p_n^⊥ (ι f) = (-1)^{n-1} ι (p_n^⊥ f)` for `n ≥ 1`.

The coefficientwise derivative of power series is a derivation; applied to `Σ h_k t^k` it gives
`t^n Σ h_k t^k`, and `Σ (-1)^k e_k t^k` is the inverse series, hence is multiplied by `-t^n`.

Sorry-free.
-/

namespace GluingCore

namespace Plan


/-- The coefficientwise application of a derivation to a power series. -/
noncomputable def coeffDeriv (D : Derivation ℚ Lambda Lambda) (f : PowerSeries Lambda) :
    PowerSeries Lambda :=
  PowerSeries.mk fun k => D (PowerSeries.coeff k f)

theorem coeff_coeffDeriv (D : Derivation ℚ Lambda Lambda) (f : PowerSeries Lambda) (k : ℕ) :
    PowerSeries.coeff k (coeffDeriv D f) = D (PowerSeries.coeff k f) := by
  unfold coeffDeriv; rw [PowerSeries.coeff_mk]

theorem coeffDeriv_mul (D : Derivation ℚ Lambda Lambda) (f g : PowerSeries Lambda) :
    coeffDeriv D (f * g) = f * coeffDeriv D g + g * coeffDeriv D f := by
  ext k
  rw [coeff_coeffDeriv, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    PowerSeries.coeff_mul, map_sum]
  have h1 : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      D (PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g) =
      PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 (coeffDeriv D g) +
        PowerSeries.coeff p.2 g * PowerSeries.coeff p.1 (coeffDeriv D f) := by
    intro p _
    rw [Derivation.leibniz, coeff_coeffDeriv, coeff_coeffDeriv]
    simp only [smul_eq_mul]
  have h2 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      PowerSeries.coeff p.2 g * PowerSeries.coeff p.1 (coeffDeriv D f) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 (coeffDeriv D f) :=
    Finset.Nat.sum_antidiagonal_swap
      (f := fun p => PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 (coeffDeriv D f))
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2]

theorem coeffDeriv_one (D : Derivation ℚ Lambda Lambda) : coeffDeriv D 1 = 0 := by
  ext k
  rw [coeff_coeffDeriv, PowerSeries.coeff_one]
  split_ifs <;> simp

/-- `Σ h_k t^k`. -/
noncomputable def hSeries : PowerSeries Lambda := PowerSeries.mk fun k => hPos k

/-- `Σ (-1)^k e_k t^k`. -/
noncomputable def eSeries : PowerSeries Lambda := PowerSeries.mk fun k => (-1) ^ k * elem k

theorem eSeries_mul_hSeries : eSeries * hSeries = 1 := by
  ext k
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i eSeries * PowerSeries.coeff j hSeries) k]
  unfold eSeries hSeries
  simp only [PowerSeries.coeff_mk]
  by_cases hk : k = 0
  · subst hk; simp [elem, hPos]
  · simp only [hk, ↓reduceIte]
    have := altConv_elem_hPos k (Nat.pos_of_ne_zero hk)
    unfold altConv at this
    rw [← this]

theorem pDeriv_hPos {n : ℕ} (hn : 0 < n) (k : ℕ) :
    pDeriv n (hPos k) = if n ≤ k then hPos (k - n) else 0 := by
  by_cases hk : 0 < k
  · have h : pDeriv n (hPos k) = hh ((k : ℤ) - n) := by
      have h1 := hPos_pnat (⟨k, hk⟩ : ℕ+)
      have h2 := pDeriv_X n (⟨k, hk⟩ : ℕ+)
      simp only [PNat.mk_coe] at h1 h2
      rw [h1]; exact h2
    rw [h]
    by_cases hnk : n ≤ k
    · simp only [hnk, ↓reduceIte]
      have : (k : ℤ) - n = ((k - n : ℕ) : ℤ) := by omega
      rw [this, hh_natCast]
    · simp only [hnk, ↓reduceIte]
      exact hh_of_neg (by omega)
  · obtain rfl : k = 0 := by omega
    have : ¬ n ≤ 0 := by omega
    simp [this, hPos]

theorem coeffDeriv_hSeries {n : ℕ} (hn : 0 < n) :
    coeffDeriv (pDeriv n) hSeries = PowerSeries.X ^ n * hSeries := by
  ext k
  rw [coeff_coeffDeriv, PowerSeries.coeff_X_pow_mul']
  unfold hSeries
  rw [PowerSeries.coeff_mk, pDeriv_hPos hn]
  split_ifs <;> simp [PowerSeries.coeff_mk]

theorem coeffDeriv_eSeries {n : ℕ} (hn : 0 < n) :
    coeffDeriv (pDeriv n) eSeries = -(PowerSeries.X ^ n * eSeries) := by
  have h1 := congrArg (coeffDeriv (pDeriv n)) eSeries_mul_hSeries
  rw [coeffDeriv_mul, coeffDeriv_one, coeffDeriv_hSeries hn] at h1
  have hEH := eSeries_mul_hSeries
  linear_combination eSeries * h1 + (-(coeffDeriv (pDeriv n) eSeries +
    PowerSeries.X ^ n * eSeries)) * hEH

theorem pDeriv_neg_one_pow (n k : ℕ) : pDeriv n ((-1 : Lambda) ^ k) = 0 := by
  rw [Derivation.leibniz_pow, map_neg, Derivation.map_one_eq_zero]; simp

theorem pDeriv_elem {n : ℕ} (hn : 0 < n) (k : ℕ) :
    pDeriv n (elem k) = if n ≤ k then (-1) ^ (n - 1) * elem (k - n) else 0 := by
  have h := congrArg (PowerSeries.coeff k) (coeffDeriv_eSeries hn)
  rw [coeff_coeffDeriv, map_neg, PowerSeries.coeff_X_pow_mul'] at h
  unfold eSeries at h
  rw [PowerSeries.coeff_mk, Derivation.leibniz, pDeriv_neg_one_pow] at h
  simp only [smul_eq_mul, mul_zero, add_zero] at h
  have hsq : ((-1 : Lambda) ^ k) * (-1) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  by_cases hnk : n ≤ k
  · simp only [hnk, ↓reduceIte] at h ⊢
    rw [PowerSeries.coeff_mk] at h
    have e1 : pDeriv n (elem k) = -((-1) ^ k * ((-1) ^ (k - n) * elem (k - n))) := by
      linear_combination ((-1 : Lambda) ^ k) * h - (pDeriv n (elem k)) * hsq
    rw [e1]
    obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have e2 : n' + 1 + j - (n' + 1) = j := by omega
    have e3 : n' + 1 - 1 = n' := by omega
    rw [e2, e3]
    have hj : ((-1 : Lambda) ^ j) * (-1) ^ j = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    have : (-1 : Lambda) ^ (n' + 1 + j) = (-1) ^ n' * (-1) * (-1) ^ j := by
      rw [pow_add, pow_succ]
    rw [this]
    linear_combination (((-1 : Lambda) ^ n') * elem j) * hj
  · simp only [hnk, ↓reduceIte] at h ⊢
    linear_combination ((-1 : Lambda) ^ k) * h - (pDeriv n (elem k)) * hsq

theorem pDeriv_elem_pnat {n : ℕ} (hn : 0 < n) (i : ℕ+) :
    pDeriv n (elem i) = (-1) ^ (n - 1) * schurInvolution (hh ((i : ℤ) - n)) := by
  rw [pDeriv_elem hn]
  by_cases hni : n ≤ (i : ℕ)
  · have : ((i : ℕ+) : ℤ) - n = (((i : ℕ) - n : ℕ) : ℤ) := by omega
    rw [this, hh_natCast, schurInvolution_hPos]
    simp only [hni, ↓reduceIte]
  · rw [hh_of_neg (by omega)]
    simp only [hni, ↓reduceIte, map_zero, mul_zero]

/-- **`p_n^⊥ ∘ ι = (-1)^{n-1} ι ∘ p_n^⊥`** for `n ≥ 1`. -/
theorem pDeriv_schurInvolution {n : ℕ} (hn : 0 < n) (f : Lambda) :
    pDeriv n (schurInvolution f) = (-1) ^ (n - 1) * schurInvolution (pDeriv n f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h1 : schurInvolution (MvPolynomial.C a) = MvPolynomial.C a := by
      rw [← MvPolynomial.algebraMap_eq]; exact AlgHom.commutes _ a
    have h2 : pDeriv n (MvPolynomial.C a : Lambda) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ a
    rw [h1, h2, map_zero, mul_zero]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, map_add, hp, hq, mul_add]
  | mul_X p i hp =>
    rw [map_mul, schurInvolution_X, Derivation.leibniz, hp, pDeriv_elem_pnat hn,
      Derivation.leibniz, pDeriv_X]
    simp only [smul_eq_mul, map_mul, map_add, schurInvolution_X]
    ring

end Plan

end GluingCore
