/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Boundary

/-!
# The order of the degree walls, and the boundary for every `κ ≥ 1`

`shields-2026-turan-bessel.tex`, `sec:phase` (`thm:two-parameter-coeff`,
`eq:pq-coefficients`, `eq:wall-slope-covariance`, `eq:qn-pn-ratio`,
`eq:q1-p1`, `eq:q-ratio-gap`, `eq:coefficient-wall-factor`).

`lem:boundary-positivity` (`Boundary`) settles `κ = 1`.  The `κ`-slope of the
degree-`n` wall is `-q_n/p_n`, so transporting it to every `κ ≥ 1` needs only
that degree one has the *least* such slope, which is `eq:q-ratio-gap`.  Both
inputs are elementary here:

    2q_n > n p_n           (`eq:qn-pn-ratio`)     `n_pRed_lt_two_qRed`
    q_1/p_1 < g/2          (`eq:q1-p1`)           `pRed_one`, `qRed_one`

The first is `Cov(K_n, α_{K_n}) < 0` with the probability language removed: the
reflection `k ↦ n-k` fixes the weight `s_ks_{n-k}`, so the antisymmetric part of
`α_k(n-2k)` is `(α_k - α_{n-k})(n-2k)/2`, which is nonnegative termwise because
`α_m = ψ₁(a+m)` decreases — and strictly positive at `k = 0`.

The conclusion is the whole `κ ≥ 1` half of `thm:two-parameter-coeff` at
coefficient level: nonnegative for `τ ≥ τ_cw`, strictly positive for `τ > τ_cw`,
and on `τ = τ_cw` the degree-one coefficient vanishes while every degree `n ≥ 2`
is strictly positive.

Sorry-free.
-/

namespace TuranBessel

variable {a κ τ : ℝ} {n : ℕ}

/-! ### `eq:qn-pn-ratio` -/

/-- **`eq:qn-pn-ratio`.**  `n p_n < 2 q_n` in the reduced weights, i.e.
`q_n/p_n > n/2`. -/
theorem n_pRed_lt_two_qRed (ha : 0 < a) (hn : 1 ≤ n) :
    (n : ℝ) * pRed a n < 2 * qRed a n := by
  -- the antisymmetrized summand
  set F : ℕ → ℝ := fun k =>
    sred a k * sred a (n - k) * ((αcoef a k - αcoef a (n - k)) * ((n : ℝ) - 2 * (k : ℝ)))
    with hF
  -- reflection `k ↦ n-k` negates the `α_k` half
  have hrefl : ∑ k ∈ Finset.range (n + 1),
        sred a k * sred a (n - k) * (αcoef a (n - k) * ((n : ℝ) - 2 * (k : ℝ)))
      = ∑ k ∈ Finset.range (n + 1),
        -(sred a k * sred a (n - k) * (αcoef a k * ((n : ℝ) - 2 * (k : ℝ)))) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp only [Nat.add_sub_cancel]
    rw [show n - (n - k) = k from Nat.sub_sub_self hk']
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hk']
    rw [hcast]
    ring
  -- the symmetric half is `2q_n - n p_n`
  have hA : ∑ k ∈ Finset.range (n + 1),
        sred a k * sred a (n - k) * (αcoef a k * ((n : ℝ) - 2 * (k : ℝ)))
      = 2 * qRed a n - (n : ℝ) * pRed a n := by
    rw [qRed, pRed, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hsum : ∑ k ∈ Finset.range (n + 1), F k = 2 * (2 * qRed a n - (n : ℝ) * pRed a n) := by
    have hsplit : ∀ k ∈ Finset.range (n + 1), F k
        = sred a k * sred a (n - k) * (αcoef a k * ((n : ℝ) - 2 * (k : ℝ)))
          - sred a k * sred a (n - k) * (αcoef a (n - k) * ((n : ℝ) - 2 * (k : ℝ))) :=
      fun k _ => by rw [hF]; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, hrefl,
      Finset.sum_neg_distrib, hA]
    ring
  -- every term is nonnegative, and the `k = 0` term is positive
  have hterm : ∀ k ∈ Finset.range (n + 1), 0 ≤ F k := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hw : 0 < sred a k * sred a (n - k) := mul_pos (sred_pos ha k) (sred_pos ha (n - k))
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by rw [Nat.cast_sub hk']
    rw [hF]
    refine mul_nonneg hw.le ?_
    by_cases h2 : 2 * k ≤ n
    · -- `k ≤ n-k`: `α` decreasing gives `α_{n-k} ≤ α_k`, and `n - 2k ≥ 0`
      have hle : (k : ℕ) ≤ n - k := by omega
      have hα : αcoef a (n - k) ≤ αcoef a k := by
        rw [αcoef, αcoef]
        exact trigamma_anti (by positivity) (by
          have : (k : ℝ) ≤ ((n - k : ℕ) : ℝ) := Nat.cast_le.mpr hle
          linarith)
      have hnk : (0 : ℝ) ≤ (n : ℝ) - 2 * (k : ℝ) := by
        have hc : ((2 * k : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast h2
        push_cast at hc
        linarith
      exact mul_nonneg (by linarith) hnk
    · -- `n-k < k`: both factors flip sign
      have h2 : n < 2 * k := by omega
      have hle : n - k ≤ (k : ℕ) := by omega
      have hα : αcoef a k ≤ αcoef a (n - k) := by
        rw [αcoef, αcoef]
        refine trigamma_anti (by positivity) ?_
        have : ((n - k : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hle
        linarith
      have hnk : (n : ℝ) - 2 * (k : ℝ) ≤ 0 := by
        have hn2 : n ≤ (2 * k : ℕ) := by omega
        have hc : ((n : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast hn2
        push_cast at hc
        linarith
      nlinarith [hα, hnk]
  have hzero : 0 < F 0 := by
    have hw : 0 < sred a 0 * sred a (n - 0) := mul_pos (sred_pos ha 0) (sred_pos ha (n - 0))
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hstrict : αcoef a (n - 0) < αcoef a 0 := by
      rw [αcoef, αcoef, Nat.cast_zero, add_zero, Nat.sub_zero]
      have h1 : trigamma a = (a⁻¹) ^ 2 + trigamma (a + 1) := trigamma_succ ha
      have h2 : trigamma (a + (n : ℝ)) ≤ trigamma (a + 1) :=
        trigamma_anti (by linarith) (by linarith)
      have h3 : (0 : ℝ) < (a⁻¹) ^ 2 := by positivity
      linarith
    rw [hF]
    refine mul_pos hw ?_
    have : (0 : ℝ) < (n : ℝ) - 2 * ((0 : ℕ) : ℝ) := by push_cast; linarith
    exact mul_pos (by linarith) this
  have hpos : 0 < ∑ k ∈ Finset.range (n + 1), F k :=
    Finset.sum_pos' hterm ⟨0, Finset.mem_range.mpr (by omega), hzero⟩
  rw [hsum] at hpos
  linarith

/-! ### `eq:q1-p1` -/

theorem pRed_one (ha : 0 < a) :
    pRed a 1 = 2 * (2 * a ^ 2 * trigamma a - 1) / a ^ 3 := by
  have hane : a ≠ 0 := ha.ne'
  simp only [pRed, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sred_zero,
    Nat.sub_self, Nat.sub_zero]
  rw [sred_one, αcoef, αcoef, Nat.cast_zero, add_zero, Nat.cast_one, trigamma_succ' ha]
  field

theorem qRed_one (ha : 0 < a) : qRed a 1 = 2 * trigamma a / a := by
  have hane : a ≠ 0 := ha.ne'
  simp only [qRed, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sred_zero,
    Nat.sub_self, Nat.sub_zero]
  rw [sred_one, αcoef, Nat.cast_zero, add_zero]
  push_cast
  field

/-- **`eq:q-ratio-gap`**, cross-multiplied: degree one has the strictly smallest
`κ`-slope among the positive-degree walls. -/
theorem qRed_pRed_cross (ha : 0 < a) (hn : 2 ≤ n) :
    (2 * a ^ 2 * trigamma a - 1) * qRed a n > a ^ 2 * trigamma a * pRed a n := by
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp := pRed_pos ha n
  have hq := qRed_pos ha (show 1 ≤ n by omega)
  have hgt := sq_mul_trigamma_gt_one ha
  have hqp : pRed a n < qRed a n := by
    have := n_pRed_lt_two_qRed ha (show 1 ≤ n by omega)
    nlinarith
  nlinarith [hgt, hqp, hq]

/-! ### The boundary for every `κ ≥ 1` -/

private theorem alg_tau (a g D κ : ℝ) (hg : g ≠ 0) (hD : D ≠ 0) (_hDd : D = 2 * a ^ 2 * g - 1) :
    (a * g * (2 * a - 1) - (κ - 1) * a ^ 2 * g ^ 2 / 2) / D
      = a * g * (2 * a - 1) / D - (κ - 1) * (a ^ 2 * g ^ 2) / (2 * D) := by
  field_simp

/-- `τ_cw(a,κ) = τ_cw(a,1) - (κ-1)q_1/p_1`, the affine `κ`-dependence of the
coefficientwise boundary (`eq:tau-cw`). -/
theorem tauCw_eq_sub (ha : 0 < a) (κ : ℝ) :
    tauCw a κ = tauCw a 1
      - (κ - 1) * (a ^ 2 * (trigamma a) ^ 2) / (2 * (2 * a ^ 2 * trigamma a - 1)) := by
  have hg := trigamma_pos ha
  have hd := sStar_den_pos ha
  rw [tauCw, tauCw]
  rw [show a * trigamma a * (2 * a - 1) - (1 - 1) * a ^ 2 * trigamma a ^ 2 / 2
      = a * trigamma a * (2 * a - 1) from by ring]
  rw [alg_tau a (trigamma a) _ κ hg.ne' hd.ne' rfl]

/-- **The boundary transports to every `κ ≥ 1`.**  `lem:boundary-positivity` is
the `κ = 1` case; the difference between the two boundary coefficients is
`(κ-1)[(2a²g-1)q_n - a²g p_n]/(2a²g-1) ≥ 0` by `eq:q-ratio-gap`. -/
theorem DcoeffKT_boundary_kappa_pos (ha : 0 < a) (hκ : 1 ≤ κ) (hn : 2 ≤ n) :
    0 < DcoeffKT a κ (tauCw a κ) n := by
  have hg := trigamma_pos ha
  have hd := sStar_den_pos ha
  have h1 := DcoeffKT_boundary_pos ha hn
  rw [DcoeffKT_affine ha] at h1 ⊢
  have hid : 2 * ((tauCw a κ - 1) / trigamma a) * pRed a n + (κ - 1) * qRed a n
      = 2 * ((tauCw a 1 - 1) / trigamma a) * pRed a n
        + (κ - 1) * (((2 * a ^ 2 * trigamma a - 1) * qRed a n
            - a ^ 2 * trigamma a * pRed a n) / (2 * a ^ 2 * trigamma a - 1)) := by
    rw [tauCw_eq_sub ha κ]
    have hgne : trigamma a ≠ 0 := hg.ne'
    have hdne : (2 * a ^ 2 * trigamma a - 1) ≠ 0 := hd.ne'
    field
  have hgap : 0 ≤ (κ - 1) * (((2 * a ^ 2 * trigamma a - 1) * qRed a n
      - a ^ 2 * trigamma a * pRed a n) / (2 * a ^ 2 * trigamma a - 1)) :=
    mul_nonneg (by linarith) (div_nonneg (by linarith [qRed_pRed_cross ha hn]) hd.le)
  linarith [hid, hgap, h1]

private theorem alg_shift (g x y P : ℝ) (hg : g ≠ 0) :
    2 * ((x - 1) / g) * P = 2 * ((y - 1) / g) * P + 2 * ((x - y) / g) * P := by
  field

/-- **`thm:two-parameter-coeff`, the `κ ≥ 1` half, strict.**  Every positive-degree
coefficient is strictly positive above the boundary. -/
theorem DcoeffKT_pos_of_gt (ha : 0 < a) (hκ : 1 ≤ κ) (hτ : tauCw a κ < τ) (hn : 1 ≤ n) :
    0 < DcoeffKT a κ τ n := by
  have hg := trigamma_pos ha
  have hb : 0 ≤ DcoeffKT a κ (tauCw a κ) n := by
    rcases eq_or_lt_of_le hn with h | h
    · rw [← h, DcoeffKT_degree_one_boundary ha κ]
    · exact (DcoeffKT_boundary_kappa_pos ha hκ (by omega)).le
  have hid : DcoeffKT a κ τ n
      = DcoeffKT a κ (tauCw a κ) n + 2 * ((τ - tauCw a κ) / trigamma a) * pRed a n := by
    rw [DcoeffKT_affine ha, DcoeffKT_affine ha]
    linarith [alg_shift (trigamma a) τ (tauCw a κ) (pRed a n) hg.ne']
  have hp : 0 < 2 * ((τ - tauCw a κ) / trigamma a) * pRed a n := by
    have := pRed_pos ha n
    have : 0 < (τ - tauCw a κ) / trigamma a := div_pos (by linarith) hg
    positivity
  linarith

/-- **`thm:two-parameter-coeff`, the `κ ≥ 1` half, nonstrict.** -/
theorem DcoeffKT_nonneg_of_ge (ha : 0 < a) (hκ : 1 ≤ κ) (hτ : tauCw a κ ≤ τ) (hn : 1 ≤ n) :
    0 ≤ DcoeffKT a κ τ n := by
  rcases eq_or_lt_of_le hτ with h | h
  · rw [← h]
    rcases eq_or_lt_of_le hn with h1 | h1
    · rw [← h1, DcoeffKT_degree_one_boundary ha κ]
    · exact (DcoeffKT_boundary_kappa_pos ha hκ (by omega)).le
  · exact (DcoeffKT_pos_of_gt ha hκ h hn).le

/-- **`thm:two-parameter-coeff` on the affine boundary**, for every `κ ≥ 1`: the
degree-one coefficient vanishes and every coefficient of degree `n ≥ 2` is
strictly positive. -/
theorem two_parameter_boundary (ha : 0 < a) (hκ : 1 ≤ κ) :
    DcoeffKT a κ (tauCw a κ) 1 = 0 ∧ ∀ n : ℕ, 2 ≤ n → 0 < DcoeffKT a κ (tauCw a κ) n :=
  ⟨DcoeffKT_degree_one_boundary ha κ, fun _ hn => DcoeffKT_boundary_kappa_pos ha hκ hn⟩

end TuranBessel
