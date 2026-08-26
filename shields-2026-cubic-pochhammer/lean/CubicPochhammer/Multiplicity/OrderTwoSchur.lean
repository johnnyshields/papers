/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Multiplicity.OrderTwo

/-!
# Multiplicity two: Schur-concavity of the coefficient convolution

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp
multiplicity threshold»: the passage from `gmw2_monotoneOn` to the generalized
Turánian at `r = 2`, which is `Bridge`'s reduction repeated with `3` replaced
by `2`.

The route is the paper's own: the beta-binomial representation `eq:C-beta`
identifies `C^{(2)}_{m,w}` with the kernel's beta average up to factors that
depend only on the parameter sum, and `BetaOrder.beta_order` — which is stated
for an arbitrary integrand symmetric about `1/2` and nondecreasing on
`[0,1/2]`, and so needs no re-proof at a new multiplicity — turns kernel
monotonicity into monotonicity in the imbalance.

## Main definitions

* `aint2` --- the `r = 2` kernel against the unnormalized `Beta(u,v)` weight.

## Main statements

* `aint2_eq_sum_bmom`, `aint2_eq` --- the beta moments of the `r = 2` kernel,
  and `eq:C-beta` at `r = 2` with the normalizations cleared.  Both run through
  `BetaOrder`'s multiplicity-free steps, so nothing of the integration is
  repeated from `Bridge`.
* `cmw2_eq_beta_expectation` --- the same identity solved for `C^{(2)}_{m,w}`.
* `cmw2_balance`, `cmw2_antitone_imbalance`, `cmw2_schur_of_kernel` --- the
  reduction itself, in the pieces `Bridge` uses at `r = 3`.
* `schur2_coeff_nonneg` --- coefficientwise Schur-concavity at `r = 2`, in the
  fixed-sum form.
* `turan2_coeff_nonneg` --- the generalized Turánian of `eq:Turan-def` at
  `r = 2`, over the whole closure `μ, α, β ≥ 0`.  The change of coordinates from
  the fixed-sum form is `Main.turan_nonneg_of_schur`, which sees no
  multiplicity, so only the weights are supplied here.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp multiplicity
  threshold», and `sec:reduction` «Exact reduction to a residue kernel» for the
  reduction it repeats: `eq:C-beta`, `lem:beta-order`, `cor:C-schur`,
  `eq:Turan-def`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-! ### The beta-binomial representation at `r = 2` -/

/-- The `r = 2` kernel against the unnormalized `Beta(u,v)` weight. -/
noncomputable def aint2 (m : ℕ) (w : ℕ → ℝ) (u v : ℝ) : ℝ :=
  ∫ p in (0:ℝ)..1, gmw2 m w p * (p ^ (u - 1) * (1 - p) ^ (v - 1))

/-- **The beta moments of the `r = 2` kernel**, `aint_eq_sum_bmom` at
multiplicity two. -/
theorem aint2_eq_sum_bmom (m : ℕ) (w : ℕ → ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    aint2 m w u v = ∑ k ∈ Finset.Icc 1 (m - 1),
      (w k * (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ))
        * bmom (u + ((2 * k : ℕ) : ℝ)) (v + ((2 * (m - k) : ℕ) : ℝ)) :=
  integral_eq_sum_bmom _ _ (fun k => 2 * k) (fun k => 2 * (m - k)) hu hv fun p hp0 hp1 => by
    unfold gmw2
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by
      rw [mul_assoc (w k * (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ)), mul_assoc,
        monomial_mul_betaKer hp0 hp1 (2 * k) (2 * (m - k))]

/-- **`eq:C-beta` at `r = 2`**, with the normalizations cleared:
`aint₂ · (u+v)_{2m} = (2m-2)! · B(u,v) · C^{(2)}_{m,w}(u,v)`.  Both steps are
`Bridge`'s, at general multiplicity: the beta moments `aint2_eq_sum_bmom`, then
`sum_bmom_mul_poch` against the trinomial split
`Bridge.choose_mul_factorial_residue`. -/
theorem aint2_eq (m : ℕ) (hm : 2 ≤ m) (w : ℕ → ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    aint2 m w u v * poch (u + v) (2 * m)
      = (Nat.factorial (2 * m - 2) : ℝ) * bmom u v * cmwr 2 w m u v := by
  rw [aint2_eq_sum_bmom m w hu hv]
  exact sum_bmom_mul_poch _ w (fun k => (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ))
    (fun k => 2 * k) (fun k => 2 * (m - k)) _ (2 * m) hu hv
    (fun k hk => by
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      dsimp only
      omega)
    (fun k hk => by
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      dsimp only
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
        (choose_mul_factorial_residue (by norm_num) hm hk1 hk2))

/-! ### Schur-concavity at `r = 2` -/

theorem cmw2_balance (w : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hsym : ∀ k, 1 ≤ k → k ≤ m - 1 → w k = w (m - k)) (u v : ℝ) :
    cmwr 2 w m u v
      = cmwr 2 w m ((u + v) / 2 + |u - v| / 2) ((u + v) / 2 - |u - v| / 2) := by
  rcases le_or_gt v u with h | h
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u - v),
      show (u + v) / 2 + (u - v) / 2 = u from by ring,
      show (u + v) / 2 - (u - v) / 2 = v from by ring]
  · rw [abs_of_neg (by linarith : u - v < 0),
      show (u + v) / 2 + (-(u - v)) / 2 = v from by ring,
      show (u + v) / 2 - (-(u - v)) / 2 = u from by ring]
    exact cmwr_symm 2 w hm hsym u v

/-- **`eq:C-beta` at `r = 2`, solved for `C^{(2)}_{m,w}`**: the coefficient
convolution is the `Beta(u,v)`-expectation of the `r = 2` kernel, scaled by
`(u+v)_{2m}/(2m-2)!`.  `Bridge.cmw_eq_beta_expectation` at multiplicity two. -/
theorem cmw2_eq_beta_expectation (m : ℕ) (hm : 2 ≤ m) (w : ℕ → ℝ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    cmwr 2 w m u v
      = poch (u + v) (2 * m) / (Nat.factorial (2 * m - 2) : ℝ) * (aint2 m w u v / bmom u v) := by
  have hB : (0:ℝ) < bmom u v := bmom_pos hu hv
  have hF : (0:ℝ) < (Nat.factorial (2 * m - 2) : ℝ) := by positivity
  field_simp
  linear_combination (-1 : ℝ) * aint2_eq m hm w hu hv

/-- **`cor:C-schur` at `r = 2`, interior range**: for symmetric weights whose
`r = 2` kernel is nondecreasing on `[0,1/2]`, `d ↦ C^{(2)}_{m,w}(s/2+d, s/2-d)`
is nonincreasing for `0 ≤ d < s/2`.  `Bridge.cmw_antitone_imbalance` at
multiplicity two, over the same `lem:beta-order`. -/
theorem cmw2_antitone_imbalance (w : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hsym : ∀ k, 1 ≤ k → k ≤ m - 1 → w k = w (m - k))
    (hG : MonotoneOn (gmw2 m w) (Set.Icc 0 (1 / 2)))
    {s d₁ d₂ : ℝ} (hd₁ : 0 ≤ d₁) (hd : d₁ ≤ d₂) (hd₂ : d₂ < s / 2) :
    cmwr 2 w m (s / 2 + d₂) (s / 2 - d₂) ≤ cmwr 2 w m (s / 2 + d₁) (s / 2 - d₁) := by
  have hs2 : (0:ℝ) < s / 2 := lt_of_le_of_lt (hd₁.trans hd) hd₂
  have hlo₁ : (0:ℝ) < s / 2 + d₁ := by linarith
  have hlo₂ : (0:ℝ) < s / 2 + d₂ := by linarith [hd₁.trans hd]
  have hhi₁ : (0:ℝ) < s / 2 - d₁ := by linarith
  have hhi₂ : (0:ℝ) < s / 2 - d₂ := by linarith
  have hbo := beta_order (H := gmw2 m w) (gmw2_symm m hm w hsym) (continuous_gmw2 m w)
    hG hd₁ hd hd₂
  rw [cmw2_eq_beta_expectation m hm w hlo₁ hhi₁, cmw2_eq_beta_expectation m hm w hlo₂ hhi₂,
    show s / 2 + d₁ + (s / 2 - d₁) = s from by ring,
    show s / 2 + d₂ + (s / 2 - d₂) = s from by ring]
  exact mul_le_mul_of_nonneg_left
    ((div_le_div_iff₀ (bmom_pos hlo₂ hhi₂) (bmom_pos hlo₁ hhi₁)).mpr hbo)
    (div_nonneg (poch_pos (by linarith) _).le (by positivity))

theorem cmw2_schur_of_kernel (w : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hsym : ∀ k, 1 ≤ k → k ≤ m - 1 → w k = w (m - k))
    (hG : MonotoneOn (gmw2 m w) (Set.Icc 0 (1 / 2)))
    (u1 v1 u2 v2 : ℝ) (hu2 : 0 < u2) (hv2 : 0 < v2)
    (hsum : u1 + v1 = u2 + v2) (himb : |u1 - v1| ≤ |u2 - v2|) :
    cmwr 2 w m u2 v2 ≤ cmwr 2 w m u1 v1 := by
  have hd₂lt : |u2 - v2| / 2 < (u1 + v1) / 2 := by
    rw [hsum]
    rcases le_or_gt v2 u2 with h | h
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u2 - v2)]; linarith
    · rw [abs_of_neg (by linarith : u2 - v2 < 0)]; linarith
  have hb1 := cmw2_balance w hm hsym u1 v1
  have hb2 := cmw2_balance w hm hsym u2 v2
  rw [← hsum] at hb2
  rw [hb1, hb2]
  exact cmw2_antitone_imbalance w m hm hsym hG (by positivity) (by linarith) hd₂lt

/-! ### `UniversalLogConcave 2` -/

/-- **Coefficientwise Schur-concavity at `r = 2`, fixed-sum form.** -/
theorem schur2_coeff_nonneg (w : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hwnn : ∀ i, 0 ≤ w i)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j)
    (hsym : ∀ k, 1 ≤ k → k ≤ m - 1 → w k = w (m - k))
    (s d₁ d₂ : ℝ) (hs : 0 < s) (hd₁ : 0 ≤ d₁) (hd : d₁ ≤ d₂) (hd₂ : d₂ ≤ s / 2) :
    cmwr 2 w m (s / 2 + d₂) (s / 2 - d₂) ≤ cmwr 2 w m (s / 2 + d₁) (s / 2 - d₁) := by
  rcases eq_or_lt_of_le hd₂ with heq | hlt
  · have hzero : s / 2 - d₂ = 0 := by rw [heq]; ring
    rw [hzero, cmwr_right_zero 2 (by norm_num) w hm]
    exact cmwr_nonneg 2 w m hwnn (by linarith) (by linarith [heq ▸ hd])
  · have hG : MonotoneOn (gmw2 m w) (Set.Icc 0 (1 / 2)) :=
      gmw2_monotoneOn m hm w hwmono (fun i _ _ => hwnn i) hsym
    refine cmw2_schur_of_kernel w m hm hsym hG (s / 2 + d₁) (s / 2 - d₁)
      (s / 2 + d₂) (s / 2 - d₂) (by linarith) (by linarith) (by ring) ?_
    rw [show s / 2 + d₁ - (s / 2 - d₁) = 2 * d₁ by ring,
      show s / 2 + d₂ - (s / 2 - d₂) = 2 * d₂ by ring,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * d₁),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * d₂)]
    linarith

/-- **Karp–Zhang's quadratic theorem, proved here**: the generalized Turánian of
`F_{f,2}` has nonnegative coefficients over the whole closure `μ, α, β ≥ 0`. -/
theorem turan2_coeff_nonneg (f : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hfnn : ∀ k, 0 ≤ f k)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → f i * f (m - i) ≤ f j * f (m - j))
    (μ α β : ℝ) (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ cmfr 2 f m (μ + α) (μ + β) - cmfr 2 f m μ (μ + α + β) := by
  set w : ℕ → ℝ := fun k => f k * f (m - k) with hw
  have hwnn : ∀ i, 0 ≤ w i := fun i => mul_nonneg (hfnn i) (hfnn (m - i))
  have hsym : ∀ k, 1 ≤ k → k ≤ m - 1 → w k = w (m - k) := by
    intro k hk1 hk2
    have h : m - (m - k) = k := by omega
    simp only [hw, h]
    ring
  exact turan_nonneg_of_schur (C := cmwr 2 w m) (cmwr_symm 2 w hm hsym)
    (fun s d₁ d₂ hs hd₁ hd hd₂ =>
      schur2_coeff_nonneg w m hm hwnn hwmono hsym s d₁ d₂ hs hd₁ hd hd₂) hμ hα hβ

end CubicPochhammer
