/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# The beta moment and the likelihood-ratio order

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:reduction` «Exact
reduction to a residue kernel» (`lem:beta-order`, `eq:beta-order`): the
likelihood-ratio order, and the beta function the reduction `eq:C-beta` runs
through.  Nothing here mentions
`C_{m,w}` or `G_{m,w}`: the order statement is proved for an arbitrary
continuous integrand symmetric about `1/2` and nondecreasing on `[0,1/2]`, and
`Bridge` supplies the kernel as that integrand.

The paper's route is measure-theoretic — the beta-binomial mixture, the density
of `Q = P(1-P)` after `q = p(1-p)`, and a likelihood-ratio order.  Mathlib at
this pin carries the `Beta` law but no stochastic order of any kind, so the route
here avoids the order theory and never names a probability law:

* `bmom α β = ∫_0^1 p^{α-1}(1-p)^{β-1} dp` is an ordinary interval integral,
  equal to `Γ(α)Γ(β)/Γ(α+β)` (`bmom_eq_Gamma`).  The one property of it the
  reduction uses is the Pochhammer shift
  `B(α+j,β+k)(α+β)_{j+k} = (α)_j(β)_k B(α,β)` (`bmom_shift`), from
  `Γ(α+1) = αΓ(α)`.
* `integral_fold` folds `∫_0^1` onto `∫_{1/2}^1` against
  `foldKer s d p = ρ_d(p) + ρ_d(1-p)`, using only the symmetry of the integrand.
  On `(0,1)` that kernel is `2(p(1-p))^{s/2-1}cosh(d·logit p)`
  (`foldKer_eq_cosh`), which is the `cosh` the paper's density carries, obtained
  as an identity in `p` rather than after a change of variables.
* `cosh_ratio_cross` is the ratio monotonicity cross-multiplied:
  `cosh(d₂x)cosh(d₁y) ≤ cosh(d₂y)cosh(d₁x)` for `0 ≤ d₁ ≤ d₂`, `0 ≤ x ≤ y`.  It
  follows from `2cosh A cosh B = cosh(A+B) + cosh(A-B)` together with
  `|d₂x ± d₁y| ≤ |d₂y ± d₁x|` — no derivative, no `tanh`, no quotient.
* `exists_crossing` turns that into the single sign change of `Z₁F₂ - Z₂F₁`, and
  `integral_mul_nonpos_of_crossing` recentres an antitone integrand at the
  crossing point so the product is pointwise signed.  Together they give
  `beta_order`, which is `eq:beta-order`.

`beta_order` is the nonstrict clause.  `beta_order_strict` is the strict one, at
the paper's own hypothesis: `H` strictly increasing on the *open* interval
`(0,1/2)`, with `strictMonoOn_of_monotoneOn_Ioo` supplying the closed interval
from that and the nondecreasing hypothesis already present.  The chain is the
same one strictly — `cosh_ratio_cross_strict`, `foldKer_cross_strict`,
`exists_crossing_strict`, `integral_mul_neg_of_crossing` — with one extra step:
the crossing point is interior, because a difference of one strict sign
throughout `(1/2,1)` cannot integrate to zero.

Sorry-free and axiom-free.

## Main definitions

* `poch` --- the Pochhammer symbol `(u)_k` for real `u`.
* `bmom` --- the beta function `B(α,β)` as an ordinary interval integral.
* `betaKer`, `foldKer` --- the unnormalized beta density at shape sum `s` and
  imbalance `d`, and that density folded about `p = 1/2`.
* `logit` --- `log p - log (1-p)`, the variable the folded kernel's `cosh` runs in.

## Main statements

* `bmom_eq_Gamma`, `bmom_shift` --- the Gamma evaluation of `bmom`, and the
  Pochhammer shift `B(α+j,β+k)(α+β)_{j+k} = (α)_j(β)_k B(α,β)` that `eq:C-beta`
  consumes.
* `integral_fold`, `foldKer_eq_cosh` --- the fold onto `[1/2,1]`, and the `cosh`
  form of the folded kernel as an identity in `p`.
* `cosh_ratio_cross`, `foldKer_cross` --- the ratio monotonicity, cross-multiplied.
* `antitoneOn_of_symm_monotoneOn` --- symmetry about `1/2` turns the hypothesis
  on `[0,1/2]` into the one the folded half needs.
* `exists_crossing` --- the single sign change of `Z₁F₂ - Z₂F₁`.
* `integral_mul_sub_const`, `crossing_mem_Ioo` --- recentring `H` at the
  crossing value, and the fact that zero total mass forces the crossing point
  into the open interval.
* `foldDiff`, `integral_foldDiff`, `integral_mul_foldDiff` --- the recentred
  difference of the two folded kernels, its vanishing mass, and the linearity
  both clauses read their conclusion off.
* `monomial_mul_betaKer`, `integral_eq_sum_bmom`, `sum_bmom_mul_poch` --- the
  three multiplicity-free steps of `eq:C-beta`: absorb a Bernstein monomial into
  the beta weight, integrate the expansion term by term, and reduce the beta
  moments to `B(u,v)` by the Pochhammer shift.
* `beta_order`, `beta_order_strict` --- `lem:beta-order` (`eq:beta-order`): for a
  continuous integrand symmetric about `1/2` and nondecreasing on `[0,1/2]`, the
  normalized beta average decreases in the imbalance.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:reduction` «Exact reduction to a
  residue kernel»: `lem:beta-order`, `eq:beta-order`, `eq:C-beta`.
-/

open MeasureTheory intervalIntegral Set

namespace CubicPochhammer

/-! ## Pochhammer symbols and the Gamma recurrence -/

/-- The Pochhammer symbol `(u)_k = u(u+1)⋯(u+k-1)` for real `u`. -/
noncomputable def poch (u : ℝ) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (u + (i : ℝ))

theorem poch_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ) : 0 ≤ poch u k :=
  Finset.prod_nonneg fun i _ => by positivity

theorem poch_pos {u : ℝ} (hu : 0 < u) (k : ℕ) : 0 < poch u k :=
  Finset.prod_pos fun i _ => by positivity

theorem poch_zero_eq_zero {k : ℕ} (hk : 1 ≤ k) : poch (0 : ℝ) k = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr hk) (by norm_num)

/-- `Γ(α+n) = (α)_n Γ(α)`, the Pochhammer form of the Gamma recurrence.

The leading capital is deliberate and is not a casing violation: this is a lemma about
`Real.Gamma`, whose own name is capitalized, and Mathlib capitalizes it in theorem names
for the same reason (`Real.Gamma_add_one`, `Real.Gamma_nat_eq_factorial`). -/
theorem Gamma_add_nat {α : ℝ} (hα : 0 < α) (n : ℕ) :
    Real.Gamma (α + n) = poch α n * Real.Gamma α := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
      have hne : α + (n : ℝ) ≠ 0 := by positivity
      have hstep : Real.Gamma (α + (n + 1 : ℕ)) = Real.Gamma ((α + n) + 1) := by
        push_cast; ring_nf
      rw [hstep, Real.Gamma_add_one hne, ih, poch, poch, Finset.prod_range_succ]
      ring

/-! ## The real beta moment -/

/-- `bmom α β = ∫_0^1 p^{α-1}(1-p)^{β-1} dp`, the beta function as a real integral. -/
noncomputable def bmom (α β : ℝ) : ℝ := ∫ p in (0:ℝ)..1, p ^ (α - 1) * (1 - p) ^ (β - 1)

theorem intervalIntegrable_betaKer_left {α : ℝ} (hα : 0 < α) (β : ℝ) :
    IntervalIntegrable (fun p : ℝ => p ^ (α - 1) * (1 - p) ^ (β - 1)) volume 0 (1/2) := by
  apply IntervalIntegrable.mul_continuousOn
  · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  · apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by positivity : (0:ℝ) ≤ 1/2)] at hx
    left; nlinarith [hx.2]

/-- The beta integrand is interval-integrable on `[0,1]` for positive exponents. -/
theorem intervalIntegrable_betaKer {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntervalIntegrable (fun p : ℝ => p ^ (α - 1) * (1 - p) ^ (β - 1)) volume 0 1 := by
  refine (intervalIntegrable_betaKer_left hα β).trans ?_
  rw [IntervalIntegrable.iff_comp_neg]
  convert ((intervalIntegrable_betaKer_left hβ α).comp_add_right 1).symm using 1
  · ext1 x
    conv_lhs => rw [mul_comm]
    congr 2 <;> ring
  · norm_num
  · simp

/-- `bmom` is the beta function: `B(α,β) = Γ(α)Γ(β)/Γ(α+β)`. -/
theorem bmom_eq_Gamma {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    bmom α β = Real.Gamma α * Real.Gamma β / Real.Gamma (α + β) := by
  have hbetaC : Complex.betaIntegral (α : ℂ) (β : ℂ) = ((bmom α β : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, bmom, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [uIcc_of_le (zero_le_one)] at hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    have hx1 : (0:ℝ) ≤ 1 - x := by linarith [hx.2]
    push_cast
    rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow hx1]
    push_cast
    ring_nf
  have hbetaReal := ProbabilityTheory.beta_eq_betaIntegralReal α β hα hβ
  rw [hbetaC] at hbetaReal
  simp only [Complex.ofReal_re] at hbetaReal
  rw [← hbetaReal, ProbabilityTheory.beta]

theorem bmom_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 < bmom α β := by
  rw [bmom_eq_Gamma hα hβ]
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos hα) (Real.Gamma_pos_of_pos hβ))
    (Real.Gamma_pos_of_pos (by linarith))

/-- Integer shifts of the beta moment, in Pochhammer form:
`B(α+j, β+k) (α+β)_{j+k} = (α)_j (β)_k B(α,β)`. -/
theorem bmom_shift {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (j k : ℕ) :
    bmom (α + j) (β + k) * poch (α + β) (j + k) = poch α j * poch β k * bmom α β := by
  have hαj : (0:ℝ) < α + j := by positivity
  have hβk : (0:ℝ) < β + k := by positivity
  have hsum : α + j + (β + k) = (α + β) + ((j + k : ℕ) : ℝ) := by push_cast; ring
  have hΓ : Real.Gamma (α + β) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hP : poch (α + β) (j + k) ≠ 0 :=
    ne_of_gt (poch_pos (show (0:ℝ) < α + β by linarith) (j + k))
  rw [bmom_eq_Gamma hαj hβk, bmom_eq_Gamma hα hβ, hsum,
      Gamma_add_nat hα j, Gamma_add_nat hβ k,
      Gamma_add_nat (show (0 : ℝ) < α + β by linarith) (j + k)]
  field_simp

/-- A Bernstein monomial absorbed into the beta weight: on the open interval,

  `p^a (1-p)^b \cdot p^{u-1}(1-p)^{v-1} = p^{u+a-1}(1-p)^{v+b-1}`,

the natural powers on the left becoming real ones on the right.  This is the
only place the `rpow` addition law is used in `eq:C-beta`, and it is what fixes
the two exponent shifts `a`, `b` a residue kernel contributes. -/
theorem monomial_mul_betaKer {u v p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (a b : ℕ) :
    p ^ a * (1 - p) ^ b * (p ^ (u - 1) * (1 - p) ^ (v - 1))
      = p ^ (u + (a : ℝ) - 1) * (1 - p) ^ (v + (b : ℝ) - 1) := by
  have hq0 : (0:ℝ) < 1 - p := by linarith
  rw [← Real.rpow_natCast p a, ← Real.rpow_natCast (1 - p) b,
    show p ^ (a : ℝ) * (1 - p) ^ (b : ℝ) * (p ^ (u - 1) * (1 - p) ^ (v - 1))
      = p ^ (a : ℝ) * p ^ (u - 1) * ((1 - p) ^ (b : ℝ) * (1 - p) ^ (v - 1)) from by ring,
    ← Real.rpow_add hp0, ← Real.rpow_add hq0]
  ring_nf

/-- **Term-by-term beta integration.**  A function whose product with the
unnormalized `Beta(u,v)` weight expands, on the open interval, into a finite
sum of beta integrands at integer-shifted parameters integrates to the
corresponding sum of beta moments:

  `∫_0^1 G(p)\,p^{u-1}(1-p)^{v-1}\,dp = ∑_k c_k\,B(u+a_k,\,v+b_k)`.

The expansion is needed only on `(0,1)`: the endpoints are a null set, which is
what lets `hG` be stated with the strict inequalities the `rpow` addition law
requires.  This is the step by which the Bernstein form `eq:G-weighted` of a
residue kernel becomes `eq:C-beta`, at any multiplicity — the shifts `a_k`, `b_k`
are the only thing that changes with `r`. -/
theorem integral_eq_sum_bmom {G : ℝ → ℝ} (t : Finset ℕ) (c : ℕ → ℝ) (a b : ℕ → ℕ)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hG : ∀ p : ℝ, 0 < p → p < 1 → G p * (p ^ (u - 1) * (1 - p) ^ (v - 1))
      = ∑ k ∈ t, c k * (p ^ (u + (a k : ℝ) - 1) * (1 - p) ^ (v + (b k : ℝ) - 1))) :
    (∫ p in (0:ℝ)..1, G p * (p ^ (u - 1) * (1 - p) ^ (v - 1)))
      = ∑ k ∈ t, c k * bmom (u + (a k : ℝ)) (v + (b k : ℝ)) := by
  have hint : ∀ k ∈ t, IntervalIntegrable
      (fun p : ℝ => c k * (p ^ (u + (a k : ℝ) - 1) * (1 - p) ^ (v + (b k : ℝ) - 1)))
      volume 0 1 := fun k _ =>
    (intervalIntegrable_betaKer (by positivity) (by positivity)).const_mul _
  have hne : ∀ᵐ (p : ℝ), p ≠ 1 := by
    have hpoint : (volume ({(1:ℝ)} : Set ℝ)) = 0 := by simp
    simpa [Set.compl_def] using MeasureTheory.compl_mem_ae_iff.mpr hpoint
  rw [intervalIntegral.integral_congr_ae
      (g := fun p => ∑ k ∈ t, c k * (p ^ (u + (a k : ℝ) - 1) * (1 - p) ^ (v + (b k : ℝ) - 1))) ?_,
    intervalIntegral.integral_finsetSum hint]
  · exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _
  · filter_upwards [hne] with p hpne hmem
    rw [Set.uIoc_of_le zero_le_one] at hmem
    exact hG p hmem.1 (lt_of_le_of_ne hmem.2 hpne)

/-- **The Pochhammer reduction of `eq:C-beta`.**  A sum of beta moments at
integer shifts `(a_k, b_k)` of a common parameter pair, multiplied by
`(u+v)_n` for the common shift total `n = a_k + b_k`, becomes `B(u,v)` times
the Pochhammer sum that defines the coefficient convolution — provided the
coefficients satisfy the trinomial split `C_k (a_k-1)!\,(b_k-1)! = N`:

  `\Big(∑_k w_k C_k B(u+a_k, v+b_k)\Big)(u+v)_n
     = N\,B(u,v) ∑_k w_k \frac{(u)_{a_k}(v)_{b_k}}{(a_k-1)!\,(b_k-1)!}`.

Termwise this is `bmom_shift`; the hypotheses are the two facts a residue
kernel at multiplicity `r` supplies, `a_k + b_k = rm` and
`\binom{rm-2}{rk-1}(rk-1)!\,[r(m-k)-1]! = (rm-2)!`. -/
theorem sum_bmom_mul_poch (t : Finset ℕ) (w C : ℕ → ℝ) (a b : ℕ → ℕ) (N : ℝ) (n : ℕ)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hab : ∀ k ∈ t, a k + b k = n)
    (hsplit : ∀ k ∈ t, C k * (Nat.factorial (a k - 1) : ℝ) * (Nat.factorial (b k - 1) : ℝ) = N) :
    (∑ k ∈ t, w k * C k * bmom (u + (a k : ℝ)) (v + (b k : ℝ))) * poch (u + v) n
      = N * bmom u v * ∑ k ∈ t, w k * (poch u (a k) * poch v (b k))
          / ((Nat.factorial (a k - 1) : ℝ) * (Nat.factorial (b k - 1) : ℝ)) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hshift := bmom_shift hu hv (a k) (b k)
  rw [hab k hk] at hshift
  have hf1 : ((Nat.factorial (a k - 1) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : ((Nat.factorial (b k - 1) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  linear_combination (w k * C k * (Nat.factorial (a k - 1) : ℝ)
      * (Nat.factorial (b k - 1) : ℝ)) * hshift
    + (w k * poch u (a k) * poch v (b k) * bmom u v) * (hsplit k hk)

/-! ## The symmetrized beta kernel -/

/-- The logit `log p - log (1-p)`. -/
noncomputable def logit (p : ℝ) : ℝ := Real.log p - Real.log (1 - p)

/-- The unnormalized beta density with shape sum `s` and imbalance `d`. -/
noncomputable def betaKer (s d p : ℝ) : ℝ := p ^ (s/2 + d - 1) * (1 - p) ^ (s/2 - d - 1)

/-- The kernel folded about `p = 1/2`. -/
noncomputable def foldKer (s d p : ℝ) : ℝ := betaKer s d p + betaKer s d (1 - p)

theorem bmom_eq_integral_betaKer (s d : ℝ) :
    bmom (s/2 + d) (s/2 - d) = ∫ p in (0:ℝ)..1, betaKer s d p := rfl

/-- The folded kernel in closed form: `(p(1-p))^{s/2-1} 2cosh(d·logit p)`. -/
theorem foldKer_eq_cosh (s d : ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    foldKer s d p = 2 * ((p * (1 - p)) ^ (s/2 - 1) * Real.cosh (d * logit p)) := by
  have hp1 : (0:ℝ) < 1 - p := by linarith
  have e1 : p ^ (s/2 + d - 1) = p ^ (s/2 - 1) * p ^ d := by
    rw [← Real.rpow_add hp0]; ring_nf
  have e2 : (1 - p) ^ (s/2 - d - 1) = (1 - p) ^ (s/2 - 1) * (1 - p) ^ (-d) := by
    rw [← Real.rpow_add hp1]; ring_nf
  have e3 : (1 - p) ^ (s/2 + d - 1) = (1 - p) ^ (s/2 - 1) * (1 - p) ^ d := by
    rw [← Real.rpow_add hp1]; ring_nf
  have e4 : p ^ (s/2 - d - 1) = p ^ (s/2 - 1) * p ^ (-d) := by
    rw [← Real.rpow_add hp0]; ring_nf
  have hW : (p * (1 - p)) ^ (s/2 - 1) = p ^ (s/2 - 1) * (1 - p) ^ (s/2 - 1) :=
    Real.mul_rpow hp0.le hp1.le
  have hx : p ^ d * (1 - p) ^ (-d) = Real.exp (d * logit p) := by
    rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp1, ← Real.exp_add, logit]; ring_nf
  have hy : (1 - p) ^ d * p ^ (-d) = Real.exp (-(d * logit p)) := by
    rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp1, ← Real.exp_add, logit]; ring_nf
  simp only [foldKer, betaKer, sub_sub_cancel]
  rw [e1, e2, e3, e4, hW, Real.cosh_eq]
  linear_combination (p ^ (s/2-1) * (1 - p) ^ (s/2-1)) * hx
    + (p ^ (s/2-1) * (1 - p) ^ (s/2-1)) * hy

theorem foldKer_pos (s d : ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < foldKer s d p := by
  rw [foldKer_eq_cosh s d hp0 hp1]
  have : (0:ℝ) < (p * (1 - p)) ^ (s/2 - 1) := Real.rpow_pos_of_pos (by nlinarith) _
  have := Real.cosh_pos (d * logit p)
  positivity

theorem logit_nonneg {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p < 1) : 0 ≤ logit p := by
  have hp1 : (0:ℝ) < 1 - p := by linarith
  simpa [logit] using Real.log_le_log hp1 (by linarith : 1 - p ≤ p)

theorem logit_mono {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) : logit p ≤ logit q := by
  have hlogp : Real.log p ≤ Real.log q := Real.log_le_log hp hpq
  have hlog1p : Real.log (1 - q) ≤ Real.log (1 - p) := Real.log_le_log (by linarith) (by linarith)
  simp only [logit]; linarith

/-- The product-to-sum identity the cross-multiplied ratio monotonicity runs on:
`2 cosh A cosh B = cosh(A+B) + cosh(A-B)`. -/
theorem two_mul_cosh_mul_cosh (A B : ℝ) :
    2 * (Real.cosh A * Real.cosh B) = Real.cosh (A + B) + Real.cosh (A - B) := by
  rw [Real.cosh_add, Real.cosh_sub]; ring

/-- `cosh(d₂x)cosh(d₁y) ≤ cosh(d₂y)cosh(d₁x)` for `0 ≤ d₁ ≤ d₂` and `0 ≤ x ≤ y`: the
likelihood ratio `cosh(d₂·)/cosh(d₁·)` is nondecreasing on `[0,∞)`.  Proved from
`2 cosh A cosh B = cosh(A+B) + cosh(A-B)` and `|d₂x ± d₁y| ≤ |d₂y ± d₁x|`. -/
theorem cosh_ratio_cross {d₁ d₂ x y : ℝ} (hd₁ : 0 ≤ d₁) (hd : d₁ ≤ d₂)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.cosh (d₂ * x) * Real.cosh (d₁ * y) ≤ Real.cosh (d₂ * y) * Real.cosh (d₁ * x) := by
  have hy : 0 ≤ y := hx.trans hxy
  have hd₂ : 0 ≤ d₂ := hd₁.trans hd
  have hplus : Real.cosh (d₂ * x + d₁ * y) ≤ Real.cosh (d₂ * y + d₁ * x) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hxy)]
  have hminus : Real.cosh (d₂ * x - d₁ * y) ≤ Real.cosh (d₂ * y - d₁ * x) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (show (0:ℝ) ≤ d₂ * y - d₁ * x by nlinarith), abs_le]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hd) (add_nonneg hx hy),
      mul_nonneg (add_nonneg hd₁ hd₂) (sub_nonneg.mpr hxy)]
  nlinarith [two_mul_cosh_mul_cosh (d₂ * x) (d₁ * y),
    two_mul_cosh_mul_cosh (d₂ * y) (d₁ * x)]

/-- Single-crossing of the folded kernels on `[1/2,1)`: the ratio
`foldKer s d₂ / foldKer s d₁` is nondecreasing, written multiplicatively. -/
theorem foldKer_cross {s d₁ d₂ p q : ℝ} (hd₁ : 0 ≤ d₁) (hd : d₁ ≤ d₂)
    (hp : 1 / 2 ≤ p) (hpq : p ≤ q) (hq : q < 1) :
    foldKer s d₂ p * foldKer s d₁ q ≤ foldKer s d₂ q * foldKer s d₁ p := by
  have hp0 : (0:ℝ) < p := by linarith
  have hp1 : p < 1 := lt_of_le_of_lt hpq hq
  have hq0 : (0:ℝ) < q := by linarith
  have hWp : (0:ℝ) < (p * (1 - p)) ^ (s/2 - 1) := Real.rpow_pos_of_pos (by nlinarith) _
  have hWq : (0:ℝ) < (q * (1 - q)) ^ (s/2 - 1) := Real.rpow_pos_of_pos (by nlinarith) _
  rw [foldKer_eq_cosh s d₂ hp0 hp1, foldKer_eq_cosh s d₁ hq0 hq,
      foldKer_eq_cosh s d₂ hq0 hq, foldKer_eq_cosh s d₁ hp0 hp1]
  have hcore := cosh_ratio_cross hd₁ hd (logit_nonneg hp hp1) (logit_mono hp0 hpq hq)
  nlinarith [mul_pos hWp hWq, hcore]

/-! ## The single-crossing inequality -/

/-- **Recentring.**  Subtracting the constant `H c` from `H` leaves `∫ H·g`
unchanged whenever `g` carries zero mass.  Both clauses use it for the same
reason: it is what lets the sign of `(H - H c)·g` be read off the two sides of
the crossing, where `H - H c` changes sign exactly with `g`. -/
theorem integral_mul_sub_const {a b : ℝ} {H g : ℝ → ℝ} (c : ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hHg : IntervalIntegrable (fun p => H p * g p) volume a b)
    (hg0 : ∫ p in a..b, g p = 0) :
    ∫ p in a..b, (H p - H c) * g p = ∫ p in a..b, H p * g p := by
  have hsplit : ∀ p : ℝ, (H p - H c) * g p = H p * g p - H c * g p := by intro p; ring
  simp_rw [hsplit]
  rw [intervalIntegral.integral_sub hHg (hg.const_mul _),
    intervalIntegral.integral_const_mul, hg0, mul_zero, sub_zero]

/-- If `g` changes sign once, from nonpositive to nonnegative, and `H` is antitone, then
`∫ H g ≤ 0` whenever `∫ g = 0`.  The crossing point `c` is where `H` is evaluated to
recentre the integrand; the point `b` itself is excluded, so the hypotheses are stated on
half-open intervals. -/
theorem integral_mul_nonpos_of_crossing {a b c : ℝ} (hab : a ≤ b) {H g : ℝ → ℝ}
    (hc : c ∈ Set.Icc a b)
    (hH : AntitoneOn H (Set.Icc a b))
    (hlo : ∀ p ∈ Set.Ico a c, g p ≤ 0)
    (hhi : ∀ p ∈ Set.Ioo c b, 0 ≤ g p)
    (hg : IntervalIntegrable g volume a b)
    (hHg : IntervalIntegrable (fun p => H p * g p) volume a b)
    (hg0 : ∫ p in a..b, g p = 0) :
    ∫ p in a..b, H p * g p ≤ 0 := by
  rw [← integral_mul_sub_const c hg hHg hg0, ← neg_nonneg,
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_nonneg_of_ae_restrict hab ?_
  change ∀ᵐ x ∂ (volume.restrict (Set.Icc a b)), 0 ≤ -((H x - H c) * g x)
  rw [← MeasureTheory.ae_restrict_congr_set MeasureTheory.Ico_ae_eq_Icc]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ico (fun p hp => ?_)
  have hpIcc : p ∈ Set.Icc a b := ⟨hp.1, hp.2.le⟩
  rcases lt_trichotomy p c with hpc | hpc | hpc
  · have hHle : H c ≤ H p := hH hpIcc hc hpc.le
    have hgnonpos : g p ≤ 0 := hlo p ⟨hp.1, hpc⟩
    simp only [neg_nonneg]; nlinarith
  · simp [hpc]
  · have hHge : H p ≤ H c := hH hc hpIcc hpc.le
    have hgnonneg : 0 ≤ g p := hhi p ⟨hpc, hp.2⟩
    simp only [neg_nonneg]; nlinarith

/-- A positive family whose ratio is nondecreasing (in the cross-multiplied form
`hcross`) makes `Z₁F₂ - Z₂F₁` change sign at most once, from `-` to `+`. -/
theorem exists_crossing {a b : ℝ} {F₁ F₂ : ℝ → ℝ} {Z₁ Z₂ : ℝ}
    (hF₁ : ∀ p ∈ Set.Ico a b, 0 < F₁ p)
    (hcross : ∀ p ∈ Set.Ico a b, ∀ q ∈ Set.Ico a b, p ≤ q → F₂ p * F₁ q ≤ F₂ q * F₁ p)
    (hZ₁ : 0 < Z₁) (hab : a ≤ b) :
    ∃ c ∈ Set.Icc a b,
      (∀ p ∈ Set.Ico a c, Z₁ * F₂ p - Z₂ * F₁ p ≤ 0) ∧
      (∀ p ∈ Set.Ioo c b, 0 ≤ Z₁ * F₂ p - Z₂ * F₁ p) := by
  set S : Set ℝ := {p | p ∈ Set.Ico a b ∧ 0 ≤ Z₁ * F₂ p - Z₂ * F₁ p} with hS
  have hup : ∀ x ∈ S, ∀ p ∈ Set.Ico a b, x ≤ p → p ∈ S := by
    intro x hx p hp hxp
    refine ⟨hp, ?_⟩
    have hFx : (0:ℝ) < F₁ x := hF₁ x hx.1
    have hFp : (0:ℝ) < F₁ p := hF₁ p hp
    have hcr := hcross x hx.1 p hp hxp
    nlinarith [hx.2, hFx, hFp, hcr, hZ₁]
  rcases Set.eq_empty_or_nonempty S with hemp | hne
  · refine ⟨b, ⟨hab, le_refl b⟩, ?_, ?_⟩
    · intro p hp
      by_contra hcon
      have : p ∈ S := ⟨⟨hp.1, hp.2⟩, le_of_lt (not_le.mp hcon)⟩
      simp only [hemp, Set.mem_empty_iff_false] at this
    · intro p hp; exact absurd hp.2 (not_lt.mpr hp.1.le)
  · have hbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
    set c := sInf S with hc
    have hca : a ≤ c := le_csInf hne (fun x hx => hx.1.1)
    have hcb : c ≤ b := by
      obtain ⟨x, hx⟩ := hne
      exact le_trans (csInf_le hbdd hx) hx.1.2.le
    refine ⟨c, ⟨hca, hcb⟩, ?_, ?_⟩
    · intro p hp
      by_contra hcon
      have hmem : p ∈ S := ⟨⟨hp.1, lt_of_lt_of_le hp.2 hcb⟩, le_of_lt (not_le.mp hcon)⟩
      exact absurd (csInf_le hbdd hmem) (not_le.mpr hp.2)
    · intro p hp
      obtain ⟨x, hxS, hxp⟩ := exists_lt_of_csInf_lt hne hp.1
      exact (hup x hxS p ⟨le_trans hxS.1.1 hxp.le, hp.2⟩ hxp.le).2

/-! ## Folding the beta integral onto `[1/2,1]` -/

theorem uIcc_zero_half_subset : Set.uIcc (0:ℝ) (1/2) ⊆ Set.uIcc (0:ℝ) 1 := by
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact Set.Icc_subset_Icc le_rfl (by norm_num)

theorem uIcc_half_one_subset : Set.uIcc (1/2:ℝ) 1 ⊆ Set.uIcc (0:ℝ) 1 := by
  rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact Set.Icc_subset_Icc (by norm_num) le_rfl

theorem intervalIntegrable_betaKer' {s d : ℝ} (hlo : 0 < s / 2 + d) (hhi : 0 < s / 2 - d) :
    IntervalIntegrable (betaKer s d) volume 0 1 := by
  simpa [betaKer] using intervalIntegrable_betaKer hlo hhi

theorem intervalIntegrable_mul_betaKer {H : ℝ → ℝ} (hHc : Continuous H) {s d : ℝ}
    (hlo : 0 < s / 2 + d) (hhi : 0 < s / 2 - d) :
    IntervalIntegrable (fun p => H p * betaKer s d p) volume 0 1 :=
  (intervalIntegrable_betaKer' hlo hhi).continuousOn_mul hHc.continuousOn

/-- For `H` symmetric about `1/2`, the beta integral over `[0,1]` equals the integral of
`H` against the folded kernel over `[1/2,1]`. -/
theorem integral_fold {H : ℝ → ℝ} (hHsymm : ∀ p, H (1 - p) = H p) (hHc : Continuous H)
    {s d : ℝ} (hlo : 0 < s / 2 + d) (hhi : 0 < s / 2 - d) :
    (∫ p in (0:ℝ)..1, H p * betaKer s d p) = ∫ p in (1/2:ℝ)..1, H p * foldKer s d p := by
  set f : ℝ → ℝ := fun p => H p * betaKer s d p with hfdef
  have hI : IntervalIntegrable f volume 0 1 := intervalIntegrable_mul_betaKer hHc hlo hhi
  have hI1 : IntervalIntegrable f volume 0 (1/2) := hI.mono_set uIcc_zero_half_subset
  have hI2 : IntervalIntegrable f volume (1/2) 1 := hI.mono_set uIcc_half_one_subset
  have hI3 : IntervalIntegrable (fun p => f (1 - p)) volume (1/2) 1 := by
    have h := hI1.comp_sub_left 1
    rw [show (1:ℝ) - 0 = 1 by norm_num, show (1:ℝ) - 1/2 = 1/2 by norm_num] at h
    exact h.symm
  have hrefl : (∫ p in (1/2:ℝ)..1, f (1 - p)) = ∫ p in (0:ℝ)..(1/2), f p := by
    rw [intervalIntegral.integral_comp_sub_left f (1:ℝ)]
    norm_num
  have hcombine : (∫ p in (1/2:ℝ)..1, H p * foldKer s d p)
      = (∫ p in (1/2:ℝ)..1, f (1 - p)) + ∫ p in (1/2:ℝ)..1, f p := by
    rw [← intervalIntegral.integral_add hI3 hI2]
    refine intervalIntegral.integral_congr (fun p _ => ?_)
    simp only [hfdef, foldKer, hHsymm p]
    ring
  rw [hcombine, hrefl, intervalIntegral.integral_add_adjacent_intervals hI1 hI2]

theorem intervalIntegrable_foldKer {s d : ℝ} (hlo : 0 < s / 2 + d) (hhi : 0 < s / 2 - d) :
    IntervalIntegrable (foldKer s d) volume (1/2) 1 := by
  have hb : IntervalIntegrable (betaKer s d) volume 0 1 := intervalIntegrable_betaKer' hlo hhi
  have hupper : IntervalIntegrable (betaKer s d) volume (1/2) 1 := hb.mono_set uIcc_half_one_subset
  have hlower : IntervalIntegrable (betaKer s d) volume 0 (1/2) := hb.mono_set uIcc_zero_half_subset
  have hreflected : IntervalIntegrable (fun p => betaKer s d (1 - p)) volume (1/2) 1 := by
    have h := hlower.comp_sub_left 1
    rw [show (1:ℝ) - 0 = 1 by norm_num, show (1:ℝ) - 1/2 = 1/2 by norm_num] at h
    exact h.symm
  simpa [foldKer] using hupper.add hreflected

theorem intervalIntegrable_mul_foldKer {H : ℝ → ℝ} (hHc : Continuous H) {s d : ℝ}
    (hlo : 0 < s / 2 + d) (hhi : 0 < s / 2 - d) :
    IntervalIntegrable (fun p => H p * foldKer s d p) volume (1/2) 1 :=
  (intervalIntegrable_foldKer hlo hhi).continuousOn_mul hHc.continuousOn

theorem bmom_eq_integral_foldKer {s d : ℝ} (hlo : 0 < s / 2 + d) (hhi : 0 < s / 2 - d) :
    bmom (s/2 + d) (s/2 - d) = ∫ p in (1/2:ℝ)..1, foldKer s d p := by
  rw [bmom_eq_integral_betaKer]
  have h := integral_fold (H := fun _ => (1:ℝ)) (fun p => rfl) continuous_const hlo hhi
  simp only [one_mul] at h
  exact h

/-- **The recentred difference of two folded beta kernels.**  Each folded kernel
is scaled by the *other's* total mass, so the two carry equal mass and the
difference has none (`integral_foldDiff`).  Both clauses of `lem:beta-order`
come down to the sign of `∫ H · foldDiff` over `[1/2,1]`. -/
noncomputable def foldDiff (s d₁ d₂ p : ℝ) : ℝ :=
  bmom (s/2 + d₁) (s/2 - d₁) * foldKer s d₂ p - bmom (s/2 + d₂) (s/2 - d₂) * foldKer s d₁ p

theorem intervalIntegrable_foldDiff {s d₁ d₂ : ℝ} (hlo₁ : 0 < s / 2 + d₁)
    (hhi₁ : 0 < s / 2 - d₁) (hlo₂ : 0 < s / 2 + d₂) (hhi₂ : 0 < s / 2 - d₂) :
    IntervalIntegrable (foldDiff s d₁ d₂) volume (1/2) 1 :=
  ((intervalIntegrable_foldKer hlo₂ hhi₂).const_mul _).sub
    ((intervalIntegrable_foldKer hlo₁ hhi₁).const_mul _)

/-- **The recentred difference has zero mass.**  Each folded kernel integrates
to its own beta moment over `[1/2,1]`, so the cross-scaled difference integrates
to `Z₁Z₂ - Z₂Z₁ = 0`.  This is what puts the crossing point of `exists_crossing`
strictly inside the interval. -/
theorem integral_foldDiff {s d₁ d₂ : ℝ} (hlo₁ : 0 < s / 2 + d₁) (hhi₁ : 0 < s / 2 - d₁)
    (hlo₂ : 0 < s / 2 + d₂) (hhi₂ : 0 < s / 2 - d₂) :
    ∫ p in (1/2:ℝ)..1, foldDiff s d₁ d₂ p = 0 := by
  unfold foldDiff
  rw [intervalIntegral.integral_sub
      ((intervalIntegrable_foldKer hlo₂ hhi₂).const_mul _)
      ((intervalIntegrable_foldKer hlo₁ hhi₁).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← bmom_eq_integral_foldKer hlo₁ hhi₁, ← bmom_eq_integral_foldKer hlo₂ hhi₂]
  ring

/-- Linearity of the integral against `foldDiff`, in the form both clauses of
`lem:beta-order` read the conclusion off. -/
theorem integral_mul_foldDiff {H : ℝ → ℝ} (hHc : Continuous H) {s d₁ d₂ : ℝ}
    (hlo₁ : 0 < s / 2 + d₁) (hhi₁ : 0 < s / 2 - d₁)
    (hlo₂ : 0 < s / 2 + d₂) (hhi₂ : 0 < s / 2 - d₂) :
    ∫ p in (1/2:ℝ)..1, H p * foldDiff s d₁ d₂ p
      = bmom (s/2 + d₁) (s/2 - d₁) * (∫ p in (1/2:ℝ)..1, H p * foldKer s d₂ p)
        - bmom (s/2 + d₂) (s/2 - d₂) * (∫ p in (1/2:ℝ)..1, H p * foldKer s d₁ p) := by
  have hsplit : ∀ p : ℝ, H p * foldDiff s d₁ d₂ p
      = bmom (s/2 + d₁) (s/2 - d₁) * (H p * foldKer s d₂ p)
        - bmom (s/2 + d₂) (s/2 - d₂) * (H p * foldKer s d₁ p) := by
    intro p; unfold foldDiff; ring
  simp_rw [hsplit]
  rw [intervalIntegral.integral_sub
      ((intervalIntegrable_mul_foldKer hHc hlo₂ hhi₂).const_mul _)
      ((intervalIntegrable_mul_foldKer hHc hlo₁ hhi₁).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-! ## The likelihood-ratio order (`lem:beta-order`) -/

/-- **Reflection.**  A function symmetric about `1/2` and nondecreasing on `[0,1/2]` is
nonincreasing on `[1/2,1]`.  This is what lets the folded integrand of `integral_fold` be
compared against a sign-changing weight on the upper half alone. -/
theorem antitoneOn_of_symm_monotoneOn {H : ℝ → ℝ} (hHsymm : ∀ p, H (1 - p) = H p)
    (hHmono : MonotoneOn H (Set.Icc 0 (1 / 2))) : AntitoneOn H (Set.Icc (1 / 2) 1) := by
  intro p hp q hq hpq
  have hq' : (1 - q) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hq.2], by linarith [hq.1]⟩
  have hp' : (1 - p) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hstep := hHmono hq' hp' (by linarith)
  rwa [hHsymm, hHsymm] at hstep

/-- The strict form of `antitoneOn_of_symm_monotoneOn`. -/
theorem strictAntiOn_of_symm_strictMonoOn {H : ℝ → ℝ} (hHsymm : ∀ p, H (1 - p) = H p)
    (hHmono : StrictMonoOn H (Set.Icc 0 (1 / 2))) : StrictAntiOn H (Set.Icc (1 / 2) 1) := by
  intro p hp q hq hpq
  have hq' : (1 - q) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hq.2], by linarith [hq.1]⟩
  have hp' : (1 - p) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hstep := hHmono hq' hp' (by linarith)
  rwa [hHsymm, hHsymm] at hstep

/-- **`lem:beta-order`.**  Fix a parameter sum `s > 0`.  For `H` symmetric about `1/2` and
nondecreasing on `[0,1/2]`, growing the imbalance `d` decreases the beta average of `H`.
Stated with the normalizing beta moments cleared, so no quotient appears. -/
theorem beta_order {H : ℝ → ℝ} (hHsymm : ∀ p, H (1 - p) = H p) (hHc : Continuous H)
    (hHmono : MonotoneOn H (Set.Icc 0 (1 / 2)))
    {s d₁ d₂ : ℝ} (hd₁ : 0 ≤ d₁) (hd : d₁ ≤ d₂) (hd₂ : d₂ < s / 2) :
    (∫ p in (0:ℝ)..1, H p * betaKer s d₂ p) * bmom (s/2 + d₁) (s/2 - d₁)
      ≤ (∫ p in (0:ℝ)..1, H p * betaKer s d₁ p) * bmom (s/2 + d₂) (s/2 - d₂) := by
  have hs2 : (0:ℝ) < s/2 := lt_of_le_of_lt (hd₁.trans hd) hd₂
  have hlo₁ : (0:ℝ) < s/2 + d₁ := by linarith
  have hlo₂ : (0:ℝ) < s/2 + d₂ := by linarith [hd₁.trans hd]
  have hhi₁ : (0:ℝ) < s/2 - d₁ := by linarith
  have hhi₂ : (0:ℝ) < s/2 - d₂ := by linarith
  have hHanti := antitoneOn_of_symm_monotoneOn hHsymm hHmono
  rw [integral_fold hHsymm hHc hlo₁ hhi₁, integral_fold hHsymm hHc hlo₂ hhi₂]
  obtain ⟨c, hcmem, hclo, hchi⟩ :=
    exists_crossing (F₁ := foldKer s d₁) (F₂ := foldKer s d₂)
      (Z₁ := bmom (s/2 + d₁) (s/2 - d₁)) (Z₂ := bmom (s/2 + d₂) (s/2 - d₂))
      (fun p hp => foldKer_pos s d₁ (by linarith [hp.1]) hp.2)
      (fun p hp q hq hpq => foldKer_cross hd₁ hd hp.1 hpq hq.2)
      (bmom_pos hlo₁ hhi₁) (by norm_num)
  have hmain : ∫ p in (1/2:ℝ)..1, H p * foldDiff s d₁ d₂ p ≤ 0 :=
    integral_mul_nonpos_of_crossing (g := foldDiff s d₁ d₂) (by norm_num) hcmem hHanti hclo hchi
      (intervalIntegrable_foldDiff hlo₁ hhi₁ hlo₂ hhi₂)
      ((intervalIntegrable_foldDiff hlo₁ hhi₁ hlo₂ hhi₂).continuousOn_mul hHc.continuousOn)
      (integral_foldDiff hlo₁ hhi₁ hlo₂ hhi₂)
  rw [integral_mul_foldDiff hHc hlo₁ hhi₁ hlo₂ hhi₂] at hmain
  linarith

/-! ## The strict clause of `lem:beta-order`

The nonstrict chain above run again with every inequality strict.  Two things
change.  The cross-multiplied `cosh` inequality becomes strict, which makes the
crossing of `Z₁F₂ - Z₂F₁` nondegenerate: the difference is strictly negative
below the crossing point and strictly positive above it.  And a difference of one
strict sign throughout `(1/2,1)` cannot integrate to zero, so the crossing point
is interior — which is what leaves two subintervals of positive length on which
the recentred integrand is strictly signed. -/

/-- `logit` is strictly increasing on `(0,1)`. -/
theorem logit_strictMono {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    logit p < logit q := by
  have hlogp : Real.log p < Real.log q := Real.log_lt_log hp hpq
  have hlog1p : Real.log (1 - q) < Real.log (1 - p) := Real.log_lt_log (by linarith) (by linarith)
  simp only [logit]; linarith

/-- `cosh(d₂x)cosh(d₁y) < cosh(d₂y)cosh(d₁x)` for `0 ≤ d₁ < d₂` and `0 ≤ x < y`:
the strict form of `cosh_ratio_cross`.  Only the first of the two summands of
`2 cosh A cosh B = cosh(A+B) + cosh(A-B)` becomes strict, `d₂y + d₁x` exceeding
`d₂x + d₁y` by `(d₂-d₁)(y-x) > 0`; the second stays as it was. -/
theorem cosh_ratio_cross_strict {d₁ d₂ x y : ℝ} (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂)
    (hx : 0 ≤ x) (hxy : x < y) :
    Real.cosh (d₂ * x) * Real.cosh (d₁ * y) < Real.cosh (d₂ * y) * Real.cosh (d₁ * x) := by
  have hy : 0 ≤ y := hx.trans hxy.le
  have hd₂ : 0 ≤ d₂ := hd₁.trans hd.le
  have hplus : Real.cosh (d₂ * x + d₁ * y) < Real.cosh (d₂ * y + d₁ * x) := by
    rw [Real.cosh_lt_cosh, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hd) (sub_pos.mpr hxy)]
  have hminus : Real.cosh (d₂ * x - d₁ * y) ≤ Real.cosh (d₂ * y - d₁ * x) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (show (0:ℝ) ≤ d₂ * y - d₁ * x by nlinarith), abs_le]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hd.le) (add_nonneg hx hy),
      mul_nonneg (add_nonneg hd₁ hd₂) (sub_nonneg.mpr hxy.le)]
  nlinarith [two_mul_cosh_mul_cosh (d₂ * x) (d₁ * y),
    two_mul_cosh_mul_cosh (d₂ * y) (d₁ * x)]

/-- Strict single-crossing of the folded kernels on `[1/2,1)`: the strict form of
`foldKer_cross`, written multiplicatively. -/
theorem foldKer_cross_strict {s d₁ d₂ p q : ℝ} (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂)
    (hp : 1 / 2 ≤ p) (hpq : p < q) (hq : q < 1) :
    foldKer s d₂ p * foldKer s d₁ q < foldKer s d₂ q * foldKer s d₁ p := by
  have hp0 : (0:ℝ) < p := by linarith
  have hp1 : p < 1 := hpq.trans hq
  have hq0 : (0:ℝ) < q := by linarith
  have hWp : (0:ℝ) < (p * (1 - p)) ^ (s/2 - 1) := Real.rpow_pos_of_pos (by nlinarith) _
  have hWq : (0:ℝ) < (q * (1 - q)) ^ (s/2 - 1) := Real.rpow_pos_of_pos (by nlinarith) _
  rw [foldKer_eq_cosh s d₂ hp0 hp1, foldKer_eq_cosh s d₁ hq0 hq,
      foldKer_eq_cosh s d₂ hq0 hq, foldKer_eq_cosh s d₁ hp0 hp1]
  have hcore := cosh_ratio_cross_strict hd₁ hd (logit_nonneg hp hp1) (logit_strictMono hp0 hpq hq)
  nlinarith [mul_pos hWp hWq, hcore]

/-- The strict form of `exists_crossing`: a strictly increasing ratio makes
`Z₁F₂ - Z₂F₁` strictly negative below the crossing point and strictly positive
above it.  Above a point where the difference is nonnegative the strict ratio
inequality forces it positive, which is both halves at once. -/
theorem exists_crossing_strict {a b : ℝ} {F₁ F₂ : ℝ → ℝ} {Z₁ Z₂ : ℝ}
    (hF₁ : ∀ p ∈ Set.Ico a b, 0 < F₁ p)
    (hcross : ∀ p ∈ Set.Ico a b, ∀ q ∈ Set.Ico a b, p < q → F₂ p * F₁ q < F₂ q * F₁ p)
    (hZ₁ : 0 < Z₁) (hab : a ≤ b) :
    ∃ c ∈ Set.Icc a b,
      (∀ p ∈ Set.Ico a c, Z₁ * F₂ p - Z₂ * F₁ p < 0) ∧
      (∀ p ∈ Set.Ioo c b, 0 < Z₁ * F₂ p - Z₂ * F₁ p) := by
  set S : Set ℝ := {p | p ∈ Set.Ico a b ∧ 0 ≤ Z₁ * F₂ p - Z₂ * F₁ p} with hS
  have hup : ∀ x ∈ S, ∀ p ∈ Set.Ico a b, x < p → 0 < Z₁ * F₂ p - Z₂ * F₁ p := by
    intro x hx p hp hxp
    have hFx : (0:ℝ) < F₁ x := hF₁ x hx.1
    have hFp : (0:ℝ) < F₁ p := hF₁ p hp
    have hcr := hcross x hx.1 p hp hxp
    nlinarith [hx.2, hFx, hFp, hcr, hZ₁]
  rcases Set.eq_empty_or_nonempty S with hemp | hne
  · refine ⟨b, ⟨hab, le_refl b⟩, ?_, ?_⟩
    · intro p hp
      by_contra hcon
      have : p ∈ S := ⟨⟨hp.1, hp.2⟩, not_lt.mp hcon⟩
      simp only [hemp, Set.mem_empty_iff_false] at this
    · intro p hp; exact absurd hp.2 (not_lt.mpr hp.1.le)
  · have hbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
    set c := sInf S with hc
    have hca : a ≤ c := le_csInf hne (fun x hx => hx.1.1)
    have hcb : c ≤ b := by
      obtain ⟨x, hx⟩ := hne
      exact le_trans (csInf_le hbdd hx) hx.1.2.le
    refine ⟨c, ⟨hca, hcb⟩, ?_, ?_⟩
    · intro p hp
      by_contra hcon
      have hmem : p ∈ S := ⟨⟨hp.1, lt_of_lt_of_le hp.2 hcb⟩, not_lt.mp hcon⟩
      exact absurd (csInf_le hbdd hmem) (not_le.mpr hp.2)
    · intro p hp
      obtain ⟨x, hxS, hxp⟩ := exists_lt_of_csInf_lt hne hp.1
      exact hup x hxS p ⟨le_trans hxS.1.1 hxp.le, hp.2⟩ hxp

/-- **The crossing point is interior.**  A `g` strictly negative below `c`,
strictly positive above it, and of zero total mass cannot have `c` at either
endpoint: at `c = a` the function would be strictly positive throughout `(a,b)`
and at `c = b` strictly negative, and either way the integral could not vanish.

This is what leaves two subintervals of positive length for the strict estimate,
and it is the only place the zero-mass hypothesis does more than recentre. -/
theorem crossing_mem_Ioo {a b c : ℝ} (hab : a < b) {g : ℝ → ℝ} (hc : c ∈ Set.Icc a b)
    (hlo : ∀ p ∈ Set.Ico a c, g p < 0) (hhi : ∀ p ∈ Set.Ioo c b, 0 < g p)
    (hg : IntervalIntegrable g volume a b) (hg0 : ∫ p in a..b, g p = 0) :
    c ∈ Set.Ioo a b := by
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hc.1 with heq | hlt
    · exfalso
      have hpos : 0 < ∫ p in a..b, g p :=
        intervalIntegral_pos_of_pos_on hg (fun x hx => hhi x (by rw [← heq]; exact hx)) hab
      rw [hg0] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact hlt
  · rcases eq_or_lt_of_le hc.2 with heq | hlt
    · exfalso
      have hpos : 0 < ∫ p in a..b, -g p := by
        refine intervalIntegral_pos_of_pos_on hg.neg (fun x hx => ?_) hab
        have hx' : g x < 0 := hlo x ⟨hx.1.le, by rw [heq]; exact hx.2⟩
        linarith
      rw [intervalIntegral.integral_neg, hg0] at hpos
      simp at hpos
    · exact hlt

/-- The strict form of `integral_mul_nonpos_of_crossing`.  `crossing_mem_Ioo`
puts `c` in the interior, and on each of the two subintervals it leaves, the
recentred integrand `-(H - H c)g` is a product of a nonzero factor with a factor
of the opposite sign. -/
theorem integral_mul_neg_of_crossing {a b c : ℝ} (hab : a < b) {H g : ℝ → ℝ}
    (hc : c ∈ Set.Icc a b)
    (hH : StrictAntiOn H (Set.Icc a b))
    (hlo : ∀ p ∈ Set.Ico a c, g p < 0)
    (hhi : ∀ p ∈ Set.Ioo c b, 0 < g p)
    (hg : IntervalIntegrable g volume a b)
    (hHg : IntervalIntegrable (fun p => H p * g p) volume a b)
    (hg0 : ∫ p in a..b, g p = 0) :
    ∫ p in a..b, H p * g p < 0 := by
  obtain ⟨hac, hcb⟩ := crossing_mem_Ioo hab hc hlo hhi hg hg0
  have hφi : IntervalIntegrable (fun p => -((H p - H c) * g p)) volume a b := by
    have heq : (fun p => -((H p - H c) * g p)) = fun p => -(H p * g p) + H c * g p := by
      funext p; ring
    rw [heq]
    exact hHg.neg.add (hg.const_mul (H c))
  have hkey : ∫ p in a..b, (-((H p - H c) * g p)) = -∫ p in a..b, H p * g p := by
    rw [intervalIntegral.integral_neg, integral_mul_sub_const c hg hHg hg0]
  have hsub1 : Set.uIcc a c ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le hac.le, Set.uIcc_of_le hab.le]
    exact Set.Icc_subset_Icc le_rfl hcb.le
  have hsub2 : Set.uIcc c b ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le hcb.le, Set.uIcc_of_le hab.le]
    exact Set.Icc_subset_Icc hac.le le_rfl
  have hpos1 : 0 < ∫ p in a..c, (-((H p - H c) * g p)) := by
    refine intervalIntegral_pos_of_pos_on (hφi.mono_set hsub1) (fun x hx => ?_) hac
    have hxI : x ∈ Set.Icc a b := ⟨hx.1.le, (hx.2.trans hcb).le⟩
    have hHlt : H c < H x := hH hxI hc hx.2
    have hgneg : g x < 0 := hlo x ⟨hx.1.le, hx.2⟩
    nlinarith
  have hpos2 : 0 < ∫ p in c..b, (-((H p - H c) * g p)) := by
    refine intervalIntegral_pos_of_pos_on (hφi.mono_set hsub2) (fun x hx => ?_) hcb
    have hxI : x ∈ Set.Icc a b := ⟨(hac.trans hx.1).le, hx.2.le⟩
    have hHgt : H x < H c := hH hc hxI hx.1
    have hgpos : 0 < g x := hhi x hx
    nlinarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hφi.mono_set hsub1) (hφi.mono_set hsub2)
  linarith [hadd, hkey, hpos1, hpos2]

/-- Nondecreasing on a closed interval and strictly increasing on its interior
gives strictly increasing on the closed interval: two interior points
`p < x < y < q` carry the strict step and monotonicity carries the ends.  This is
what lets the strict clause be stated at the paper's own hypothesis, strict
increase on the open interval `(0,1/2)`. -/
theorem strictMonoOn_of_monotoneOn_Ioo {H : ℝ → ℝ} {a b : ℝ}
    (hmono : MonotoneOn H (Set.Icc a b)) (hstrict : StrictMonoOn H (Set.Ioo a b)) :
    StrictMonoOn H (Set.Icc a b) := by
  intro p hp q hq hpq
  have hx : (2 * p + q) / 3 ∈ Set.Ioo a b :=
    ⟨by have := hp.1; linarith, by have := hq.2; linarith⟩
  have hy : (p + 2 * q) / 3 ∈ Set.Ioo a b :=
    ⟨by have := hp.1; linarith, by have := hq.2; linarith⟩
  have hleft : H p ≤ H ((2 * p + q) / 3) := hmono hp ⟨hx.1.le, hx.2.le⟩ (by linarith)
  have hjump : H ((2 * p + q) / 3) < H ((p + 2 * q) / 3) := hstrict hx hy (by linarith)
  have hright : H ((p + 2 * q) / 3) ≤ H q := hmono ⟨hy.1.le, hy.2.le⟩ hq (by linarith)
  linarith

/-- **`lem:beta-order`, strict clause.**  For `H` symmetric about `1/2`,
nondecreasing on `[0,1/2]` and strictly increasing on `(0,1/2)`, growing the
imbalance strictly decreases the beta average of `H`.  Stated with the
normalizing beta moments cleared, as `beta_order` is. -/
theorem beta_order_strict {H : ℝ → ℝ} (hHsymm : ∀ p, H (1 - p) = H p) (hHc : Continuous H)
    (hHmono : MonotoneOn H (Set.Icc 0 (1 / 2)))
    (hHstrict : StrictMonoOn H (Set.Ioo 0 (1 / 2)))
    {s d₁ d₂ : ℝ} (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂) (hd₂ : d₂ < s / 2) :
    (∫ p in (0:ℝ)..1, H p * betaKer s d₂ p) * bmom (s/2 + d₁) (s/2 - d₁)
      < (∫ p in (0:ℝ)..1, H p * betaKer s d₁ p) * bmom (s/2 + d₂) (s/2 - d₂) := by
  have hs2 : (0:ℝ) < s/2 := lt_of_le_of_lt (hd₁.trans hd.le) hd₂
  have hlo₁ : (0:ℝ) < s/2 + d₁ := by linarith
  have hlo₂ : (0:ℝ) < s/2 + d₂ := by linarith [hd₁.trans hd.le]
  have hhi₁ : (0:ℝ) < s/2 - d₁ := by linarith
  have hhi₂ : (0:ℝ) < s/2 - d₂ := by linarith
  have hHsm : StrictMonoOn H (Set.Icc 0 (1/2)) :=
    strictMonoOn_of_monotoneOn_Ioo hHmono hHstrict
  have hHanti := strictAntiOn_of_symm_strictMonoOn hHsymm hHsm
  rw [integral_fold hHsymm hHc hlo₁ hhi₁, integral_fold hHsymm hHc hlo₂ hhi₂]
  obtain ⟨c, hcmem, hclo, hchi⟩ :=
    exists_crossing_strict (F₁ := foldKer s d₁) (F₂ := foldKer s d₂)
      (Z₁ := bmom (s/2 + d₁) (s/2 - d₁)) (Z₂ := bmom (s/2 + d₂) (s/2 - d₂))
      (fun p hp => foldKer_pos s d₁ (by linarith [hp.1]) hp.2)
      (fun p hp q hq hpq => foldKer_cross_strict hd₁ hd hp.1 hpq hq.2)
      (bmom_pos hlo₁ hhi₁) (by norm_num)
  have hmain : ∫ p in (1/2:ℝ)..1, H p * foldDiff s d₁ d₂ p < 0 :=
    integral_mul_neg_of_crossing (g := foldDiff s d₁ d₂) (by norm_num) hcmem hHanti hclo hchi
      (intervalIntegrable_foldDiff hlo₁ hhi₁ hlo₂ hhi₂)
      ((intervalIntegrable_foldDiff hlo₁ hhi₁ hlo₂ hhi₂).continuousOn_mul hHc.continuousOn)
      (integral_foldDiff hlo₁ hhi₁ hlo₂ hhi₂)
  rw [integral_mul_foldDiff hHc hlo₁ hhi₁ hlo₂ hhi₂] at hmain
  linarith

end CubicPochhammer
