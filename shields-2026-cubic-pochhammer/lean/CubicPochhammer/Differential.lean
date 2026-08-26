/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Consequences
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The differential Turánian

Formalizes `shields-2026-cubic-pochhammer.tex`,
`subsec:differential-turan-inequality` (`cor:differential`).

`Consequences.dcoeff` is the antidiagonal sum `Σ_{k+l=m}(a_k' a_l' - a_k a_l'')`
of the coefficient functions `a_n(μ) = f_n (μ)_{3n}/(3n-1)!` of `eq:F-def`.
This module identifies it with the analytic object of `cor:differential` and
extracts the positivity that `thm:main` supplies.

## The identification

`dcoeff_tsum_eq` is `cor:differential`'s left-hand side:

  `(∂_μ F_f(μ;x))² - F_f(μ;x) ∂_μ² F_f(μ;x) = Σ_m dcoeff f m μ · x^m`

for `0 < x < y` with `Σ f_n y^n` convergent.  Both `μ`-derivatives are taken
term by term.  What licenses that is the same polynomial majorant `cor:ordinary`
uses on the undifferentiated series: `∂_μ (μ)_N` and `∂_μ² (μ)_N` are sums of at
most `N` and `N²` products of the factors `μ + j` with one or two of them
dropped, so on `|μ| < M` with `1 ≤ M` they are bounded by `N (M)_N` and
`N² (M)_N`, and `poch_le_factorial_mul_pow` turns that into a
polynomial-times-geometric majorant.  The Cauchy product then runs exactly as in
`fser_mul`.

## The positivity `thm:main` gives

Along the antidiagonal `Φ_m(d) = C_{m,f}(μ+d, μ-d)` of `eq:C-def` the paper's
identity `[x^m][(∂_μ F_f)² - F_f ∂_μ² F_f] = -Φ_m''(0)/2` is exact and
algebraic: `psiD2_at_zero`, whose whole content is that the reflection
`k ↔ m-k` makes the two outer terms of `Φ_m''(0)` equal.  `thm:main` makes
`d = 0` a maximum of `Φ_m` on `|d| ≤ μ`, so `deriv2_nonpos_of_max` gives

  `0 ≤ dcoeff f m μ`   (`μ ≥ 0`, weights nondecreasing toward the center),

as `dcoeff_nonneg`, with `dcoeff_nonneg_of_logConcave` at the paper's own
sequence hypothesis.  That is the "nonnegative coefficients" half of
`cor:differential`; with `dcoeff_eq_zero_of_weights` and
`dcoeff_at_zero_pos_iff` it settles the vanishing half at every `μ` and the
exact support at `μ = 0`.

## `m = 2`, in both directions

`pochD_sq_sub_mul_pochD2` is the exact polynomial identity

  `((μ)_N')² - (μ)_N (μ)_N'' = Σ_{i<N} (∏_{j≠i}(μ+j))²`,

so `(μ)_N` is strictly log-concave on `[0,∞)`.  At `m = 2` the antidiagonal has
the single term `k = 1`, and `dcoeff_two_pos_iff` closes `cor:differential`
there for every `μ ≥ 0`: the coefficient is positive exactly when `f_1 > 0`,
which is `2 ∈ I+I`.

**Not proved here: strict positivity for `μ > 0` and `m ∈ I+I` at `m ≥ 3`.**
The gap and what it would take are stated below.

Sorry-free and axiom-free.

## Main definitions

* `pochD`, `pochD2` --- the first two `μ`-derivatives of `(μ)_N`, as sums of
  products with one or two factors dropped.
* `aserD`, `aserD2` --- the same for the coefficient `a_n(μ)` of `eq:F-def`.
* `majTail` --- the tail of the majorant series, the constant of the
  Weierstrass comparison.
* `psi`, `psiD`, `psiD2` --- `Φ_m(d) = C_{m,f}(μ+d, μ-d)` and its two
  `d`-derivatives, written so that differentiation is termwise.

## Main statements

* `abs_pochD_le`, `abs_pochD2_le`, `majorant_bound` --- the
  polynomial-times-geometric majorant that licenses term-by-term
  differentiation.
* `hasDerivAt_fser`, `hasDerivAt_deriv_fser` --- the two `μ`-derivatives of
  `eq:F-def` taken term by term.
* `dcoeff_tsum_eq` --- `cor:differential`'s left-hand side as `Σ_m dcoeff · x^m`.
* `dcoeff_eq_sum`, `psiD2_at_zero` --- the identity
  `[x^m][(∂_μ F_f)² - F_f ∂_μ² F_f] = -Φ_m''(0)/2`.
* `dcoeff_nonneg_of_logConcave` --- the positivity `thm:main` supplies.
* `dcoeff_two_pos_iff` --- the degree-two coefficient, where strictness is exact.

## References

* `shields-2026-cubic-pochhammer.tex`,
  `subsec:differential-turan-inequality` (`cor:differential`), `eq:C-def`,
  `eq:F-def`.
-/

open scoped BigOperators
open Set

namespace CubicPochhammer

/-! ### `μ`-derivatives of the Pochhammer symbol

`poch μ N = ∏_{j<N} (μ + j)` is a polynomial in `μ`, and its first two
derivatives are the sums over which one or two factors are dropped. -/

/-- `∂_μ (μ)_N = Σ_{i<N} ∏_{j<N, j≠i} (μ+j)`. -/
noncomputable def pochD (μ : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ∏ j ∈ (Finset.range N).erase i, (μ + (j : ℝ))

/-- `∂_μ² (μ)_N = Σ_{i<N} Σ_{i'≠i} ∏_{j≠i,i'} (μ+j)`. -/
noncomputable def pochD2 (μ : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ i' ∈ (Finset.range N).erase i,
    ∏ j ∈ ((Finset.range N).erase i).erase i', (μ + (j : ℝ))

theorem hasDerivAt_poch (μ : ℝ) (N : ℕ) :
    HasDerivAt (fun t : ℝ => poch t N) (pochD μ N) μ := by
  have h : HasDerivAt (fun t : ℝ => ∏ i ∈ Finset.range N, (t + (i : ℝ)))
      (∑ i ∈ Finset.range N, (∏ j ∈ (Finset.range N).erase i, (μ + (j : ℝ))) • (1 : ℝ)) μ :=
    HasDerivAt.fun_finsetProd fun i _ => (hasDerivAt_id μ).add_const (i : ℝ)
  simpa [poch, pochD] using h

theorem hasDerivAt_pochD (μ : ℝ) (N : ℕ) :
    HasDerivAt (fun t : ℝ => pochD t N) (pochD2 μ N) μ := by
  rw [pochD2]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h : HasDerivAt (fun t : ℝ => ∏ j ∈ (Finset.range N).erase i, (t + (j : ℝ)))
      (∑ i' ∈ (Finset.range N).erase i,
        (∏ j ∈ ((Finset.range N).erase i).erase i', (μ + (j : ℝ))) • (1 : ℝ)) μ :=
    HasDerivAt.fun_finsetProd fun j _ => (hasDerivAt_id μ).add_const (j : ℝ)
  simpa using h

/-! ### The majorant `(M)_N` for the two derivatives

For `1 ≤ M` every factor `M + j` is at least one, so dropping factors only
decreases the product and the whole family is dominated by `(M)_N`. -/

/-- A partial product of the factors of `(M)_N`, evaluated at any `|μ| ≤ M`, is
bounded in absolute value by `(M)_N` itself: the factors dominate termwise, and
those left out are at least one. -/
theorem abs_prod_sub_le {μ M : ℝ} (hM : 1 ≤ M) (hμ : |μ| ≤ M) {s : Finset ℕ} {N : ℕ}
    (hs : s ⊆ Finset.range N) : |∏ j ∈ s, (μ + (j : ℝ))| ≤ poch M N := by
  have hM0 : (0:ℝ) ≤ M := by linarith
  have hfac : ∀ j : ℕ, (1:ℝ) ≤ M + (j : ℝ) := fun j => by
    have : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hprod_le : |∏ j ∈ s, (μ + (j : ℝ))| ≤ ∏ j ∈ s, (M + (j : ℝ)) := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod (fun j _ => abs_nonneg _) fun j _ => ?_
    have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hμ' := abs_le.mp hμ
    exact abs_le.mpr ⟨by linarith [hμ'.1], by linarith [hμ'.2]⟩
  have hshift_le : ∏ j ∈ s, (M + (j : ℝ)) ≤ poch M N := by
    have hsplit := Finset.prod_sdiff (f := fun j : ℕ => M + (j : ℝ)) hs
    have hone : (1:ℝ) ≤ ∏ j ∈ Finset.range N \ s, (M + (j : ℝ)) := by
      calc (1:ℝ) = ∏ _j ∈ Finset.range N \ s, (1:ℝ) := by simp
        _ ≤ ∏ j ∈ Finset.range N \ s, (M + (j : ℝ)) :=
            Finset.prod_le_prod (fun _ _ => zero_le_one) fun j _ => hfac j
    have hnn : (0:ℝ) ≤ ∏ j ∈ s, (M + (j : ℝ)) :=
      Finset.prod_nonneg fun j _ => by linarith [hfac j]
    calc ∏ j ∈ s, (M + (j : ℝ))
        ≤ (∏ j ∈ Finset.range N \ s, (M + (j : ℝ))) * ∏ j ∈ s, (M + (j : ℝ)) :=
          le_mul_of_one_le_left hnn hone
      _ = poch M N := by rw [hsplit]; rfl
  exact hprod_le.trans hshift_le

theorem abs_poch_le {μ M : ℝ} (hM : 1 ≤ M) (hμ : |μ| ≤ M) (N : ℕ) :
    |poch μ N| ≤ poch M N :=
  abs_prod_sub_le hM hμ (Finset.Subset.refl _)

theorem abs_pochD_le {μ M : ℝ} (hM : 1 ≤ M) (hμ : |μ| ≤ M) (N : ℕ) :
    |pochD μ N| ≤ (N : ℝ) * poch M N := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Finset.range N, |∏ j ∈ (Finset.range N).erase i, (μ + (j : ℝ))|
      ≤ ∑ _i ∈ Finset.range N, poch M N :=
        Finset.sum_le_sum fun i _ => abs_prod_sub_le hM hμ (Finset.erase_subset _ _)
    _ = (N : ℝ) * poch M N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem abs_pochD2_le {μ M : ℝ} (hM : 1 ≤ M) (hμ : |μ| ≤ M) (N : ℕ) :
    |pochD2 μ N| ≤ (N : ℝ) * (N : ℝ) * poch M N := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hrow : ∀ i ∈ Finset.range N,
      |∑ i' ∈ (Finset.range N).erase i,
        ∏ j ∈ ((Finset.range N).erase i).erase i', (μ + (j : ℝ))| ≤ (N : ℝ) * poch M N := by
    intro i _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hcard : ((Finset.range N).erase i).card ≤ N := by
      calc ((Finset.range N).erase i).card ≤ (Finset.range N).card :=
            Finset.card_le_card (Finset.erase_subset _ _)
        _ = N := Finset.card_range N
    calc ∑ i' ∈ (Finset.range N).erase i,
            |∏ j ∈ ((Finset.range N).erase i).erase i', (μ + (j : ℝ))|
        ≤ ∑ _i' ∈ (Finset.range N).erase i, poch M N :=
          Finset.sum_le_sum fun i' _ => abs_prod_sub_le hM hμ
            ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
      _ = (((Finset.range N).erase i).card : ℝ) * poch M N := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * poch M N := by
          have hp : (0:ℝ) ≤ poch M N := poch_nonneg (by linarith) N
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hp
  calc ∑ i ∈ Finset.range N,
        |∑ i' ∈ (Finset.range N).erase i,
          ∏ j ∈ ((Finset.range N).erase i).erase i', (μ + (j : ℝ))|
      ≤ ∑ _i ∈ Finset.range N, (N : ℝ) * poch M N := Finset.sum_le_sum hrow
    _ = (N : ℝ) * (N : ℝ) * poch M N := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ### `μ`-derivatives of the coefficients of `eq:F-def` -/

/-- `∂_μ a_n(μ)` for the coefficient `a_n(μ) = f_n (μ)_{3n}/(3n-1)!` of
`eq:F-def`, zero at `n = 0` where the coefficient itself is. -/
noncomputable def aserD (f : ℕ → ℝ) (μ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else f n * pochD μ (3 * n) / (Nat.factorial (3 * n - 1) : ℝ)

/-- `∂_μ² a_n(μ)`. -/
noncomputable def aserD2 (f : ℕ → ℝ) (μ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else f n * pochD2 μ (3 * n) / (Nat.factorial (3 * n - 1) : ℝ)

theorem hasDerivAt_aser (f : ℕ → ℝ) (μ : ℝ) (n : ℕ) :
    HasDerivAt (fun t : ℝ => aser f t n) (aserD f μ n) μ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [aserD] using (hasDerivAt_const μ (0:ℝ)).congr_of_eventuallyEq
      (by filter_upwards with t using (aser_zero f t))
  · have hfun : (fun t : ℝ => aser f t n)
        = fun t : ℝ => f n * poch t (3 * n) / (Nat.factorial (3 * n - 1) : ℝ) :=
      funext fun t => aser_of_ne_zero f t hn
    rw [hfun, aserD, if_neg hn]
    exact ((hasDerivAt_poch μ (3 * n)).const_mul (f n)).div_const _

theorem deriv_aser_eq (f : ℕ → ℝ) (μ : ℝ) (n : ℕ) :
    deriv (fun t : ℝ => aser f t n) μ = aserD f μ n :=
  (hasDerivAt_aser f μ n).deriv

theorem deriv_aser_fun_eq (f : ℕ → ℝ) (n : ℕ) :
    (deriv fun t : ℝ => aser f t n) = fun μ : ℝ => aserD f μ n :=
  funext fun μ => deriv_aser_eq f μ n

theorem hasDerivAt_aserD (f : ℕ → ℝ) (μ : ℝ) (n : ℕ) :
    HasDerivAt (fun t : ℝ => aserD f t n) (aserD2 f μ n) μ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [aserD, aserD2] using hasDerivAt_const μ (0:ℝ)
  · have hfun : (fun t : ℝ => aserD f t n)
        = fun t : ℝ => f n * pochD t (3 * n) / (Nat.factorial (3 * n - 1) : ℝ) := by
      funext t; rw [aserD, if_neg hn]
    rw [hfun, aserD2, if_neg hn]
    exact ((hasDerivAt_pochD μ (3 * n)).const_mul (f n)).div_const _

theorem deriv2_aser_eq (f : ℕ → ℝ) (μ : ℝ) (n : ℕ) :
    deriv (deriv fun t : ℝ => aser f t n) μ = aserD2 f μ n := by
  rw [deriv_aser_fun_eq f n]
  exact (hasDerivAt_aserD f μ n).deriv

/-! ### The polynomial-times-geometric majorant for the differentiated series -/

/-- `(M)_{3n} ≤ (3n-1)! · 3n(3n+1)^K` for `0 ≤ M ≤ K` and `n ≥ 1`: the majorant
of `aser_le_bound` with the factorial cleared. -/
theorem poch_le_factorial_pred_mul (K : ℕ) {M : ℝ} (hM : 0 ≤ M) (hK : M ≤ (K : ℝ)) {n : ℕ}
    (hn : n ≠ 0) :
    poch M (3 * n) ≤ (Nat.factorial (3 * n - 1) : ℝ) * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K) := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hpoch := poch_le_factorial_mul_pow K hM hK (3 * n)
  have hcast : ((3 * n : ℕ) : ℝ) + 1 = 3 * (n:ℝ) + 1 := by push_cast; ring
  rw [hcast, factorial_three_mul n hn1] at hpoch
  calc poch M (3 * n) ≤ 3 * (n:ℝ) * (Nat.factorial (3 * n - 1) : ℝ) * (3 * (n:ℝ) + 1) ^ K := hpoch
    _ = (Nat.factorial (3 * n - 1) : ℝ) * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K) := by ring

/-- `(3n)^r · 3n(3n+1)^K ≤ 3n(3n+1)^{K+r}`: the `r` extra factors a derivative
contributes are absorbed into the exponent. -/
theorem poly_bound_mono (K r : ℕ) (n : ℕ) :
    (3 * (n:ℝ)) ^ r * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K)
      ≤ (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ (K + r) := by
  have hn : (0:ℝ) ≤ 3 * (n:ℝ) := by positivity
  have hpow_le : (3 * (n:ℝ)) ^ r ≤ (3 * (n:ℝ) + 1) ^ r :=
    pow_le_pow_left₀ hn (by linarith) r
  have hnn : (0:ℝ) ≤ (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K := by positivity
  calc (3 * (n:ℝ)) ^ r * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K)
      ≤ (3 * (n:ℝ) + 1) ^ r * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K) :=
        mul_le_mul_of_nonneg_right hpow_le hnn
    _ = (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ (K + r) := by rw [pow_add]; ring

/-- **The uniform coefficient bound.** On `|t| ≤ M` with `1 ≤ M ≤ K`, the
`r`-th `μ`-derivative of the degree-`n` coefficient of `eq:F-def` is bounded by
`f_n · 3n(3n+1)^{K+r}`, for `r = 0, 1, 2`: the derivative is a sum of at most
`(3n)^r` partial products of `(t)_{3n}`, each dominated by `(M)_{3n}`. -/
theorem abs_aserD_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {M : ℝ} (K : ℕ) (hM : 1 ≤ M)
    (hK : M ≤ (K : ℝ)) {μ : ℝ} (hμ : |μ| ≤ M) (n : ℕ) :
    |aserD f μ n| ≤ f n * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ (K + 1)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [aserD]
  have hfacpos : (0:ℝ) < (Nat.factorial (3 * n - 1) : ℝ) := by positivity
  rw [aserD, if_neg hn, abs_div, abs_of_pos hfacpos, abs_mul, abs_of_nonneg (hf n),
    div_le_iff₀ hfacpos]
  have hcast : ((3 * n : ℕ) : ℝ) = 3 * (n:ℝ) := by push_cast; ring
  have hd : |pochD μ (3 * n)| ≤ (3 * (n:ℝ)) * poch M (3 * n) := by
    simpa [hcast] using abs_pochD_le hM hμ (3 * n)
  have hpoch := poch_le_factorial_pred_mul K (by linarith) hK hn
  have hstep : f n * |pochD μ (3 * n)|
      ≤ f n * ((3 * (n:ℝ)) * ((Nat.factorial (3 * n - 1) : ℝ)
        * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K))) := by
    refine mul_le_mul_of_nonneg_left (hd.trans ?_) (hf n)
    exact mul_le_mul_of_nonneg_left hpoch (by positivity)
  refine hstep.trans ?_
  have hpb := poly_bound_mono K 1 n
  have : (3 * (n:ℝ)) ^ 1 * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K)
      ≤ (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ (K + 1) := hpb
  have hfn := hf n
  nlinarith [hfacpos.le, sq_nonneg (3 * (n:ℝ)), mul_nonneg hfn hfacpos.le]

theorem abs_aserD2_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {M : ℝ} (K : ℕ) (hM : 1 ≤ M)
    (hK : M ≤ (K : ℝ)) {μ : ℝ} (hμ : |μ| ≤ M) (n : ℕ) :
    |aserD2 f μ n| ≤ f n * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ (K + 2)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [aserD2]
  have hfacpos : (0:ℝ) < (Nat.factorial (3 * n - 1) : ℝ) := by positivity
  rw [aserD2, if_neg hn, abs_div, abs_of_pos hfacpos, abs_mul, abs_of_nonneg (hf n),
    div_le_iff₀ hfacpos]
  have hcast : ((3 * n : ℕ) : ℝ) = 3 * (n:ℝ) := by push_cast; ring
  have hd : |pochD2 μ (3 * n)| ≤ (3 * (n:ℝ)) * (3 * (n:ℝ)) * poch M (3 * n) := by
    simpa [hcast] using abs_pochD2_le hM hμ (3 * n)
  have hpoch := poch_le_factorial_pred_mul K (by linarith) hK hn
  have hstep : f n * |pochD2 μ (3 * n)|
      ≤ f n * ((3 * (n:ℝ)) * (3 * (n:ℝ)) * ((Nat.factorial (3 * n - 1) : ℝ)
        * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K))) := by
    refine mul_le_mul_of_nonneg_left (hd.trans ?_) (hf n)
    exact mul_le_mul_of_nonneg_left hpoch (by positivity)
  refine hstep.trans ?_
  have hpb : (3 * (n:ℝ)) ^ 2 * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K)
      ≤ (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ (K + 2) := poly_bound_mono K 2 n
  have hfn := hf n
  nlinarith [hfacpos.le, mul_nonneg hfn hfacpos.le, sq_nonneg (3 * (n:ℝ))]

/-! ### Termwise differentiation of `F_f(μ;x)` in the parameter -/

/-- The tail sum of the majorant series, the constant of the Weierstrass
comparison. -/
noncomputable def majTail (x y : ℝ) (K : ℕ) : ℝ :=
  ∑' k : ℕ, (3 * (k:ℝ)) * (3 * (k:ℝ) + 1) ^ K * (x / y) ^ k

theorem summable_maj {f : ℕ → ℝ} {x y : ℝ} (hy : Summable fun n => f n * y ^ n) (K : ℕ) :
    Summable fun n => (f n * y ^ n) * majTail x y K :=
  hy.mul_right _

/-- The Weierstrass comparison step: a coefficient bounded by
`f_n · 3n(3n+1)^K` gives a summable bound on `|·| x^n` uniform in the
parameter. -/
theorem majorant_bound {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (K : ℕ) {a : ℝ} {n : ℕ} (ha : |a| ≤ f n * ((3 * (n : ℝ)) * (3 * (n : ℝ) + 1) ^ K)) :
    ‖a * x ^ n‖ ≤ (f n * y ^ n) * majTail x y K := by
  have hy0 : 0 < y := lt_trans hx hxy
  have ht0 : 0 < x / y := by positivity
  have ht1 : x / y < 1 := by rw [div_lt_one hy0]; exact hxy
  have hsum := summable_poly_geom K ht0 ht1
  have hCle : (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K * (x / y) ^ n ≤ majTail x y K :=
    hsum.le_tsum n (fun k _ => by positivity)
  have hxt : x ^ n = y ^ n * (x / y) ^ n := by
    rw [div_pow, mul_div_cancel₀]; positivity
  have hxn : (0:ℝ) ≤ x ^ n := by positivity
  calc ‖a * x ^ n‖ = |a| * x ^ n := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hxn]
    _ ≤ (f n * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K)) * x ^ n :=
        mul_le_mul_of_nonneg_right ha hxn
    _ = (f n * y ^ n) * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K * (x / y) ^ n) := by
        rw [hxt]; ring
    _ ≤ (f n * y ^ n) * majTail x y K :=
        mul_le_mul_of_nonneg_left hCle (mul_nonneg (hf n) (by positivity))

/-- **`∂_μ F_f(μ;x)` term by term.**  The series of `μ`-derivatives is
dominated uniformly on `|μ| < M` by a convergent polynomial-times-geometric
series, so `hasDerivAt_tsum_of_isPreconnected` differentiates `eq:F-def` under
the sum. -/
theorem hasDerivAt_fser {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {x y M : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : Summable fun n => f n * y ^ n) (hM : 1 ≤ M) {μ : ℝ} (hμ : μ ∈ Ioo (-M) M) :
    HasDerivAt (fun t : ℝ => fser f t x) (∑' n, aserD f μ n * x ^ n) μ := by
  set K : ℕ := ⌈M⌉₊ with hKdef
  have hK : M ≤ (K:ℝ) := Nat.le_ceil M
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n => (f n * y ^ n) * majTail x y (K + 1))
    (summable_maj hy (K + 1)) isOpen_Ioo (convex_Ioo (-M) M).isPreconnected
    (fun n z _ => (hasDerivAt_aser f z n).mul_const (x ^ n)) (fun n z hz => ?_)
    (show (0:ℝ) ∈ Ioo (-M) M from ⟨by linarith, by linarith⟩) ?_ hμ
  · refine majorant_bound hf hx hxy (K + 1) ?_
    exact abs_aserD_le hf K hM hK (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) n
  · simp [aser_at_zero]

/-- **`∂_μ² F_f(μ;x)` term by term.**  The same comparison one order up, applied
to the function `μ ↦ ∂_μ F_f(μ;x)` that the previous lemma identifies. -/
theorem hasDerivAt_deriv_fser {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {x y M : ℝ} (hx : 0 < x)
    (hxy : x < y) (hy : Summable fun n => f n * y ^ n) (hM : 1 ≤ M) {μ : ℝ}
    (hμ : μ ∈ Ioo (-M) M) :
    HasDerivAt (deriv fun t : ℝ => fser f t x) (∑' n, aserD2 f μ n * x ^ n) μ := by
  set K : ℕ := ⌈M⌉₊ with hKdef
  have hK : M ≤ (K:ℝ) := Nat.le_ceil M
  have hxy0 : Summable fun n => f n * x ^ n := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hf n) (by positivity))
      (fun n => ?_) hy
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hxy.le n) (hf n)
  have hstep : HasDerivAt (fun z : ℝ => ∑' n, aserD f z n * x ^ n)
      (∑' n, aserD2 f μ n * x ^ n) μ := by
    refine hasDerivAt_tsum_of_isPreconnected (u := fun n => (f n * y ^ n) * majTail x y (K + 2))
      (summable_maj hy (K + 2)) isOpen_Ioo (convex_Ioo (-M) M).isPreconnected
      (fun n z _ => (hasDerivAt_aserD f z n).mul_const (x ^ n)) (fun n z hz => ?_)
      (show (0:ℝ) ∈ Ioo (-M) M from ⟨by linarith, by linarith⟩) ?_ hμ
    · refine majorant_bound hf hx hxy (K + 2) ?_
      exact abs_aserD2_le hf K hM hK (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) n
    · refine Summable.of_norm_bounded (summable_maj (x := x) hy (K + 1)) fun n => ?_
      refine majorant_bound hf hx hxy (K + 1) ?_
      exact abs_aserD_le hf K hM hK (by rw [abs_zero]; linarith) n
  refine hstep.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hμ] with z hz
  exact (hasDerivAt_fser hf hx hxy hy hM hz).deriv

/-! ### The Cauchy product: `dcoeff` is the coefficient of the differential Turánian -/

theorem abs_aser_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {M : ℝ} (K : ℕ) (hM : 1 ≤ M)
    (hK : M ≤ (K : ℝ)) {μ : ℝ} (hμ : |μ| ≤ M) (n : ℕ) :
    |aser f μ n| ≤ f n * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hfacpos : (0:ℝ) < (Nat.factorial (3 * n - 1) : ℝ) := by positivity
  rw [aser_of_ne_zero f μ hn, abs_div, abs_of_pos hfacpos, abs_mul, abs_of_nonneg (hf n),
    div_le_iff₀ hfacpos]
  have hd : |poch μ (3 * n)| ≤ poch M (3 * n) := abs_poch_le hM hμ (3 * n)
  have hpoch := poch_le_factorial_pred_mul K (by linarith) hK hn
  calc f n * |poch μ (3 * n)|
      ≤ f n * ((Nat.factorial (3 * n - 1) : ℝ) * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K)) :=
        mul_le_mul_of_nonneg_left (hd.trans hpoch) (hf n)
    _ = f n * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K) * (Nat.factorial (3 * n - 1) : ℝ) := by ring

/-- Absolute convergence of `eq:F-def` and of both differentiated series, at any
parameter in `(-M, M)`. -/
theorem summable_norm_aserD_family {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {x y M : ℝ} (hx : 0 < x)
    (hxy : x < y) (hy : Summable fun n => f n * y ^ n) (hM : 1 ≤ M) {μ : ℝ} (hμ : |μ| ≤ M) :
    (Summable fun n => ‖aser f μ n * x ^ n‖) ∧ (Summable fun n => ‖aserD f μ n * x ^ n‖)
      ∧ (Summable fun n => ‖aserD2 f μ n * x ^ n‖) := by
  set K : ℕ := ⌈M⌉₊ with hKdef
  have hK : M ≤ (K:ℝ) := Nat.le_ceil M
  refine ⟨?_, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_maj (x := x) hy K)
    exact majorant_bound hf hx hxy K (abs_aser_le hf K hM hK hμ n)
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_maj (x := x) hy (K + 1))
    exact majorant_bound hf hx hxy (K + 1) (abs_aserD_le hf K hM hK hμ n)
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_maj (x := x) hy (K + 2))
    exact majorant_bound hf hx hxy (K + 2) (abs_aserD2_le hf K hM hK hμ n)

/-- **The degree-`m` Cauchy coefficient of the differential Turánian is
`dcoeff`**: the two boundary terms of each convolution vanish because
`eq:F-def` has no constant term, and `x^k x^{m-k} = x^m`. -/
theorem sum_range_dcoeff (f : ℕ → ℝ) (μ x : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      (aserD f μ k * x ^ k * (aserD f μ (m - k) * x ^ (m - k))
        - aser f μ k * x ^ k * (aserD2 f μ (m - k) * x ^ (m - k)))
      = dcoeff f m μ * x ^ m := by
  rw [dcoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hxx : x ^ k * x ^ (m - k) = x ^ m := by
    rw [← pow_add]; congr 1; omega
  rw [deriv_aser_eq, deriv_aser_eq, deriv2_aser_eq, ← hxx]
  ring

/-- **`cor:differential`'s left-hand side.**  For `0 < x` strictly inside the
disc of convergence of `Σ f_n x^n`, the differential Turánian of `eq:F-def` is
the power series whose degree-`m` coefficient is `dcoeff f m μ`:

  `(∂_μ F_f(μ;x))² - F_f(μ;x) ∂_μ² F_f(μ;x) = Σ_m dcoeff f m μ · x^m`.

Both `μ`-derivatives are termwise (`hasDerivAt_fser`, `hasDerivAt_deriv_fser`)
and the Cauchy product is legal because all three series converge absolutely. -/
theorem dcoeff_tsum_eq {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {x y M : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : Summable fun n => f n * y ^ n) (hM : 1 ≤ M) {μ : ℝ} (hμ : μ ∈ Ioo (-M) M) :
    (deriv (fun t : ℝ => fser f t x) μ) ^ 2
        - fser f μ x * deriv (deriv fun t : ℝ => fser f t x) μ
      = ∑' m, dcoeff f m μ * x ^ m := by
  obtain ⟨hn0, hn1, hn2⟩ :=
    summable_norm_aserD_family hf hx hxy hy hM (abs_le.mpr ⟨hμ.1.le, hμ.2.le⟩)
  have hd1 : deriv (fun t : ℝ => fser f t x) μ = ∑' n, aserD f μ n * x ^ n :=
    (hasDerivAt_fser hf hx hxy hy hM hμ).deriv
  have hd2 : deriv (deriv fun t : ℝ => fser f t x) μ = ∑' n, aserD2 f μ n * x ^ n :=
    (hasDerivAt_deriv_fser hf hx hxy hy hM hμ).deriv
  have hP : (∑' n, aserD f μ n * x ^ n) * (∑' n, aserD f μ n * x ^ n)
      = ∑' m, ∑ k ∈ Finset.range (m + 1),
          aserD f μ k * x ^ k * (aserD f μ (m - k) * x ^ (m - k)) :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hn1 hn1
  have hQ : (∑' n, aser f μ n * x ^ n) * (∑' n, aserD2 f μ n * x ^ n)
      = ∑' m, ∑ k ∈ Finset.range (m + 1),
          aser f μ k * x ^ k * (aserD2 f μ (m - k) * x ^ (m - k)) :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hn0 hn2
  have hPs := summable_sum_mul_range_of_summable_norm' hn1 hn1.of_norm hn1 hn1.of_norm
  have hQs := summable_sum_mul_range_of_summable_norm' hn0 hn0.of_norm hn2 hn2.of_norm
  have hterm : ∀ m : ℕ,
      (∑ k ∈ Finset.range (m + 1),
          aserD f μ k * x ^ k * (aserD f μ (m - k) * x ^ (m - k)))
        - (∑ k ∈ Finset.range (m + 1),
          aser f μ k * x ^ k * (aserD2 f μ (m - k) * x ^ (m - k)))
      = dcoeff f m μ * x ^ m := by
    intro m
    rw [← Finset.sum_sub_distrib]
    exact sum_range_dcoeff f μ x m
  have hsub : (∑' m, ∑ k ∈ Finset.range (m + 1),
        aserD f μ k * x ^ k * (aserD f μ (m - k) * x ^ (m - k)))
      - (∑' m, ∑ k ∈ Finset.range (m + 1),
        aser f μ k * x ^ k * (aserD2 f μ (m - k) * x ^ (m - k)))
      = ∑' m, dcoeff f m μ * x ^ m := by
    rw [← hPs.tsum_sub hQs]
    exact tsum_congr hterm
  rw [hd1, hd2, fser, pow_two, hP, hQ]
  exact hsub

/-! ### The antidiagonal `Φ_m(d) = C_{m,f}(μ+d, μ-d)` and its second derivative -/

/-- `Φ_m(d) = C_{m,f}(μ+d, μ-d)` of `cor:differential`, written as the
convolution of `eq:F-def`'s coefficients so that its `d`-derivatives are
termwise. -/
noncomputable def psi (f : ℕ → ℝ) (m : ℕ) (μ d : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), aser f (μ + d) k * aser f (μ - d) (m - k)

/-- `∂_d Φ_m`. -/
noncomputable def psiD (f : ℕ → ℝ) (m : ℕ) (μ d : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (aserD f (μ + d) k * aser f (μ - d) (m - k)
      - aser f (μ + d) k * aserD f (μ - d) (m - k))

/-- `∂_d² Φ_m`. -/
noncomputable def psiD2 (f : ℕ → ℝ) (m : ℕ) (μ d : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (aserD2 f (μ + d) k * aser f (μ - d) (m - k)
      - 2 * (aserD f (μ + d) k * aserD f (μ - d) (m - k))
      + aser f (μ + d) k * aserD2 f (μ - d) (m - k))

theorem psi_eq_cmf (f : ℕ → ℝ) (m : ℕ) (μ d : ℝ) :
    psi f m μ d = cmf f m (μ + d) (μ - d) := by
  have h := sum_range_aser f (μ + d) (μ - d) 1 m
  simpa [psi] using h

theorem hasDerivAt_psi (f : ℕ → ℝ) (m : ℕ) (μ d : ℝ) :
    HasDerivAt (psi f m μ) (psiD f m μ d) d := by
  rw [psiD]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have hleft := (hasDerivAt_aser f (μ + d) k).comp d ((hasDerivAt_id d).const_add μ)
  have hright := (hasDerivAt_aser f (μ - d) (m - k)).comp d ((hasDerivAt_id d).const_sub μ)
  have h := hleft.mul hright
  simp only [Function.comp_def] at h
  convert h using 1
  ring

theorem hasDerivAt_psiD (f : ℕ → ℝ) (m : ℕ) (μ d : ℝ) :
    HasDerivAt (psiD f m μ) (psiD2 f m μ d) d := by
  rw [psiD2]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have hleft := (hasDerivAt_aser f (μ + d) k).comp d ((hasDerivAt_id d).const_add μ)
  have hright := (hasDerivAt_aser f (μ - d) (m - k)).comp d ((hasDerivAt_id d).const_sub μ)
  have g1 := (hasDerivAt_aserD f (μ + d) k).comp d ((hasDerivAt_id d).const_add μ)
  have g2 := (hasDerivAt_aserD f (μ - d) (m - k)).comp d ((hasDerivAt_id d).const_sub μ)
  have h := (g1.mul hright).sub (hleft.mul g2)
  simp only [Function.comp_def] at h
  convert h using 1
  ring

/-! ### Continuity of the second derivative -/

theorem continuous_pochD (N : ℕ) : Continuous fun t : ℝ => pochD t N := by
  unfold pochD
  exact continuous_finsetSum _ fun i _ =>
    continuous_finsetProd _ fun j _ => continuous_id.add continuous_const

theorem continuous_pochD2 (N : ℕ) : Continuous fun t : ℝ => pochD2 t N := by
  unfold pochD2
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun i' _ =>
    continuous_finsetProd _ fun j _ => continuous_id.add continuous_const

theorem continuous_aserD (f : ℕ → ℝ) (n : ℕ) : Continuous fun t : ℝ => aserD f t n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [aserD] using continuous_const
  · have h : (fun t : ℝ => aserD f t n)
        = fun t : ℝ => f n * pochD t (3 * n) / (Nat.factorial (3 * n - 1) : ℝ) := by
      funext t; rw [aserD, if_neg hn]
    rw [h]
    exact ((continuous_pochD (3 * n)).const_mul (f n)).div_const _

theorem continuous_aserD2 (f : ℕ → ℝ) (n : ℕ) : Continuous fun t : ℝ => aserD2 f t n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [aserD2] using continuous_const
  · have h : (fun t : ℝ => aserD2 f t n)
        = fun t : ℝ => f n * pochD2 t (3 * n) / (Nat.factorial (3 * n - 1) : ℝ) := by
      funext t; rw [aserD2, if_neg hn]
    rw [h]
    exact ((continuous_pochD2 (3 * n)).const_mul (f n)).div_const _

theorem continuous_psiD2 (f : ℕ → ℝ) (m : ℕ) (μ : ℝ) : Continuous (psiD2 f m μ) := by
  unfold psiD2
  refine continuous_finsetSum _ fun k _ => ?_
  have ha : Continuous fun d : ℝ => aser f (μ + d) k :=
    (continuous_aser f k).comp (continuous_const.add continuous_id)
  have hb : Continuous fun d : ℝ => aser f (μ - d) (m - k) :=
    (continuous_aser f (m - k)).comp (continuous_const.sub continuous_id)
  have hDleft : Continuous fun d : ℝ => aserD f (μ + d) k :=
    (continuous_aserD f k).comp (continuous_const.add continuous_id)
  have hDright : Continuous fun d : ℝ => aserD f (μ - d) (m - k) :=
    (continuous_aserD f (m - k)).comp (continuous_const.sub continuous_id)
  have hD2left : Continuous fun d : ℝ => aserD2 f (μ + d) k :=
    (continuous_aserD2 f k).comp (continuous_const.add continuous_id)
  have hD2right : Continuous fun d : ℝ => aserD2 f (μ - d) (m - k) :=
    (continuous_aserD2 f (m - k)).comp (continuous_const.sub continuous_id)
  exact ((hD2left.mul hb).sub ((hDleft.mul hDright).const_mul 2)).add (ha.mul hD2right)

/-! ### `[x^m][(∂_μ F_f)² - F_f ∂_μ² F_f] = -Φ_m''(0)/2` -/

theorem dcoeff_eq_sum (f : ℕ → ℝ) (m : ℕ) (μ : ℝ) :
    dcoeff f m μ = ∑ k ∈ Finset.range (m + 1),
      (aserD f μ k * aserD f μ (m - k) - aser f μ k * aserD2 f μ (m - k)) := by
  rw [dcoeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [deriv_aser_eq, deriv_aser_eq, deriv2_aser_eq]

/-- The reflection `k ↔ m-k` of the antidiagonal, which makes the two outer
terms of `Φ_m''(0)` equal. -/
theorem sum_reflect_aserD2 (f : ℕ → ℝ) (m : ℕ) (μ : ℝ) :
    ∑ k ∈ Finset.range (m + 1), aserD2 f μ k * aser f μ (m - k)
      = ∑ k ∈ Finset.range (m + 1), aser f μ k * aserD2 f μ (m - k) := by
  have h := Finset.sum_range_reflect
    (fun k => aserD2 f μ k * aser f μ (m - k)) (m + 1)
  rw [← h]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hidx : m + 1 - 1 - k = m - k := by omega
  have hback : m - (m - k) = k := by omega
  rw [hidx, hback]
  ring

/-- **The paper's identity** `[x^m][(∂_μ F_f)² - F_f ∂_μ² F_f] = -Φ_m''(0)/2`,
exact and algebraic: `Φ_m''(0)` has the two outer terms of the second
derivative equal by the reflection `k ↔ m-k`. -/
theorem psiD2_at_zero (f : ℕ → ℝ) (m : ℕ) (μ : ℝ) :
    psiD2 f m μ 0 = -2 * dcoeff f m μ := by
  have hz : ∀ t : ℝ, t + 0 = t := fun t => by ring
  have hz' : ∀ t : ℝ, t - 0 = t := fun t => by ring
  rw [psiD2, dcoeff_eq_sum]
  simp only [hz, hz']
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_reflect_aserD2, Finset.sum_sub_distrib]
  ring

/-! ### The second-derivative test at an interior maximum -/

/-- If `Φ` is twice differentiable with continuous second derivative, `Φ'(0) = 0`
and `Φ(d) ≤ Φ(0)` on `|d| ≤ ε`, then `Φ''(0) ≤ 0`.  A positive `Φ''(0)` would
make `Φ'` strictly increasing near `0`, hence `Φ` strictly increasing to the
right of `0`.  Mathlib carries the first-derivative test
(`IsLocalMax.deriv_eq_zero`) but no second-derivative counterpart. -/
theorem deriv2_nonpos_of_max {Φ Φ1 Φ2 : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h1 : ∀ d, HasDerivAt Φ (Φ1 d) d) (h2 : ∀ d, HasDerivAt Φ1 (Φ2 d) d)
    (hc : Continuous Φ2) (hz : Φ1 0 = 0) (hmax : ∀ d, |d| ≤ ε → Φ d ≤ Φ 0) :
    Φ2 0 ≤ 0 := by
  by_contra hcon
  rw [not_le] at hcon
  have hopen : {x : ℝ | 0 < Φ2 x} ∈ nhds (0:ℝ) :=
    (isOpen_lt continuous_const hc).mem_nhds hcon
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.mem_nhds_iff.mp hopen
  set δ : ℝ := min (δ₀ / 2) ε with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) hε
  have hδlt : ∀ x ∈ Icc (0:ℝ) δ, 0 < Φ2 x := by
    intro x hx
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    calc x ≤ δ := hx.2
      _ ≤ δ₀ / 2 := min_le_left _ _
      _ < δ₀ := by linarith
  have hmono : StrictMonoOn Φ1 (Icc (0:ℝ) δ) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun x _ => (h2 x).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [(h2 x).deriv]
    exact hδlt x (interior_subset hx)
  have hΦ1pos : ∀ x ∈ Ioc (0:ℝ) δ, 0 < Φ1 x := by
    intro x hx
    have := hmono (a := 0) (b := x) ⟨le_refl 0, hδpos.le⟩ ⟨hx.1.le, hx.2⟩ hx.1
    rwa [hz] at this
  have hmono2 : StrictMonoOn Φ (Icc (0:ℝ) δ) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun x _ => (h1 x).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [(h1 x).deriv]
    have hx' := interior_subset hx
    rw [interior_Icc] at hx
    exact hΦ1pos x ⟨hx.1, hx'.2⟩
  have hlt : Φ 0 < Φ δ :=
    hmono2 ⟨le_refl 0, hδpos.le⟩ ⟨hδpos.le, le_refl δ⟩ hδpos
  have hle : Φ δ ≤ Φ 0 := hmax δ (by
    rw [abs_of_nonneg hδpos.le]
    exact min_le_right _ _)
  linarith

/-! ### `cor:differential`'s nonnegativity half -/

/-- `Φ_m'(0) = 0`: the first derivative of the antidiagonal vanishes at the
diagonal, by the reflection `k ↔ m-k`. -/
theorem psiD_at_zero (f : ℕ → ℝ) (m : ℕ) (μ : ℝ) : psiD f m μ 0 = 0 := by
  have hz : ∀ t : ℝ, t + 0 = t := fun t => by ring
  have hz' : ∀ t : ℝ, t - 0 = t := fun t => by ring
  rw [psiD]
  simp only [hz, hz']
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  have h := Finset.sum_range_reflect
    (fun k => aserD f μ k * aser f μ (m - k)) (m + 1)
  rw [← h]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hidx : m + 1 - 1 - k = m - k := by omega
  have hback : m - (m - k) = k := by omega
  rw [hidx, hback]
  ring

/-- **`cor:differential`'s nonnegativity half.**  `thm:main` makes `d = 0` a
maximum of `Φ_m` on `|d| ≤ μ`, and `psiD2_at_zero` identifies `-Φ_m''(0)/2` with
the degree-`m` coefficient, so that coefficient is nonnegative:

  `0 ≤ dcoeff f m μ`   for `μ ≥ 0`.

The hypothesis is the degree-local weight chain of `rem:local-weight` that
`Main.turan_coeff_nonneg` consumes, wider than `thm:main`'s sequence
hypothesis. -/
theorem dcoeff_nonneg (f : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m) (hfnn : ∀ r, 0 ≤ f r)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → f i * f (m - i) ≤ f j * f (m - j))
    {μ : ℝ} (hμ : 0 ≤ μ) : 0 ≤ dcoeff f m μ := by
  rcases eq_or_lt_of_le hμ with rfl | hμ0
  · rw [dcoeff_at_zero]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hfnn k) (hfnn (m - k))
  set w : ℕ → ℝ := fun k => f k * f (m - k) with hw
  have hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r) := by
    intro r hr1 hr2
    have h : m - (m - r) = r := by omega
    simp only [hw, h]
    ring
  have hmax : ∀ d : ℝ, |d| ≤ μ → psi f m μ d ≤ psi f m μ 0 := by
    intro d hd
    have habs := abs_le.mp hd
    have hkey := turan_coeff_nonneg f m hm hfnn hwmono (μ - |d|) |d| |d|
      (by linarith [abs_nonneg d]) (abs_nonneg d) (abs_nonneg d)
    have hrecover : μ - |d| + |d| = μ := by ring
    rw [hrecover] at hkey
    rw [psi_eq_cmf, psi_eq_cmf, add_zero, sub_zero]
    rcases le_or_gt 0 d with hd0 | hd0
    · have hdd : |d| = d := abs_of_nonneg hd0
      rw [hdd] at hkey
      have hswap : cmf f m (μ - d) (μ + d) = cmf f m (μ + d) (μ - d) :=
        cmw_symm w hm hsym (μ - d) (μ + d)
      rw [hswap] at hkey
      linarith
    · have hdd : |d| = -d := abs_of_neg hd0
      rw [hdd] at hkey
      have hadd : μ - -d = μ + d := by ring
      have hsub : μ + -d = μ - d := by ring
      rw [hadd, hsub] at hkey
      linarith
  have hnp : psiD2 f m μ 0 ≤ 0 :=
    deriv2_nonpos_of_max hμ0 (hasDerivAt_psi f m μ) (hasDerivAt_psiD f m μ)
      (continuous_psiD2 f m μ) (psiD_at_zero f m μ) hmax
  rw [psiD2_at_zero] at hnp
  linarith

/-- `dcoeff_nonneg` at `thm:main`'s own sequence hypothesis, through
`lem:central-products`. -/
theorem dcoeff_nonneg_of_logConcave (f : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m) (hfnn : ∀ r, 0 ≤ f r)
    (hlc : LogConcaveSeq f) (hint : IntervalSupport f) {μ : ℝ} (hμ : 0 ≤ μ) :
    0 ≤ dcoeff f m μ :=
  dcoeff_nonneg f m hm hfnn
    (fun i j hi hij hjm =>
      centralProducts_chain (centralProducts_of_logConcave hfnn hlc hint) m i j hi hij hjm)
    hμ

/-! ### Strict log-concavity of the Pochhammer polynomial

`(μ)_N` is a product of `N` linear factors, so its Wronskian-type combination
`((μ)_N')² - (μ)_N (μ)_N''` collapses to a sum of squares.  This is an exact
polynomial identity — no positivity is used in deriving it — and it is what makes
`cor:differential` strict at `m = 2`. -/

/-- `((μ)_N')² - (μ)_N (μ)_N'' = Σ_{i<N} (∏_{j≠i}(μ+j))²`.  Each off-diagonal
term of the square cancels against the corresponding term of `(μ)_N (μ)_N''`,
because `(μ)_N · ∏_{j≠i,i'}(μ+j) = ∏_{j≠i}(μ+j) · ∏_{j≠i'}(μ+j)`. -/
theorem pochD_sq_sub_mul_pochD2 (μ : ℝ) (N : ℕ) :
    pochD μ N ^ 2 - poch μ N * pochD2 μ N
      = ∑ i ∈ Finset.range N, (∏ j ∈ (Finset.range N).erase i, (μ + (j : ℝ))) ^ 2 := by
  set P : ℕ → ℝ := fun i => ∏ j ∈ (Finset.range N).erase i, (μ + (j : ℝ)) with hP
  have hmul : ∀ i ∈ Finset.range N, ∀ i' ∈ (Finset.range N).erase i,
      poch μ N * (∏ j ∈ ((Finset.range N).erase i).erase i', (μ + (j : ℝ))) = P i * P i' := by
    intro i hi i' hi'
    have hi'mem : i' ∈ Finset.range N := Finset.mem_of_mem_erase hi'
    have hne : i' ≠ i := Finset.ne_of_mem_erase hi'
    have himem2 : i ∈ (Finset.range N).erase i' := Finset.mem_erase.mpr ⟨Ne.symm hne, hi⟩
    have e1 : (∏ j ∈ ((Finset.range N).erase i).erase i', (μ + (j : ℝ))) * (μ + (i' : ℝ))
        = P i := Finset.prod_erase_mul _ _ hi'
    have e2 : (∏ j ∈ ((Finset.range N).erase i').erase i, (μ + (j : ℝ))) * (μ + (i : ℝ))
        = P i' := Finset.prod_erase_mul _ _ himem2
    have ecomm : ((Finset.range N).erase i').erase i = ((Finset.range N).erase i).erase i' :=
      Finset.erase_right_comm
    rw [ecomm] at e2
    have e3 : P i * (μ + (i : ℝ)) = poch μ N := Finset.prod_erase_mul _ _ hi
    calc poch μ N * (∏ j ∈ ((Finset.range N).erase i).erase i', (μ + (j : ℝ)))
        = (P i * (μ + (i : ℝ))) * (∏ j ∈ ((Finset.range N).erase i).erase i', (μ + (j : ℝ))) := by
          rw [e3]
      _ = P i * ((∏ j ∈ ((Finset.range N).erase i).erase i', (μ + (j : ℝ))) * (μ + (i : ℝ))) := by
          ring
      _ = P i * P i' := by rw [e2]
  have hsq : pochD μ N ^ 2 = ∑ i ∈ Finset.range N, ∑ i' ∈ Finset.range N, P i * P i' := by
    rw [pochD, sq, Finset.sum_mul_sum]
  have hsplit : ∀ i ∈ Finset.range N, (∑ i' ∈ Finset.range N, P i * P i')
      = P i ^ 2 + ∑ i' ∈ (Finset.range N).erase i, P i * P i' := by
    intro i hi
    rw [← Finset.sum_erase_add _ _ hi, sq]
    ring
  have hprod : poch μ N * pochD2 μ N
      = ∑ i ∈ Finset.range N, ∑ i' ∈ (Finset.range N).erase i, P i * P i' := by
    rw [pochD2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' hi' => hmul i hi i' hi'
  rw [hsq, Finset.sum_congr rfl hsplit, hprod, Finset.sum_add_distrib]
  ring

/-- **`(μ)_N` is strictly log-concave for `μ ≥ 0` and `N ≥ 1`**: the `i = 0`
square of `pochD_sq_sub_mul_pochD2` is `((N-1)!)²` at `μ = 0` and positive
throughout. -/
theorem poch_mul_pochD2_lt {μ : ℝ} (hμ : 0 ≤ μ) {N : ℕ} (hN : 1 ≤ N) :
    poch μ N * pochD2 μ N < pochD μ N ^ 2 := by
  have hid := pochD_sq_sub_mul_pochD2 μ N
  have hpos : 0 < ∑ i ∈ Finset.range N, (∏ j ∈ (Finset.range N).erase i, (μ + (j : ℝ))) ^ 2 := by
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨0, Finset.mem_range.mpr hN, ?_⟩
    refine pow_pos ?_ 2
    refine Finset.prod_pos fun j hj => ?_
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    have : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
    linarith
  linarith

/-! ### `cor:differential` at `m = 2`

At `m = 2` the antidiagonal has one term, `k = 1`, so the coefficient is the
Wronskian of a single Pochhammer factor and `poch_mul_pochD2_lt` closes
`cor:differential` there: `2 ∈ I+I` exactly when `f_1 > 0`, and the coefficient
is then positive at every `μ ≥ 0`. -/

theorem dcoeff_two_eq (f : ℕ → ℝ) (μ : ℝ) :
    dcoeff f 2 μ = (f 1 / (Nat.factorial 2 : ℝ)) ^ 2
      * (pochD μ 3 ^ 2 - poch μ 3 * pochD2 μ 3) := by
  rw [dcoeff_eq_sum]
  rw [show (2 : ℕ) + 1 = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  norm_num [aserD, aserD2, aser_of_ne_zero]
  ring

/-- **`cor:differential` at `m = 2`**, both directions: the degree-two
coefficient of the differential Turánian is positive exactly when `f_1 > 0`,
which is `2 ∈ I+I`. -/
theorem dcoeff_two_pos_iff {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {μ : ℝ} (hμ : 0 ≤ μ) :
    0 < dcoeff f 2 μ ↔ 0 < f 1 := by
  have hw := poch_mul_pochD2_lt hμ (N := 3) (by norm_num)
  rw [dcoeff_two_eq]
  constructor
  · intro h
    rcases eq_or_lt_of_le (hf 1) with h0 | h0
    · rw [← h0] at h; simp at h
    · exact h0
  · intro h
    have hsq_pos : (0:ℝ) < (f 1 / (Nat.factorial 2 : ℝ)) ^ 2 := by positivity
    exact mul_pos hsq_pos (by linarith)

/-! ### The remaining gap in `cor:differential`

For `m ≥ 3` and `μ > 0`, strict positivity of `dcoeff f m μ` on `m ∈ I+I` is
open here.  `dcoeff_nonneg` is as far as `thm:main` reaches: Schur-concavity
makes `d = 0` a maximum of `Φ_m`, hence `Φ_m''(0) ≤ 0`, and a quartically flat
maximum satisfies that too — `Multiplicity.ghat_three_center_expansion` exhibits
such flatness elsewhere in the paper — so strictness needs its own argument.

The precise missing sub-statement, in the finite algebraic form the rest of this
module lives in.  Write `u_k = w_k (μ)_{3k}(μ)_{3(m-k)}/((3k-1)!(3(m-k)-1)!)`
for the terms of `C_{m,w}(μ,μ)`, and

  `T_k = H(3k) - H(3(m-k))`,   `H(N) = Σ_{j<N} 1/(μ+j)`,
  `V_k = S(3k) + S(3(m-k))`,   `S(N) = Σ_{j<N} 1/(μ+j)²`.

Then `-Φ_m''(0) = Σ_k u_k (V_k - T_k²)`, and the missing statement is

  `Σ_k u_k T_k² < Σ_k u_k V_k`

for weights satisfying `eq:w-monotone` and not all zero.  Three facts about it,
each measured in `scripts/check_differential_coefficients.py`:

* It is **not** termwise, and not pairwise either.  `T` is odd and `u` even under
  `k ↔ m-k`, so the sum is `Σ_k u_k V_k - Var(T)` against the normalized weights;
  the pairwise bound `V_k + V_l ≥ (T_k - T_l)²` fails already at `k = 1`,
  `l = m-1`, `m = 40`, `μ = 1` (`49.3` against `6.01`).  What makes the sum
  positive is the correlation, not any single term.
* It is **asymptotically tight**.  At constant weights the slack is `2/μ²`, and
  once `μ` dominates `m` both sides are `3m/μ²`, so the relative margin is
  `2/(3m)` and vanishes with `m`.  A proof has to reproduce an exact
  cancellation, not just an estimate.
* The `1/μ²` term of `V` is exactly the slack in the limit, and it cannot simply
  be split off: with the `j = 0` term dropped from both sides the inequality
  **reverses** at `m = 40`, `μ = 5` (by `3·10⁻⁸`).

A fourth measured fact says what a coefficientwise proof would face: as a
polynomial in `μ`, the degree-`m` coefficient has strictly positive coefficients
at every extreme ray of the `eq:w-monotone` cone, but the smallest of them is
`1801/2497779395061350400000` at `m = 9`, so those positivities are themselves
the result of cancellation.

`lem:weighting` cuts the weight family down to two members, and that reduction
is measured too.  The coefficient is linear in `w`, so nonnegativity against
every `eq:w-monotone` weight holds exactly when every Abel tail sum
`B_j = Σ_{k=j}^{m-j} β_k` of the unit-weight summands does — `B_j` being the
value at the `j`-th extreme ray.  Here `B_{j+1} - B_j = -2 β_j / w` in the
notation below, whose sign is `-sign τ(3j)` for the increasing `τ` defined next,
so the differences run `+ … + - … -`: `B` is unimodal in `j` and its minimum sits
at `j = 1` or `j = ⌊m/2⌋`.  Which of the two depends on `μ`, so both are needed.
`B_{⌊m/2⌋}` is the central window, where the gap block is empty (`m` even) or has
three elements (`m` odd), and `S(n) > 3 r_n²` settles it for `m ≥ 4`.  **`B_1` is
the constant weight — that is, the sequence `f = 1` — so what is left is
`0 < dcoeff 1 m μ`, and `subsec:hypergeometric-specialization` is where the paper
looks at exactly that sequence.**

The summand has a **much simpler equivalent form**, which is the shape to attack.
Write `r_i = 1/(μ+i)` and `e₂(B) = Σ_{i<j ∈ B} r_i r_j`.  Then

  `(V_k - T_k²)/2 = τ(3 min(k, m-k))`,   `τ(n) = S(n) - e₂([n, 3m-n))`,

because both `e₁` products collapse: over the shorter index block `S` and the
longer `T ⊇ S`, `e₁(S)e₁(T) - e₂(S) - e₂(T) = Σ_{i ∈ S} r_i² - e₂(T \ S)`.  So
the summand depends on `k` only through the length of the shorter block, and `τ`
is strictly increasing in `n` with a **single sign change** — negative at the
ends of the antidiagonal, positive at its center.  The missing statement is then
exactly that a single-crossing function has positive mean against the weights
`u`, which is the shape `lem:weighting` and `lem:beta-order` already take in this
paper.

The paper takes the other route, differentiating the beta representation
`eq:fixed-sum` twice under the integral to reach
`Φ_m''(0) = κ_{m,2μ} Cov(Ĝ_{m,w}(Q₀), ℓ(Q₀)²) < 0` from `thm:kernel`'s strict
monotonicity against a strictly decreasing `ℓ²`.  That needs differentiation
under the integral sign with the paper's two domination bounds and a strict
two-copy covariance inequality; `BetaOrder` carries the folded kernel, the
`cosh` form, `logit` and the integrability lemmas the first half of it would
consume. -/

end CubicPochhammer
