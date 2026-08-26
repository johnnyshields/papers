/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Main
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact

/-!
# Analytic consequences of the cubic theorem

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:consequences`
«Consequences».

## `subsec:strict-pointwise-log-concavity` (`cor:ordinary`) — proved

For `0 < x` inside the disc of convergence of `Σ_{n≥1} f_n x^n`, `cor_ordinary`
gives all five clauses: `μ ↦ F_f(μ;x)` is finite for `μ ≥ 0`, positive and
continuous on `(0,∞)`, `μ ↦ log F_f(μ;x)` is strictly concave there, and

  `F_f(μ+α;x) F_f(μ+β;x) > F_f(μ;x) F_f(μ+α+β;x)`   (`μ ≥ 0`, `α, β > 0`).

Two steps of the paper's proof are replaced by shorter ones.  The Gamma-ratio
asymptotic `(μ)_{3n}/(3n-1)! ∼ (3n)^μ/Γ(μ)` is not needed: only an upper bound
of polynomial growth is used, and `poch_le_factorial_mul_pow` supplies
`(μ)_N ≤ N!(N+1)^K` for `0 ≤ μ ≤ K` from Bernoulli's inequality.  Strictness does
not go through `cor:strict`: at `m = 2a` with `a` the least index of the support
the convolution has a single term, and `poch_mul_lt` compares it factor by
factor, the two products differing by exactly `αβ` in each factor.

`strictConcaveOn_of_midpoint` — strict midpoint concavity plus continuity gives
`StrictConcaveOn` — is general and is not in Mathlib.  Its mechanism is that a
chord cannot be met from below at an interior point (`not_isMinOn_sub_chord`),
since an affine function reproduces its own midpoints while `g` strictly
exceeds them; no dyadic approximation is involved.

## `subsec:differential-turan-inequality` (`cor:differential`) — partial

`dcoeff f m μ` is the degree-`m` coefficient of `(∂_μ F_f)² - F_f ∂_μ² F_f`
written out as the antidiagonal sum `Σ_{k+l=m}(a_k' a_l' - a_k a_l'')` of
coefficient derivatives.  Proved here:

* `dcoeff_eq_zero_of_weights`: it vanishes identically in `μ` when `m ∉ I+I`.
* `dcoeff_at_zero`: at `μ = 0` it equals `Σ_{k+l=m} f_k f_l`, the paper's
  `(Σ f_n x^n)²`, and `dcoeff_at_zero_pos_iff` is `> 0 ⟺ m ∈ I+I` there.

`Differential` carries the rest: that `dcoeff f m μ` really is the `x^m`
coefficient of the analytic differential Turánian (`dcoeff_tsum_eq`), its
nonnegativity for every `μ ≥ 0` (`dcoeff_nonneg`), and `cor:differential` in
both directions at `m = 2` (`dcoeff_two_pos_iff`).  Strict positivity for
`μ > 0` and `m ∈ I+I` at `m ≥ 3` is open, and the precise missing sub-statement
is stated there.

Sorry-free and axiom-free.

## Main definitions

* `aser`, `fser` --- the degree-`n` coefficient of `eq:F-def` and the series
  itself, the coefficient set to zero at `n = 0` so the sum runs over all of `ℕ`.
* `dcoeff` --- the degree-`m` coefficient of `(∂_μ F_f)² - F_f ∂_μ² F_f`,
  written as an antidiagonal sum of coefficient derivatives.
* `chord` --- the affine interpolant of `g` through `(p, g p)` and `(q, g q)`.

## Main statements

* `poch_le_factorial_mul_pow` --- `(μ)_N ≤ N!(N+1)^K` for `0 ≤ μ ≤ K`, the
  polynomial majorant that replaces the paper's Gamma-ratio asymptotic.
* `fser_mul`, `summable_cmf` --- the Cauchy product of two copies of `eq:F-def`.
* `not_isMinOn_sub_chord`, `chord_lt_of_midpoint` --- strict midpoint concavity
  forbids an interior minimum of `g - chord`, hence puts the chord strictly
  below `g` between its endpoints.
* `log_midpoint_lt_of_mul_lt_sq` --- the bridge from a strict Turán inequality
  `AB < C²` to strict midpoint concavity of `log`; the only place logarithms
  enter `cor:ordinary`.
* `strictConcaveOn_of_midpoint` --- strict midpoint concavity plus continuity
  gives `StrictConcaveOn`; general, and not in Mathlib.
* `cor_ordinary` --- `cor:ordinary` in full, all five clauses.
* `dcoeff_at_zero`, `dcoeff_at_zero_pos_iff` --- the `μ = 0` boundary of
  `cor:differential`, where the antidiagonal sum collapses.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:consequences` «Consequences»:
  `subsec:strict-pointwise-log-concavity` (`cor:ordinary`),
  `subsec:differential-turan-inequality` (`cor:differential`), `eq:F-def`.
-/

open scoped BigOperators
open Set

namespace CubicPochhammer

/-! ### A polynomial majorant for the Gamma ratio -/

/-- `A^K(A+K) ≤ A(A+1)^K`, Bernoulli's inequality in the form the majorant
induction consumes. -/
theorem pow_mul_add_le_mul_add_pow {A : ℝ} (hA : 0 ≤ A) (K : ℕ) :
    A ^ K * (A + K) ≤ A * (A + 1) ^ K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have h := pow_add_mul_le_add_pow (a := A) (b := (1:ℝ)) hA (by linarith) K
  have hpow : A ^ (K - 1) * A = A ^ K := by
    rw [← pow_succ]
    congr 1
    omega
  calc A ^ K * (A + K) = A * (A ^ K + (K:ℝ) * A ^ (K - 1) * 1) := by
        linear_combination (-(K:ℝ)) * hpow
    _ ≤ A * (A + 1) ^ K := mul_le_mul_of_nonneg_left h hA

/-- `(μ)_N ≤ N! (N+1)^K` for `0 ≤ μ ≤ K`: the elementary majorant replacing the
Stirling estimate `(μ)_{3n}/(3n-1)! ∼ (3n)^μ/Γ(μ)`.  Only an upper bound is
needed, and `pow_mul_add_le_mul_add_pow` supplies the induction step. -/
theorem poch_le_factorial_mul_pow (K : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) (hK : μ ≤ (K : ℝ)) (N : ℕ) :
    poch μ N ≤ (Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ K := by
  induction N with
  | zero => simp [poch]
  | succ N ih =>
    have hstep : poch μ (N + 1) = poch μ N * (μ + (N:ℝ)) := by
      rw [poch, poch, Finset.prod_range_succ]
    have hfac : (Nat.factorial (N + 1) : ℝ) = ((N:ℝ) + 1) * (Nat.factorial N : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hpos : (0:ℝ) ≤ (Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ K := by positivity
    have hstep : poch μ (N + 1) ≤ (Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ K * ((K:ℝ) + (N:ℝ)) := by
      rw [hstep]
      exact mul_le_mul ih (by linarith) (by linarith [poch_nonneg hμ N]) hpos
    have hbern := pow_mul_add_le_mul_add_pow (A := (N:ℝ) + 1) (by positivity) K
    have hfold : ((N : ℝ) + 1) ^ K * ((K:ℝ) + (N:ℝ))
        ≤ ((N : ℝ) + 1) * (((N : ℝ) + 1) + 1) ^ K := by
      refine le_trans ?_ hbern
      have : ((N:ℝ) + 1) ^ K * ((K:ℝ) + N) ≤ ((N:ℝ) + 1) ^ K * (((N:ℝ) + 1) + K) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    calc poch μ (N + 1) ≤ (Nat.factorial N : ℝ) * (((N : ℝ) + 1) ^ K * ((K:ℝ) + (N:ℝ))) := by
          rw [← mul_assoc]; exact hstep
      _ ≤ (Nat.factorial N : ℝ) * (((N : ℝ) + 1) * (((N : ℝ) + 1) + 1) ^ K) :=
          mul_le_mul_of_nonneg_left hfold (by positivity)
      _ = (Nat.factorial (N + 1) : ℝ) * (((N + 1 : ℕ) : ℝ) + 1) ^ K := by
          rw [hfac]; push_cast; ring

/-- `(μ)_k` is nondecreasing in `μ` on `[0,∞)`. -/
theorem poch_mono {μ ν : ℝ} (hμ : 0 ≤ μ) (hμν : μ ≤ ν) (k : ℕ) : poch μ k ≤ poch ν k :=
  Finset.prod_le_prod (fun i _ => by linarith [Nat.cast_nonneg (α := ℝ) i])
    (fun i _ => by linarith)


/-! ### The series `F_f(μ;x)` and its convergence -/

/-- The degree-`n` coefficient `f_n (μ)_{3n}/(3n-1)!` of `F_f(μ;x)`
(`eq:F-def`), set to zero at `n = 0` so that the series runs over all of `ℕ`. -/
noncomputable def aser (f : ℕ → ℝ) (μ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else f n * poch μ (3 * n) / (Nat.factorial (3 * n - 1) : ℝ)

/-- `F_f(μ;x) = Σ_{n≥1} f_n (μ)_{3n} x^n/(3n-1)!` (`eq:F-def`). -/
noncomputable def fser (f : ℕ → ℝ) (μ x : ℝ) : ℝ := ∑' n, aser f μ n * x ^ n

@[simp] theorem aser_zero (f : ℕ → ℝ) (μ : ℝ) : aser f μ 0 = 0 := by simp [aser]

theorem aser_of_ne_zero (f : ℕ → ℝ) (μ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    aser f μ n = f n * poch μ (3 * n) / (Nat.factorial (3 * n - 1) : ℝ) := by
  simp [aser, hn]

theorem aser_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) :
    0 ≤ aser f μ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [aser_of_ne_zero f μ hn]
    exact div_nonneg (mul_nonneg (hf n) (poch_nonneg hμ _)) (by positivity)

theorem aser_mono {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {μ ν : ℝ} (hμ : 0 ≤ μ) (hμν : μ ≤ ν)
    (n : ℕ) : aser f μ n ≤ aser f ν n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [aser_of_ne_zero f μ hn, aser_of_ne_zero f ν hn, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (poch_mono hμ hμν _) (hf n)) (by positivity)

/-- `(3n)! = 3n·(3n-1)!` for `n ≥ 1`, the cancellation the majorant needs. -/
theorem factorial_three_mul (n : ℕ) (hn : 1 ≤ n) :
    (Nat.factorial (3 * n) : ℝ) = (3 * (n:ℝ)) * (Nat.factorial (3 * n - 1) : ℝ) := by
  obtain ⟨j, hj⟩ : ∃ j, 3 * n = j + 1 := ⟨3 * n - 1, by omega⟩
  have hidx : 3 * n - 1 = j := by omega
  have hcast : ((j:ℝ) + 1) = 3 * (n:ℝ) := by
    have hcast : ((j + 1 : ℕ) : ℝ) = ((3 * n : ℕ) : ℝ) := by rw [hj]
    push_cast at hcast
    linarith
  rw [hidx, hj, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hcast]

/-- The elementary majorant on the coefficients: for `0 ≤ μ ≤ K`,
`aser f μ n ≤ f_n · 3n(3n+1)^K`.  This replaces `cor:ordinary`'s Stirling
estimate; only an upper bound of polynomial growth in `n` is needed. -/
theorem aser_le_bound {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (K : ℕ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hK : μ ≤ (K : ℝ)) (n : ℕ) :
    aser f μ n ≤ f n * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hfacpos : (0:ℝ) < (Nat.factorial (3 * n - 1) : ℝ) := by positivity
  rw [aser_of_ne_zero f μ hn, div_le_iff₀ hfacpos]
  have hpoch := poch_le_factorial_mul_pow K hμ hK (3 * n)
  have hcast : ((3 * n : ℕ) : ℝ) + 1 = 3 * (n:ℝ) + 1 := by push_cast; ring
  rw [hcast, factorial_three_mul n hn1] at hpoch
  calc f n * poch μ (3 * n) ≤ f n * (3 * (n:ℝ) * (Nat.factorial (3 * n - 1) : ℝ)
        * (3 * (n:ℝ) + 1) ^ K) := mul_le_mul_of_nonneg_left hpoch (hf n)
    _ = f n * (3 * (n:ℝ) * (3 * (n:ℝ) + 1) ^ K) * (Nat.factorial (3 * n - 1) : ℝ) := by ring

/-- The polynomial-times-geometric majorant series converges for `0 < t < 1`. -/
theorem summable_poly_geom (K : ℕ) {t : ℝ} (ht0 : 0 < t) (ht : t < 1) :
    Summable (fun n : ℕ => (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K * t ^ n) := by
  have hnorm : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos ht0]; exact ht
  have hg : Summable (fun n : ℕ => (n:ℝ) ^ (K + 1) * t ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (K + 1) hnorm
  have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (K + 1) * t ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hg
  have hstep : Summable (fun n : ℕ => (3:ℝ) ^ (K + 1) * (((n:ℝ) + 1) ^ (K + 1) * t ^ n)) := by
    refine (hshift.mul_left ((3:ℝ) ^ (K + 1) / t)).congr fun n => ?_
    have htne : t ≠ 0 := ne_of_gt ht0
    push_cast
    field
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hstep
  have hgrow : (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K ≤ (3:ℝ) ^ (K + 1) * ((n:ℝ) + 1) ^ (K + 1) := by
    have hb : (3 * (n:ℝ) + 1) ^ K ≤ (3 * ((n:ℝ) + 1)) ^ K := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hsplit : (3 * ((n:ℝ) + 1)) ^ K = (3:ℝ) ^ K * ((n:ℝ) + 1) ^ K := by
      rw [mul_pow]
    calc (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K
        ≤ (3 * ((n:ℝ) + 1)) * ((3:ℝ) ^ K * ((n:ℝ) + 1) ^ K) := by
          apply mul_le_mul (by linarith) (by rw [← hsplit]; exact hb)
            (by positivity) (by positivity)
      _ = (3:ℝ) ^ (K + 1) * ((n:ℝ) + 1) ^ (K + 1) := by ring
  have ht' : (0:ℝ) ≤ t ^ n := by positivity
  calc (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K * t ^ n
      ≤ ((3:ℝ) ^ (K + 1) * ((n:ℝ) + 1) ^ (K + 1)) * t ^ n := by
        exact mul_le_mul_of_nonneg_right hgrow ht'
    _ = (3:ℝ) ^ (K + 1) * (((n:ℝ) + 1) ^ (K + 1) * t ^ n) := by ring

/-- **`F_f(μ;x)` converges** for `0 ≤ μ` and `0 < x` strictly inside the disc of
convergence of `Σ f_n x^n`, which is what `cor:ordinary`'s Weierstrass step
gives.  The hypothesis is the paper's `x < y < R` together with convergence at
`y`. -/
theorem summable_aser {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {μ x y : ℝ} (hμ : 0 ≤ μ)
    (hx : 0 < x) (hxy : x < y) (hy : Summable fun n => f n * y ^ n) :
    Summable (fun n => aser f μ n * x ^ n) := by
  set K : ℕ := ⌈μ⌉₊ with hKdef
  have hK : μ ≤ (K:ℝ) := Nat.le_ceil μ
  have hy0 : 0 < y := lt_trans hx hxy
  set t : ℝ := x / y with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [htdef, div_lt_one hy0]; exact hxy
  have hsum := summable_poly_geom K ht0 ht1
  set C : ℝ := ∑' n : ℕ, (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K * t ^ n with hCdef
  have hCle : ∀ n : ℕ, (3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K * t ^ n ≤ C :=
    fun n => hsum.le_tsum n (fun m _ => by positivity)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hy.mul_right C)
  · exact mul_nonneg (aser_nonneg hf hμ n) (by positivity)
  · have hxt : x ^ n = y ^ n * t ^ n := by
      rw [htdef, div_pow, mul_div_cancel₀]
      positivity
    have hstep := aser_le_bound hf K hμ hK n
    have hyn : (0:ℝ) ≤ y ^ n := by positivity
    calc aser f μ n * x ^ n
        ≤ (f n * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K)) * (y ^ n * t ^ n) := by
          rw [hxt]
          exact mul_le_mul_of_nonneg_right hstep
            (mul_nonneg (pow_nonneg hy0.le n) (pow_nonneg ht0.le n))
      _ = (f n * y ^ n) * ((3 * (n:ℝ)) * (3 * (n:ℝ) + 1) ^ K * t ^ n) := by ring
      _ ≤ (f n * y ^ n) * C := by
          exact mul_le_mul_of_nonneg_left (hCle n)
            (mul_nonneg (hf n) (pow_nonneg hy0.le n))

theorem summable_norm_aser {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {μ x y : ℝ} (hμ : 0 ≤ μ)
    (hx : 0 < x) (hxy : x < y) (hy : Summable fun n => f n * y ^ n) :
    Summable (fun n => ‖aser f μ n * x ^ n‖) := by
  refine (summable_aser hf hμ hx hxy hy).congr fun n => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (aser_nonneg hf hμ n) (pow_nonneg hx.le n))]

/-- Each coefficient is a polynomial in `μ`, hence continuous. -/
theorem continuous_aser (f : ℕ → ℝ) (n : ℕ) : Continuous fun μ : ℝ => aser f μ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using continuous_const
  · have h : (fun μ : ℝ => aser f μ n)
        = fun μ : ℝ => f n * poch μ (3 * n) / (Nat.factorial (3 * n - 1) : ℝ) :=
      funext fun μ => aser_of_ne_zero f μ hn
    rw [h]
    unfold poch
    fun_prop

/-! ### The product of two series and its coefficients -/

/-- **The degree-`m` Cauchy coefficient is `C_{m,f}(u,v)`** (`eq:C-def` at the
weights `eq:w-from-f`): the two boundary terms of the convolution vanish because
the series has no constant term, and `x^k x^{m-k} = x^m`. -/
theorem sum_range_aser (f : ℕ → ℝ) (u v x : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), aser f u k * x ^ k * (aser f v (m - k) * x ^ (m - k))
      = cmf f m u v * x ^ m := by
  have hsub : Finset.Icc 1 (m - 1) ⊆ Finset.range (m + 1) := by
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    simp only [Finset.mem_range]
    omega
  have hvanish : ∀ k ∈ Finset.range (m + 1), k ∉ Finset.Icc 1 (m - 1) →
      aser f u k * x ^ k * (aser f v (m - k) * x ^ (m - k)) = 0 := by
    intro k hk hk'
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc, not_and, not_le] at hk'
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · have hmk : m - k = 0 := by
        have := hk' hkpos
        omega
      rw [hmk]
      simp
  rw [← Finset.sum_subset hsub hvanish, cmf, cmw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hr
  have hr0 : r ≠ 0 := by omega
  have hmr0 : m - r ≠ 0 := by omega
  have hxx : x ^ r * x ^ (m - r) = x ^ m := by
    rw [← pow_add]
    congr 1
    omega
  have hd1 : ((Nat.factorial (3 * r - 1) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd2 : ((Nat.factorial (3 * (m - r) - 1) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [aser_of_ne_zero f u hr0, aser_of_ne_zero f v hmr0, ← hxx]
  field_simp

/-- **`F_f(u;x) F_f(v;x) = Σ_m C_{m,f}(u,v) x^m`**: the Cauchy product, legal
because both series converge absolutely inside the disc. -/
theorem fser_mul {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {u v x y : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : 0 < x) (hxy : x < y) (hy : Summable fun n => f n * y ^ n) :
    fser f u x * fser f v x = ∑' m, cmf f m u v * x ^ m := by
  have hnu := summable_norm_aser hf hu hx hxy hy
  have hnv := summable_norm_aser hf hv hx hxy hy
  rw [fser, fser, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hnu hnv]
  exact tsum_congr fun m => sum_range_aser f u v x m

theorem summable_cmf {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {u v x y : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : 0 < x) (hxy : x < y) (hy : Summable fun n => f n * y ^ n) :
    Summable fun m => cmf f m u v * x ^ m := by
  have hnu := summable_norm_aser hf hu hx hxy hy
  have hnv := summable_norm_aser hf hv hx hxy hy
  refine (summable_sum_mul_range_of_summable_norm' hnu hnu.of_norm hnv hnv.of_norm).congr
    fun m => ?_
  exact sum_range_aser f u v x m

/-! ### Finiteness, positivity and continuity in the parameter -/

/-- **`F_f(μ;x) > 0`** for `μ > 0` and `x > 0`: every coefficient is nonnegative
and the one at an index of the support is positive. -/
theorem fser_pos {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {n₀ : ℕ} (hn₀ : n₀ ≠ 0) (hfn₀ : 0 < f n₀)
    {μ x y : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hxy : x < y)
    (hy : Summable fun n => f n * y ^ n) : 0 < fser f μ x := by
  refine (summable_aser hf hμ.le hx hxy hy).tsum_pos
    (fun n => mul_nonneg (aser_nonneg hf hμ.le n) (pow_nonneg hx.le n)) n₀ ?_
  rw [aser_of_ne_zero f μ hn₀]
  have hp : 0 < poch μ (3 * n₀) := poch_pos hμ _
  have hfac : (0:ℝ) < (Nat.factorial (3 * n₀ - 1) : ℝ) := by positivity
  have hxn : (0:ℝ) < x ^ n₀ := by positivity
  positivity

/-- **Local uniform convergence in `μ`** (`cor:ordinary`'s Weierstrass step): on
`[0,M]` the series at `μ = M` dominates, so `μ ↦ F_f(μ;x)` is continuous
there. -/
theorem fser_continuousOn_Icc {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {x y M : ℝ} (hM : 0 ≤ M)
    (hx : 0 < x) (hxy : x < y) (hy : Summable fun n => f n * y ^ n) :
    ContinuousOn (fun μ => fser f μ x) (Icc 0 M) := by
  refine continuousOn_tsum (u := fun n => aser f M n * x ^ n)
    (fun n => ((continuous_aser f n).mul continuous_const).continuousOn)
    (summable_aser hf hM hx hxy hy) ?_
  intro n μ hμ
  rw [Real.norm_of_nonneg (mul_nonneg (aser_nonneg hf hμ.1 n) (pow_nonneg hx.le n))]
  exact mul_le_mul_of_nonneg_right (aser_mono hf hμ.1 hμ.2 n) (pow_nonneg hx.le n)

/-- **`μ ↦ F_f(μ;x)` is continuous on `(0,∞)`** (`cor:ordinary`). -/
theorem fser_continuousOn_Ioi {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy : Summable fun n => f n * y ^ n) :
    ContinuousOn (fun μ => fser f μ x) (Ioi 0) := by
  intro μ hμ
  have hμ0 : 0 < μ := hμ
  have hmem : Icc 0 (μ + 1) ∈ nhds μ := Icc_mem_nhds hμ0 (by linarith)
  exact ((fser_continuousOn_Icc hf (by linarith : (0:ℝ) ≤ μ + 1) hx hxy hy).continuousAt
    hmem).continuousWithinAt

/-! ### Strict positivity of one coefficient -/

/-- A strict product comparison with nonnegative — not necessarily positive —
left factors: the parameter `μ = 0` of `cor:ordinary` makes the first factor of
`(μ)_N` vanish, so `Finset.prod_lt_prod_of_nonempty` does not apply. -/
theorem prod_lt_prod_of_lt (N : ℕ) {F G : ℕ → ℝ} (h0 : ∀ j, 0 ≤ F j) (hlt : ∀ j, F j < G j) :
    ∏ j ∈ Finset.range (N + 1), F j < ∏ j ∈ Finset.range (N + 1), G j := by
  induction N with
  | zero => simpa using hlt 0
  | succ N ih =>
    have hFnn : 0 ≤ ∏ j ∈ Finset.range (N + 1), F j := Finset.prod_nonneg fun j _ => h0 j
    have hGN : 0 < G (N + 1) := lt_of_le_of_lt (h0 (N + 1)) (hlt (N + 1))
    rw [Finset.prod_range_succ F (N + 1), Finset.prod_range_succ G (N + 1)]
    calc (∏ j ∈ Finset.range (N + 1), F j) * F (N + 1)
        ≤ (∏ j ∈ Finset.range (N + 1), F j) * G (N + 1) :=
          mul_le_mul_of_nonneg_left (hlt (N + 1)).le hFnn
      _ < (∏ j ∈ Finset.range (N + 1), G j) * G (N + 1) := mul_lt_mul_of_pos_right ih hGN

/-- **`(μ)_N (μ+α+β)_N < (μ+α)_N (μ+β)_N`** for `N ≥ 1`, `μ ≥ 0`, `α, β > 0`:
factor by factor the two products differ by exactly `αβ`. -/
theorem poch_mul_lt {N : ℕ} (hN : 1 ≤ N) {μ α β : ℝ} (hμ : 0 ≤ μ) (hα : 0 < α) (hβ : 0 < β) :
    poch μ N * poch (μ + α + β) N < poch (μ + α) N * poch (μ + β) N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  unfold poch
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine prod_lt_prod_of_lt M (fun j => ?_) (fun j => ?_)
  · have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    exact mul_nonneg (by linarith) (by linarith)
  · have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    have hid : (μ + α + (j:ℝ)) * (μ + β + (j:ℝ)) - (μ + (j:ℝ)) * (μ + α + β + (j:ℝ)) = α * β := by
      ring
    have := mul_pos hα hβ
    linarith

theorem cmf_eq_zero_of_lt_two {f : ℕ → ℝ} {m : ℕ} (hm : m < 2) (u v : ℝ) : cmf f m u v = 0 := by
  have he : Finset.Icc 1 (m - 1) = ∅ := Finset.Icc_eq_empty (by omega)
  simp [cmf, cmw, he]

/-- At `m = 2a` with `a` the least index of the support, the convolution
`eq:C-def` has a single surviving term: `r < a` kills `f_r` and `r > a` kills
`f_{2a-r}`. -/
theorem cmf_two_mul_min {f : ℕ → ℝ} {a : ℕ} (ha : 1 ≤ a)
    (hmin : ∀ n, 1 ≤ n → n < a → f n = 0) (u v : ℝ) :
    cmf f (2 * a) u v
      = f a * f a * (poch u (3 * a) * poch v (3 * a))
          / ((Nat.factorial (3 * a - 1) : ℝ) * (Nat.factorial (3 * a - 1) : ℝ)) := by
  have hmem : a ∈ Finset.Icc 1 (2 * a - 1) := Finset.mem_Icc.mpr ⟨ha, by omega⟩
  have hother : ∀ r ∈ Finset.Icc 1 (2 * a - 1), r ≠ a →
      (f r * f (2 * a - r)) * (poch u (3 * r) * poch v (3 * (2 * a - r)))
        / ((Nat.factorial (3 * r - 1) : ℝ) * (Nat.factorial (3 * (2 * a - r) - 1) : ℝ)) = 0 := by
    intro r hr hra
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hr
    rcases lt_or_gt_of_ne hra with hlt | hgt
    · rw [hmin r h1 hlt]; ring
    · rw [hmin (2 * a - r) (by omega) (by omega)]; ring
  simp only [cmf, cmw]
  rw [Finset.sum_eq_single_of_mem a hmem hother]
  have hidx : 2 * a - a = a := by omega
  rw [hidx]

/-- **The degree-`2a` coefficient is strictly positive** (`cor:strict`'s
instance at the least support index, proved here from `poch_mul_lt` rather than
from the strict kernel monotonicity). -/
theorem cmf_two_mul_min_strict {f : ℕ → ℝ} {a : ℕ} (ha : 1 ≤ a) (hfa : 0 < f a)
    (hmin : ∀ n, 1 ≤ n → n < a → f n = 0) {μ α β : ℝ} (hμ : 0 ≤ μ) (hα : 0 < α) (hβ : 0 < β) :
    cmf f (2 * a) μ (μ + α + β) < cmf f (2 * a) (μ + α) (μ + β) := by
  rw [cmf_two_mul_min ha hmin, cmf_two_mul_min ha hmin]
  have hnum : f a * f a * (poch μ (3 * a) * poch (μ + α + β) (3 * a))
      < f a * f a * (poch (μ + α) (3 * a) * poch (μ + β) (3 * a)) :=
    mul_lt_mul_of_pos_left (poch_mul_lt (by omega) hμ hα hβ) (by positivity)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right hnum (by positivity)

/-! ### The strict pointwise Turán inequality -/

/-- **`cor:ordinary`'s Turán inequality**: for `μ ≥ 0` and `α, β > 0`,

  `F_f(μ;x) F_f(μ+α+β;x) < F_f(μ+α;x) F_f(μ+β;x)`.

Every coefficient of the difference is nonnegative by `thm:main`
(`turan_coeff_nonneg_of_logConcave`), and the coefficient at `m = 2a` is
strictly positive, so the sums separate. -/
theorem fser_turan_strict {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hlc : LogConcaveSeq f)
    (hint : IntervalSupport f) {a : ℕ} (ha : 1 ≤ a) (hfa : 0 < f a)
    (hmin : ∀ n, 1 ≤ n → n < a → f n = 0) {μ α β x y : ℝ} (hμ : 0 ≤ μ) (hα : 0 < α)
    (hβ : 0 < β) (hx : 0 < x) (hxy : x < y) (hy : Summable fun n => f n * y ^ n) :
    fser f μ x * fser f (μ + α + β) x < fser f (μ + α) x * fser f (μ + β) x := by
  have hbalanced : fser f μ x * fser f (μ + α + β) x = ∑' m, cmf f m μ (μ + α + β) * x ^ m :=
    fser_mul hf hμ (by linarith) hx hxy hy
  have hspread : fser f (μ + α) x * fser f (μ + β) x = ∑' m, cmf f m (μ + α) (μ + β) * x ^ m :=
    fser_mul hf (by linarith) (by linarith) hx hxy hy
  rw [hbalanced, hspread]
  have hle : ∀ m : ℕ, cmf f m μ (μ + α + β) * x ^ m ≤ cmf f m (μ + α) (μ + β) * x ^ m := by
    intro m
    rcases lt_or_ge m 2 with hm | hm
    · rw [cmf_eq_zero_of_lt_two hm, cmf_eq_zero_of_lt_two hm]
    · have := turan_coeff_nonneg_of_logConcave f m hm hf hlc hint μ α β hμ hα.le hβ.le
      have hxm : (0:ℝ) ≤ x ^ m := by positivity
      nlinarith [this, hxm]
  have hlt : cmf f (2 * a) μ (μ + α + β) * x ^ (2 * a)
      < cmf f (2 * a) (μ + α) (μ + β) * x ^ (2 * a) :=
    mul_lt_mul_of_pos_right (cmf_two_mul_min_strict ha hfa hmin hμ hα hβ) (by positivity)
  exact (summable_cmf hf hμ (by linarith) hx hxy hy).tsum_lt_tsum hle hlt
    (summable_cmf hf (by linarith) (by linarith) hx hxy hy)

/-! ### Strict midpoint concavity upgraded to strict concavity -/

/-- The chord of `g` through `(p, g p)` and `(q, g q)`, read as a function of the abscissa. -/
noncomputable def chord (g : ℝ → ℝ) (p q w : ℝ) : ℝ :=
  g p + (w - p) / (q - p) * (g q - g p)

/-- The chord takes the value `g p` at `p`. -/
theorem chord_left (g : ℝ → ℝ) (p q : ℝ) : chord g p q p = g p := by
  unfold chord; simp

/-- The chord takes the value `g q` at `q`. -/
theorem chord_right (g : ℝ → ℝ) {p q : ℝ} (hpq : p < q) : chord g p q q = g q := by
  have hqp : q - p ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  unfold chord; field_simp; ring

/-- The chord is affine, so it reproduces its own midpoints.  This is the only property
of the interpolant the argument below uses, and it is what makes the strict midpoint
inequality for `g` a strict inequality for `g - chord`. -/
theorem chord_midpoint (g : ℝ → ℝ) (p q w δ : ℝ) :
    (chord g p q (w - δ) + chord g p q (w + δ)) / 2 = chord g p q w := by
  unfold chord; ring

/-- The chord is continuous. -/
theorem continuous_chord (g : ℝ → ℝ) (p q : ℝ) : Continuous (chord g p q) := by
  unfold chord; fun_prop

/-- **No interior minimizer.**  Where `g` is strictly midpoint concave on `s` and
`[p,q] ⊆ s`, the difference `g - chord` has no minimum over `[p,q]` at an interior point:
at such a `w`, the strict midpoint inequality at `w ± δ` beats minimality, the chord
contributing nothing because `chord_midpoint` reproduces its own midpoints. -/
theorem not_isMinOn_sub_chord {s : Set ℝ} {g : ℝ → ℝ}
    (hmid : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (g a + g b) / 2 < g ((a + b) / 2))
    {p q : ℝ} (hsub : Icc p q ⊆ s) {w : ℝ} (hw1 : p < w) (hw2 : w < q) :
    ¬ IsMinOn (fun v => g v - chord g p q v) (Icc p q) w := by
  intro hmin
  have hmin' : ∀ v ∈ Icc p q, g w - chord g p q w ≤ g v - chord g p q v := fun v hv => hmin hv
  set δ : ℝ := min (w - p) (q - w) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hm1 : w - δ ∈ Icc p q := ⟨by have : δ ≤ w - p := min_le_left _ _; linarith, by linarith⟩
  have hm2 : w + δ ∈ Icc p q := ⟨by linarith, by have : δ ≤ q - w := min_le_right _ _; linarith⟩
  have hstrict := hmid (w - δ) (hsub hm1) (w + δ) (hsub hm2) (by intro hEq; linarith [hEq])
  rw [show (w - δ + (w + δ)) / 2 = w from by ring] at hstrict
  linarith [hmin' _ hm1, hmin' _ hm2, chord_midpoint g p q w δ]

/-- **Chord form of strict concavity.**  On a convex `s` where `g` is continuous and
strictly midpoint concave, the chord through two points of `s` lies strictly below `g`
between them.

`g - chord` is continuous on the compact `[p,q]`, so it attains a minimum there;
`not_isMinOn_sub_chord` forces that minimum to an endpoint, where the chord meets `g` and
the difference is `0`, and the same lemma then excludes the value `0` at an interior
point.  No dyadic approximation is involved. -/
theorem chord_lt_of_midpoint {s : Set ℝ} (hs : Convex ℝ s) {g : ℝ → ℝ}
    (hcont : ContinuousOn g s)
    (hmid : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (g a + g b) / 2 < g ((a + b) / 2))
    {p q : ℝ} (hp : p ∈ s) (hq : q ∈ s) (hpq : p < q) {z : ℝ} (hz1 : p < z) (hz2 : z < q) :
    chord g p q z < g z := by
  have hsub : Icc p q ⊆ s := by
    rw [← segment_eq_Icc hpq.le]; exact hs.segment_subset hp hq
  have hcont' : ContinuousOn (fun v => g v - chord g p q v) (Icc p q) :=
    (hcont.mono hsub).sub (continuous_chord g p q).continuousOn
  obtain ⟨z₀, hz₀mem, hz₀min⟩ :=
    (isCompact_Icc (a := p) (b := q)).exists_isMinOn (nonempty_Icc.mpr hpq.le) hcont'
  have hmin' : ∀ v ∈ Icc p q, g z₀ - chord g p q z₀ ≤ g v - chord g p q v :=
    fun v hv => hz₀min hv
  have hz₀val : g z₀ - chord g p q z₀ = 0 := by
    obtain ⟨hl, hr⟩ := hz₀mem
    rcases eq_or_lt_of_le hl with heq | hlt
    · rw [← heq, chord_left]; ring
    rcases eq_or_lt_of_le hr with heq | hlt2
    · rw [heq, chord_right g hpq]; ring
    · exact absurd hz₀min (not_isMinOn_sub_chord hmid hsub hlt hlt2)
  rcases eq_or_lt_of_le (by linarith [hmin' z ⟨hz1.le, hz2.le⟩] :
      (0 : ℝ) ≤ g z - chord g p q z) with heq | hlt
  · exfalso
    refine not_isMinOn_sub_chord hmid hsub hz1 hz2 (isMinOn_iff.mpr fun v hv => ?_)
    linarith [hmin' v hv]
  · linarith

/-- **From a strict Turán inequality to strict midpoint concavity of `log`.**
For positive `A, B, C` with `A B < C²`, the logarithmic midpoint sits strictly
below: `(\log A + \log B)/2 < \log C`.

This is the only place logarithms enter `cor:ordinary`.  Everything before it is
the Turán inequality `fser_turan_strict` for the series itself, and this lemma
is what turns that inequality into a statement about `\log F_f`. -/
theorem log_midpoint_lt_of_mul_lt_sq {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A * B < C * C) : (Real.log A + Real.log B) / 2 < Real.log C := by
  have hlogmul : Real.log (A * B) < Real.log (C * C) := Real.log_lt_log (by positivity) h
  rw [Real.log_mul (ne_of_gt hA) (ne_of_gt hB),
    Real.log_mul (ne_of_gt hC) (ne_of_gt hC)] at hlogmul
  linarith

/-- **Strict midpoint concavity plus continuity gives strict concavity**, which
is `cor:ordinary`'s last step («continuity gives concavity, and equality at any
interior convex combination would force affinity on an interval»).  The content
is `chord_lt_of_midpoint`; what remains is to read the convex combination
`c·p + d·q` as an interior point and its chord value as `c·g p + d·g q`. -/
theorem strictConcaveOn_of_midpoint {s : Set ℝ} (hs : Convex ℝ s) {g : ℝ → ℝ}
    (hcont : ContinuousOn g s)
    (hmid : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (g a + g b) / 2 < g ((a + b) / 2)) :
    StrictConcaveOn ℝ s g := by
  refine ⟨hs, ?_⟩
  intro p hp q hq hpq c d hc hd hcd
  simp only [smul_eq_mul]
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · have hqp : (0 : ℝ) < q - p := by linarith
    have e1 : c * p + d * q - p = d * (q - p) := by linear_combination p * hcd
    have hz1 : p < c * p + d * q := by linarith [mul_pos hd hqp]
    have hz2 : c * p + d * q < q := by
      have e2 : q - (c * p + d * q) = c * (q - p) := by linear_combination (-q) * hcd
      linarith [mul_pos hc hqp]
    have hk := chord_lt_of_midpoint hs hcont hmid hp hq hlt hz1 hz2
    unfold chord at hk
    rw [show (c * p + d * q - p) / (q - p) = d from by rw [e1]; field_simp] at hk
    rw [show c * g p + d * g q = g p + d * (g q - g p) from by
      rw [show c = 1 - d from by linarith]; ring]
    exact hk
  · have hpq' : (0 : ℝ) < p - q := by linarith
    have e1 : c * p + d * q - q = c * (p - q) := by linear_combination q * hcd
    have hz1 : q < c * p + d * q := by linarith [mul_pos hc hpq']
    have hz2 : c * p + d * q < p := by
      have e2 : p - (c * p + d * q) = d * (p - q) := by linear_combination (-p) * hcd
      linarith [mul_pos hd hpq']
    have hk := chord_lt_of_midpoint hs hcont hmid hq hp hlt hz1 hz2
    unfold chord at hk
    rw [show (c * p + d * q - q) / (p - q) = c from by rw [e1]; field_simp] at hk
    rw [show c * g p + d * g q = g q + c * (g p - g q) from by
      rw [show d = 1 - c from by linarith]; ring]
    exact hk

/-! ### `cor:ordinary` -/

/-- The support of a nonzero nonnegative sequence has a least element. -/
theorem exists_min_support {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hne : ∃ n, 1 ≤ n ∧ 0 < f n) :
    ∃ a, 1 ≤ a ∧ 0 < f a ∧ ∀ n, 1 ≤ n → n < a → f n = 0 := by
  have hP : ∃ n, 1 ≤ n ∧ 0 < f n := hne
  obtain ⟨h1, h2⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, h1, h2, fun n hn1 hn => ?_⟩
  have := Nat.find_min hP hn
  rcases (hf n).lt_or_eq with hlt | heq
  · exact absurd ⟨hn1, hlt⟩ this
  · exact heq.symm

/-- **`μ ↦ log F_f(μ;x)` is strictly concave on `(0,∞)`** (`cor:ordinary`).
Strict midpoint concavity is `fser_turan_strict` at `α = β`, and continuity
promotes it to strict concavity. -/
theorem log_fser_strictConcaveOn {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hlc : LogConcaveSeq f)
    (hint : IntervalSupport f) (hne : ∃ n, 1 ≤ n ∧ 0 < f n) {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy : Summable fun n => f n * y ^ n) :
    StrictConcaveOn ℝ (Ioi 0) fun μ => Real.log (fser f μ x) := by
  obtain ⟨a, ha, hfa, hmin⟩ := exists_min_support hf hne
  have hane : a ≠ 0 := by omega
  have hpos : ∀ μ : ℝ, 0 < μ → 0 < fser f μ x := fun μ hμ =>
    fser_pos hf hane hfa hμ hx hxy hy
  refine strictConcaveOn_of_midpoint (convex_Ioi 0) ?_ ?_
  · exact (fser_continuousOn_Ioi hf hx hxy hy).log fun μ hμ => ne_of_gt (hpos μ hμ)
  · intro u hu v hv huv
    have hu0 : 0 < u := hu
    have hv0 : 0 < v := hv
    rcases lt_or_gt_of_ne huv with hlt | hlt
    · have hhalf : 0 < (v - u) / 2 := by linarith
      have hk := fser_turan_strict hf hlc hint ha hfa hmin (le_of_lt hu0) hhalf hhalf hx hxy hy
      rw [show u + (v - u) / 2 + (v - u) / 2 = v by ring,
        show u + (v - u) / 2 = (u + v) / 2 by ring] at hk
      exact log_midpoint_lt_of_mul_lt_sq (hpos u hu0) (hpos v hv0) (hpos _ (by linarith)) hk
    · have hhalf : 0 < (u - v) / 2 := by linarith
      have hk := fser_turan_strict hf hlc hint ha hfa hmin (le_of_lt hv0) hhalf hhalf hx hxy hy
      rw [show v + (u - v) / 2 + (u - v) / 2 = u by ring,
        show v + (u - v) / 2 = (u + v) / 2 by ring] at hk
      have := log_midpoint_lt_of_mul_lt_sq (hpos v hv0) (hpos u hu0)
        (hpos ((u + v) / 2) (by linarith)) hk
      linarith

/-- **`cor:ordinary`** in full.  `R` is carried by the property the paper's proof
consumes — the series `Σ f_n z^n` converges at every `0 ≤ z < R` — so `R` is (at
most) the radius of convergence of `Σ_{n≥1} f_n x^n`, and `x` is any point of
`(0,R)`.  Then

* `F_f(μ;x)` is finite for every `μ ≥ 0`,
* positive for every `μ > 0`,
* continuous in `μ` on `(0,∞)`,
* `log F_f(·;x)` is strictly concave on `(0,∞)`, and
* the strict Turán inequality holds for `μ ≥ 0` and `α, β > 0`.

No Stirling asymptotics enter: the majorant `poch_le_factorial_mul_pow` and the
Weierstrass test do the analytic work, and the strictness comes from the
single-term degree-`2a` coefficient rather than from `cor:strict`. -/
theorem cor_ordinary {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hlc : LogConcaveSeq f)
    (hint : IntervalSupport f) (hne : ∃ n, 1 ≤ n ∧ 0 < f n) {R x : ℝ}
    (hR : ∀ z : ℝ, 0 ≤ z → z < R → Summable fun n => f n * z ^ n)
    (hx : 0 < x) (hxR : x < R) :
    (∀ μ : ℝ, 0 ≤ μ → Summable fun n => aser f μ n * x ^ n) ∧
      (∀ μ : ℝ, 0 < μ → 0 < fser f μ x) ∧
      ContinuousOn (fun μ => fser f μ x) (Ioi 0) ∧
      StrictConcaveOn ℝ (Ioi 0) (fun μ => Real.log (fser f μ x)) ∧
      (∀ μ α β : ℝ, 0 ≤ μ → 0 < α → 0 < β →
        fser f μ x * fser f (μ + α + β) x < fser f (μ + α) x * fser f (μ + β) x) := by
  obtain ⟨a, ha, hfa, hmin⟩ := exists_min_support hf hne
  set y : ℝ := (x + R) / 2 with hydef
  have hxy : x < y := by rw [hydef]; linarith
  have hyR : y < R := by rw [hydef]; linarith
  have hy0 : (0:ℝ) ≤ y := by rw [hydef]; linarith
  have hy : Summable fun n => f n * y ^ n := hR y hy0 hyR
  refine ⟨fun μ hμ => summable_aser hf hμ hx hxy hy,
    fun μ hμ => fser_pos hf (by omega : a ≠ 0) hfa hμ hx hxy hy,
    fser_continuousOn_Ioi hf hx hxy hy,
    log_fser_strictConcaveOn hf hlc hint hne hx hxy hy,
    fun μ α β hμ hα hβ => fser_turan_strict hf hlc hint ha hfa hmin hμ hα hβ hx hxy hy⟩

/-! ### The differential Turánian at the coefficient level

`cor:differential` is about `[x^m][(∂_μ F_f)² - F_f ∂_μ² F_f]`.  `dcoeff` below
is that coefficient written out as the antidiagonal sum of coefficient
derivatives, which is what the paper's proof manipulates.  **What is proved here
is exactly what is stated about `dcoeff`**: the identification of `dcoeff` with a
coefficient of the analytic `F_f` is a term-wise differentiation in `μ` that is
not carried out in this file, and the strict positivity for `μ > 0` is not
proved here either — see the module docstring. -/

/-- `(t)_N` has derivative `(N-1)!` at `t = 0`: only the factor `t` itself
survives, the rest of the product evaluating to `(N-1)!`. -/
theorem hasDerivAt_poch_zero {N : ℕ} (hN : 1 ≤ N) :
    HasDerivAt (fun t : ℝ => poch t N) ((Nat.factorial (N - 1) : ℝ)) 0 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨c, hQ⟩ : ∃ c, HasDerivAt (fun t : ℝ => ∏ i ∈ Finset.range M, (t + ((i:ℝ) + 1))) c 0 :=
    ⟨_, HasDerivAt.fun_finsetProd fun i _ => (hasDerivAt_id (0:ℝ)).add_const _⟩
  have hQ0 : (∏ i ∈ Finset.range M, ((0:ℝ) + ((i:ℝ) + 1))) = (Nat.factorial M : ℝ) := by
    have h : ((∏ i ∈ Finset.range M, (i + 1) : ℕ) : ℝ) = (Nat.factorial M : ℝ) := by
      rw [Finset.prod_range_add_one_eq_factorial]
    push_cast at h
    simpa using h
  have heq : (fun t : ℝ => poch t (M + 1))
      = fun t : ℝ => (∏ i ∈ Finset.range M, (t + ((i:ℝ) + 1))) * t := by
    funext t
    rw [poch, Finset.prod_range_succ' (fun i => t + (i:ℝ)) M]
    push_cast
    ring_nf
  rw [heq, show M + 1 - 1 = M from rfl]
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id' 0
  have hmul := hQ.mul hid
  convert hmul using 1
  rw [hQ0]
  ring

section DerivativeAtZero

variable (f : ℕ → ℝ)

theorem aser_at_zero (n : ℕ) : aser f 0 n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [aser_of_ne_zero f 0 hn, poch_zero_eq_zero (by omega)]
    simp

theorem aser_fun_eq_zero {n : ℕ} (hn : f n = 0 ∨ n = 0) :
    (fun t : ℝ => aser f t n) = fun _ => 0 := by
  funext t
  rcases hn with h | rfl
  · rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [aser_of_ne_zero f t hn0, h]; simp
  · simp

/-- `∂_μ` of the degree-`n` coefficient at `μ = 0` is `f_n`, since
`∂_μ (μ)_{3n}/(3n-1)!` is `1` there — the identity behind `cor:differential`'s
`μ = 0` case. -/
theorem hasDerivAt_aser_zero {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt (fun t : ℝ => aser f t n) (f n) 0 := by
  have hfun : (fun t : ℝ => aser f t n)
      = fun t : ℝ => f n * poch t (3 * n) / (Nat.factorial (3 * n - 1) : ℝ) :=
    funext fun t => aser_of_ne_zero f t hn
  rw [hfun]
  have hpoch : HasDerivAt (fun t : ℝ => poch t (3 * n)) ((Nat.factorial (3 * n - 1) : ℝ)) 0 :=
    hasDerivAt_poch_zero (by omega)
  have hscaled := (HasDerivAt.const_mul (f n) hpoch).div_const ((Nat.factorial (3 * n - 1) : ℝ))
  have hcancel : f n * (Nat.factorial (3 * n - 1) : ℝ) / (Nat.factorial (3 * n - 1) : ℝ) = f n := by
    have : ((Nat.factorial (3 * n - 1) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  rwa [hcancel] at hscaled

theorem deriv_aser_at_zero (n : ℕ) :
    deriv (fun t : ℝ => aser f t n) 0 = if n = 0 then 0 else f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl, aser_fun_eq_zero f (Or.inr rfl)]
    simp
  · rw [if_neg hn]
    exact (hasDerivAt_aser_zero f hn).deriv

/-- The degree-`m` coefficient of `(∂_μ F_f)² - F_f ∂_μ² F_f` (`cor:differential`),
written as the antidiagonal sum `Σ_{k+l=m} (a_k' a_l' - a_k a_l'')` of the
coefficient functions `a_n(μ) = f_n (μ)_{3n}/(3n-1)!`. -/
noncomputable def dcoeff (m : ℕ) (μ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (deriv (fun t => aser f t k) μ * deriv (fun t => aser f t (m - k)) μ
      - aser f μ k * deriv (deriv fun t => aser f t (m - k)) μ)

/-- **`cor:differential` at `μ = 0`**: `F_f(0;x) = 0` and `∂_μ F_f(0;x) = Σ f_n
x^n`, so the differential Turánian degenerates to the square of that series and
its degree-`m` coefficient is `Σ_{k+l=m} f_k f_l`. -/
theorem dcoeff_at_zero (m : ℕ) :
    dcoeff f m 0 = ∑ k ∈ Finset.Icc 1 (m - 1), f k * f (m - k) := by
  have hsub : Finset.Icc 1 (m - 1) ⊆ Finset.range (m + 1) := by
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    simp only [Finset.mem_range]
    omega
  have hterm : ∀ k ∈ Finset.range (m + 1),
      (deriv (fun t => aser f t k) 0 * deriv (fun t => aser f t (m - k)) 0
        - aser f 0 k * deriv (deriv fun t => aser f t (m - k)) 0)
      = (if k = 0 then 0 else f k) * (if m - k = 0 then 0 else f (m - k)) := by
    intro k _
    rw [aser_at_zero, deriv_aser_at_zero, deriv_aser_at_zero]
    ring
  rw [dcoeff, Finset.sum_congr rfl hterm]
  rw [← Finset.sum_subset hsub ?_]
  · refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ m - k = 0)]
  · intro k hk hk'
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc, not_and, not_le] at hk'
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · have : m - k = 0 := by
        have := hk' hkpos
        omega
      rw [this]
      simp

/-- **`cor:differential`'s vanishing half**, at every `μ`: if no `k+l=m` has both
`f_k` and `f_l` positive — that is, `m ∉ I+I` — then every term of the
antidiagonal carries a factor that is identically zero in `μ`. -/
theorem dcoeff_eq_zero_of_weights {m : ℕ}
    (h : ∀ k, 1 ≤ k → k ≤ m - 1 → f k * f (m - k) = 0) (μ : ℝ) : dcoeff f m μ = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hzero : (fun t : ℝ => aser f t k) = (fun _ => 0)
      ∨ (fun t : ℝ => aser f t (m - k)) = fun _ => 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact Or.inl (aser_fun_eq_zero f (Or.inr rfl))
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with heq | hlt
    · exact Or.inr (aser_fun_eq_zero f (Or.inr (by omega)))
    · have hw := h k hkpos (by omega)
      rcases mul_eq_zero.mp hw with h1 | h1
      · exact Or.inl (aser_fun_eq_zero f (Or.inl h1))
      · exact Or.inr (aser_fun_eq_zero f (Or.inl h1))
  rcases hzero with h1 | h1
  · have hzero : aser f μ k = 0 := congrFun h1 μ
    rw [h1, hzero]
    simp
  · have hzero : aser f μ (m - k) = 0 := congrFun h1 μ
    rw [h1]
    simp

end DerivativeAtZero

/-- **`cor:differential`'s support statement at `μ = 0`**: the degree-`m`
coefficient is positive exactly when `m ∈ I+I`. -/
theorem dcoeff_at_zero_pos_iff {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {m : ℕ} (hm : 2 ≤ m) :
    0 < dcoeff f m 0 ↔ ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧ i + j = m ∧ 0 < f i ∧ 0 < f j := by
  rw [dcoeff_at_zero]
  constructor
  · intro hpos
    by_contra hcon
    have hz : ∀ k ∈ Finset.Icc 1 (m - 1), f k * f (m - k) = 0 := by
      intro k hk
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
      by_contra hne
      obtain ⟨hk1, hk2⟩ := mul_ne_zero_iff.mp hne
      exact hcon ⟨k, m - k, h1, by omega, by omega,
        lt_of_le_of_ne (hf k) (Ne.symm hk1), lt_of_le_of_ne (hf (m - k)) (Ne.symm hk2)⟩
    rw [Finset.sum_congr rfl hz] at hpos
    simp at hpos
  · rintro ⟨i, j, hi, hj, hij, hfi, hfj⟩
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hf k) (hf (m - k))) ⟨i, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hi, by omega⟩
    · rw [show m - i = j by omega]
      exact mul_pos hfi hfj

end CubicPochhammer
