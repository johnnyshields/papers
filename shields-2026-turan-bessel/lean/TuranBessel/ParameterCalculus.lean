/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Zseries
import TuranBessel.Trigamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Deriv

/-!
# Parameter calculus of the reciprocal-gamma series

Differentiation of `Z(a,\lambda)=\sum_k \lambda^k/(k!\Gamma(a+k))` in the **parameter** `a`,
which is the half of `shields-2026-turan-bessel.tex`, «Reciprocal-gamma convolution and
canonical--microcanonical structure» (`sec:coefficients`, `thm:coefficients`) that the
combinatorial identities of `Convolution` and `Zseries` do not reach.  The paper takes
`\partial_a` and `\partial_a^2` of `Z` termwise and reads off the polygamma family
`\psi_j(a+k)`; Mathlib carries `Complex.digamma` and nothing above it.

* `realDigamma` — `\psi = (\log\Gamma)'` on `(0,\infty)`, with `digamma_ofReal` identifying it
  with Mathlib's `Complex.digamma` on the positive reals, `realDigamma_add_one` the recurrence,
  `realDigamma_monotoneOn` its monotonicity (from `convexOn_log_Gamma`), and
  `abs_realDigamma_add_nat_le` the linear-in-`k` bound the domination arguments run on.
* `hasDerivAt_inv_Gamma`, `hasDerivAt_zterm`, `hasDerivAt_dzterm` — the weight derivatives
  `\partial_a\Gamma(a)^{-1}=-\psi(a)/\Gamma(a)` and the first two `a`-derivatives of the `k`-th
  term of `Z`, the second being `(\psi^2-\psi_1)(a+k)` times the term.
* `hasDerivAt_Zfun_param`, `hasDerivAt_deriv_Zfun` — **differentiation under the summation
  sign**, twice.  The Weierstrass domination is uniform on `(a/2,a+1)`, which is what the
  paper's local statements consume; `eq:A-second-delta` assembles `A=ZZ_{aa}-Z_a^2` from
  these two series.
* `deriv_realDigamma_eq_trigamma`, `deriv_digamma_ofReal` — **`\psi'=\psi_1`**, connecting the
  from-scratch `trigamma` of `Trigamma` to Mathlib's `digamma`.  `\psi` and the regularized
  series `digammaSeries` satisfy the same recurrence, so their difference has period `1`; the
  difference is monotone because `\psi'\ge\psi_1` termwise, and a monotone function of period
  `1` on `(0,\infty)` is constant.  This is what licenses reading `lem:trigamma-bounds` and the
  normalization `turanCoeffFactor` as statements about the classical trigamma function.
* `realDigamma_eq_gauss` — Gauss's series `\psi(y)=-\gamma+\sum_n(1/(n+1)-1/(y+n))`, the
  function-level form of the same constancy, with the constant fixed by `Complex.digamma_one`.

* `gammaPairInv`, `deriv_deriv_Fdelta` — **`eq:F-second-delta`**: `F_m''(0)=-2S_m\psi_1(a+m)`
  for the closed form `eq:Fdelta` that `lem:convolution` supplies.  The score
  `-\psi(y+\delta)+\psi(y-\delta)` vanishes at `\delta=0`, so only the second log-derivative
  survives, and identifying it as `\psi_1` is exactly what `deriv_realDigamma_eq_trigamma` gives.

Sorry-free, and axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Filter Topology Set
open scoped BigOperators

namespace TuranBessel

variable {y : ℝ}
variable {a : ℝ}

/-! ### The real digamma function -/

/-- `ψ(y) = (log Γ)'(y)`, the real digamma function. -/
noncomputable def realDigamma (y : ℝ) : ℝ := deriv (Real.log ∘ Real.Gamma) y

private theorem ne_neg_nat_of_pos (hy : 0 < y) (m : ℕ) : y ≠ -(m : ℝ) := by
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  intro h; rw [h] at hy; linarith

/-- `log ∘ Γ` is differentiable on the positive half line. -/
theorem differentiableAt_log_Gamma (hy : 0 < y) :
    DifferentiableAt ℝ (Real.log ∘ Real.Gamma) y := by
  refine (Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_) <;>
    exact ne_neg_nat_of_pos hy

/-- `ψ = Γ'/Γ` on the positive half line. -/
theorem realDigamma_eq_div (hy : 0 < y) :
    realDigamma y = deriv Real.Gamma y / Real.Gamma y := by
  rw [realDigamma, Function.comp_def,
    deriv.log (Real.differentiableAt_Gamma (ne_neg_nat_of_pos hy))
      (Real.Gamma_pos_of_pos hy).ne']

/-- `ψ(y+1) = ψ(y) + 1/y`, the digamma recurrence. -/
theorem realDigamma_add_one (hy : 0 < y) :
    realDigamma (y + 1) = realDigamma y + 1 / y := by
  have h_rec : ∀ x : ℝ, 0 < x →
      (Real.log ∘ Real.Gamma) (x + 1) = (Real.log ∘ Real.Gamma) x + Real.log x := by
    intro x hx
    simp only [Function.comp_apply, Real.Gamma_add_one hx.ne',
      Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne', add_comm]
  rw [realDigamma, realDigamma, ← deriv_comp_add_const, one_div, ← Real.deriv_log,
    ← deriv_add (differentiableAt_log_Gamma hy) (Real.differentiableAt_log hy.ne')]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_gt_nhds hy] using h_rec

/-! ### Agreement with Mathlib's `Complex.digamma` -/

private theorem ofReal_ne_neg_nat (hy : 0 < y) (m : ℕ) : (y : ℂ) ≠ -(m : ℂ) := by
  intro h
  have : y = -(m : ℝ) := by exact_mod_cast h
  exact ne_neg_nat_of_pos hy m this

/-- The complex derivative of `Γ` at a positive real point is the real one. -/
theorem ofReal_deriv_Gamma (hy : 0 < y) :
    deriv Complex.Gamma (y : ℂ) = ((deriv Real.Gamma y : ℝ) : ℂ) := by
  have hC : HasDerivAt Complex.Gamma (deriv Complex.Gamma (y : ℂ)) (y : ℂ) :=
    (Complex.differentiableAt_Gamma _ (ofReal_ne_neg_nat hy)).hasDerivAt
  have h1 : HasDerivAt (fun x : ℝ => Complex.Gamma (x : ℂ)) (deriv Complex.Gamma (y : ℂ)) y :=
    hC.comp_ofReal
  have hR : HasDerivAt Real.Gamma (deriv Real.Gamma y) y :=
    (Real.differentiableAt_Gamma (ne_neg_nat_of_pos hy)).hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => ((Real.Gamma x : ℝ) : ℂ))
      ((deriv Real.Gamma y : ℝ) : ℂ) y := hR.ofReal_comp
  exact h1.unique (h2.congr_of_eventuallyEq (by
    filter_upwards with x using Complex.Gamma_ofReal x))

/-- **`Complex.digamma` restricted to the positive reals is `realDigamma`.** -/
theorem digamma_ofReal (hy : 0 < y) :
    Complex.digamma (y : ℂ) = ((realDigamma y : ℝ) : ℂ) := by
  rw [Complex.digamma_def, logDeriv_apply, ofReal_deriv_Gamma hy, Complex.Gamma_ofReal,
    realDigamma_eq_div hy, Complex.ofReal_div]

/-! ### Second-order regularity of `ψ` -/

/-- `Complex.digamma` is holomorphic on the open right half plane. -/
theorem differentiableAt_complex_digamma {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.digamma s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m h
    have : (0 : ℝ) < ((-(m : ℂ)).re) := by rw [← h]; exact hz
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hana : AnalyticAt ℂ Complex.Gamma s := hd.analyticAt (hU.mem_nhds hs)
  have hderiv : AnalyticAt ℂ (deriv Complex.Gamma) s := hana.deriv
  have hdiv : DifferentiableAt ℂ (fun z => deriv Complex.Gamma z / Complex.Gamma z) s :=
    hderiv.differentiableAt.div hana.differentiableAt (Complex.Gamma_ne_zero_of_re_pos hs)
  simpa [Complex.digamma_def, logDeriv] using hdiv

/-- `ψ` is differentiable on `(0,∞)`; its derivative is the real part of the complex
derivative of `Complex.digamma`. -/
theorem hasDerivAt_realDigamma (hy : 0 < y) :
    HasDerivAt realDigamma ((deriv Complex.digamma (y : ℂ)).re) y := by
  have hC : HasDerivAt Complex.digamma (deriv Complex.digamma (y : ℂ)) (y : ℂ) :=
    (differentiableAt_complex_digamma (by simpa using hy)).hasDerivAt
  refine hC.real_of_complex.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hy] with x hx
  rw [digamma_ofReal hx, Complex.ofReal_re]

theorem differentiableAt_realDigamma (hy : 0 < y) :
    DifferentiableAt ℝ realDigamma y := (hasDerivAt_realDigamma hy).differentiableAt

/-! ### Monotonicity and the linear bound on `ψ` along integer shifts -/

/-- `ψ` is monotone on `(0,∞)`: it is the derivative of the convex function `log Γ`. -/
theorem realDigamma_monotoneOn : MonotoneOn realDigamma (Ioi (0 : ℝ)) :=
  Real.convexOn_log_Gamma.monotoneOn_deriv (fun _ hx => differentiableAt_log_Gamma hx)

/-- `ψ(y+k) = ψ(y) + ∑_{j<k} 1/(y+j)`, the iterated recurrence. -/
theorem realDigamma_add_nat (hy : 0 < y) (k : ℕ) :
    realDigamma (y + k) = realDigamma y + ∑ j ∈ Finset.range k, 1 / (y + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : 0 < y + (k : ℝ) := by
        have := Nat.cast_nonneg (α := ℝ) k; linarith
      rw [show y + ((k + 1 : ℕ) : ℝ) = (y + (k : ℝ)) + 1 by push_cast; ring,
        realDigamma_add_one hk, ih, Finset.sum_range_succ]
      ring

/-- `ψ(y+k) ≤ ψ(y) + k/y`: the shift grows at most linearly in `k`, which is all the
factorial decay of `1/Γ(a+k)` has to absorb. -/
theorem realDigamma_add_nat_le (hy : 0 < y) (k : ℕ) :
    realDigamma (y + k) ≤ realDigamma y + k / y := by
  rw [realDigamma_add_nat hy]
  have : ∑ j ∈ Finset.range k, 1 / (y + (j : ℝ)) ≤ ∑ _j ∈ Finset.range k, 1 / y := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    exact one_div_le_one_div_of_le hy (by linarith)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hk : (k : ℝ) * (1 / y) = (k : ℝ) / y := by ring
  linarith [hk ▸ this]

/-- Uniform bound on `|ψ(a+k)|` for `a` in a compact subinterval of `(0,∞)`. -/
theorem abs_realDigamma_add_nat_le {a₀ a₁ a : ℝ} (h₀ : 0 < a₀) (ha : a ∈ Icc a₀ a₁) (k : ℕ) :
    |realDigamma (a + (k : ℝ))| ≤ |realDigamma a₀| + |realDigamma a₁| + (k : ℝ) / a₀ := by
  obtain ⟨hle₀, hle₁⟩ := ha
  have h₁ : 0 < a₁ := lt_of_lt_of_le h₀ (hle₀.trans hle₁)
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hlow : realDigamma a₀ ≤ realDigamma (a + (k : ℝ)) :=
    realDigamma_monotoneOn (mem_Ioi.2 h₀) (mem_Ioi.2 (by linarith)) (by linarith)
  have hup : realDigamma (a + (k : ℝ)) ≤ realDigamma (a₁ + (k : ℝ)) :=
    realDigamma_monotoneOn (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) (by linarith)
  have hup2 : realDigamma (a₁ + (k : ℝ)) ≤ realDigamma a₁ + (k : ℝ) / a₀ := by
    refine (realDigamma_add_nat_le h₁ k).trans ?_
    have : (k : ℝ) / a₁ ≤ (k : ℝ) / a₀ := by
      apply div_le_div_of_nonneg_left hk h₀ (hle₀.trans hle₁)
    linarith
  rw [abs_le]
  constructor
  · have := neg_abs_le (realDigamma a₀)
    have h2 := abs_nonneg (realDigamma a₁)
    have h3 : (0 : ℝ) ≤ (k : ℝ) / a₀ := by positivity
    linarith
  · have := le_abs_self (realDigamma a₁)
    have h2 := abs_nonneg (realDigamma a₀)
    linarith

/-! ### The derivative of the reciprocal gamma weight -/

/-- **`∂_a Γ(a)⁻¹ = -ψ(a)/Γ(a)`.**  `1/Γ` is entire; on `(0,∞)` its derivative is
read off the real digamma. -/
theorem hasDerivAt_inv_Gamma (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => (Real.Gamma x)⁻¹) (-realDigamma y / Real.Gamma y) y := by
  have hR : HasDerivAt Real.Gamma (deriv Real.Gamma y) y :=
    (Real.differentiableAt_Gamma (ne_neg_nat_of_pos hy)).hasDerivAt
  have hG : Real.Gamma y ≠ 0 := (Real.Gamma_pos_of_pos hy).ne'
  have h := hR.inv hG
  refine h.congr_deriv ?_
  rw [realDigamma_eq_div hy]
  field_simp

/-- **`∂_a` of the `k`-th term of `Z`.**  `∂_a [λ^k/(k!Γ(a+k))] = -ψ(a+k)·λ^k/(k!Γ(a+k))`. -/
theorem hasDerivAt_zterm (ha : 0 < a) (lam : ℝ) (k : ℕ) :
    HasDerivAt (fun x : ℝ => zterm x lam k) (-realDigamma (a + (k : ℝ)) * zterm a lam k) a := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hak : 0 < a + (k : ℝ) := by linarith
  have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hGk : Real.Gamma (a + (k : ℝ)) ≠ 0 := (Real.Gamma_pos_of_pos hak).ne'
  have hshift : HasDerivAt (fun x : ℝ => (Real.Gamma (x + (k : ℝ)))⁻¹)
      (-realDigamma (a + (k : ℝ)) / Real.Gamma (a + (k : ℝ))) a := by
    simpa using (hasDerivAt_inv_Gamma hak).comp a ((hasDerivAt_id a).add_const (k : ℝ))
  have hmul := hshift.const_mul (lam ^ k / (Nat.factorial k : ℝ))
  have hfun : (fun x : ℝ => lam ^ k / (Nat.factorial k : ℝ) * (Real.Gamma (x + (k : ℝ)))⁻¹)
      = fun x : ℝ => zterm x lam k := by
    funext x; rw [zterm]; field_simp
  rw [hfun] at hmul
  refine hmul.congr_deriv ?_
  rw [zterm]
  field_simp

/-! ### Differentiation under the summation sign -/

/-- `1/Γ` is bounded on a compact subinterval of `(0,∞)`. -/
private theorem exists_inv_Gamma_bound {a₀ a₁ : ℝ} (h₀ : 0 < a₀) (h : a₀ ≤ a₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ Icc a₀ a₁, (Real.Gamma x)⁻¹ ≤ K := by
  have hsub : Icc a₀ a₁ ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le h₀ hx.1
  have hcont : ContinuousOn (fun x : ℝ => (Real.Gamma x)⁻¹) (Icc a₀ a₁) :=
    (Real.differentiableOn_Gamma_Ioi.continuousOn.mono hsub).inv₀
      (fun x hx => (Real.Gamma_pos_of_pos (hsub hx)).ne')
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a₀, left_mem_Icc.2 h⟩ hcont
  exact ⟨(Real.Gamma x₀)⁻¹, inv_pos.2 (Real.Gamma_pos_of_pos (hsub hx₀)),
    fun x hx => isMaxOn_iff.1 hmax x hx⟩

/-- On the window `a/2 < x`, a bound `K` on `(Γ x)⁻¹` propagates to every integer shift:
`Γ(x+k) ≥ Γ(x)·min(a/2,1)` by `Gamma_mul_min_le_Gamma_add`, so `(Γ(x+k))⁻¹ ≤ K/min(a/2,1)`
uniformly in `k`.  This is the reciprocal-gamma weight both dominating functions below are
built from. -/
private theorem inv_Gamma_add_nat_le {x K : ℝ} (h₀ : 0 < a / 2) (hx0 : a / 2 < x)
    (hK : (Real.Gamma x)⁻¹ ≤ K) (k : ℕ) :
    (Real.Gamma (x + (k : ℝ)))⁻¹ ≤ K / min (a / 2) 1 := by
  have hxpos : 0 < x := lt_trans h₀ hx0
  have hmin0 : 0 < min (a / 2) 1 := lt_min h₀ one_pos
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hxpos
  have hlow : Real.Gamma x * min (a / 2) 1 ≤ Real.Gamma (x + (k : ℝ)) :=
    le_trans (mul_le_mul_of_nonneg_left (min_le_min hx0.le le_rfl) hGx.le)
      (Gamma_mul_min_le_Gamma_add hxpos k)
  have h1 : (Real.Gamma (x + (k : ℝ)))⁻¹ ≤ (Real.Gamma x * min (a / 2) 1)⁻¹ :=
    inv_anti₀ (by positivity) hlow
  rw [show (Real.Gamma x * min (a / 2) 1)⁻¹ = (Real.Gamma x)⁻¹ / min (a / 2) 1 from by
    rw [mul_inv]; ring] at h1
  exact h1.trans (div_le_div_of_nonneg_right hK hmin0.le)

/-- `‖zterm x lam k‖ = |lam|^k/k! · (Γ(x+k))⁻¹`, so a bound on the reciprocal gamma weight
bounds the term with the exponential-series factor left untouched. -/
private theorem norm_zterm_le {x lam D : ℝ} (hx : 0 < x) (k : ℕ)
    (hinvG : (Real.Gamma (x + (k : ℝ)))⁻¹ ≤ D) :
    ‖zterm x lam k‖ ≤ D * (|lam| ^ k / (Nat.factorial k : ℝ)) := by
  have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hGk : 0 < Real.Gamma (x + (k : ℝ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hnorm : ‖zterm x lam k‖
      = (|lam| ^ k / (Nat.factorial k : ℝ)) * (Real.Gamma (x + (k : ℝ)))⁻¹ := by
    rw [zterm, Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (mul_pos hfk hGk)]
    field_simp
  rw [hnorm, mul_comm]
  exact mul_le_mul_of_nonneg_right hinvG (by positivity)

/-- A summable majorant for the termwise `a`-derivative of `Z`, uniform on `(a/2, a+1)`. -/
private theorem exists_dzterm_bound (ha : 0 < a) (lam : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ (k : ℕ) (x : ℝ), x ∈ Ioo (a / 2) (a + 1) →
      ‖-realDigamma (x + (k : ℝ)) * zterm x lam k‖ ≤ u k := by
  have h₀ : 0 < a / 2 := by linarith
  have hle : a / 2 ≤ a + 1 := by linarith
  obtain ⟨K, hK, hKle⟩ := exists_inv_Gamma_bound h₀ hle
  set C : ℝ := |realDigamma (a / 2)| + |realDigamma (a + 1)| with hC
  have hC0 : 0 ≤ C := by positivity
  set D : ℝ := K / min (a / 2) 1 with hD
  have hmin0 : 0 < min (a / 2) 1 := lt_min h₀ one_pos
  have hD0 : 0 < D := div_pos hK hmin0
  set u : ℕ → ℝ := fun k => (C + 1 / (a / 2)) * D * ((2 * |lam|) ^ k / (Nat.factorial k : ℝ))
    with hu_def
  have hu : Summable u :=
    (Real.summable_pow_div_factorial (2 * |lam|)).mul_left _
  have hbound : ∀ (k : ℕ) (x : ℝ), x ∈ Ioo (a / 2) (a + 1) →
      ‖-realDigamma (x + (k : ℝ)) * zterm x lam k‖ ≤ u k := by
    intro k x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hxpos : 0 < x := lt_trans h₀ hx0
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hxk : 0 < x + (k : ℝ) := by linarith
    -- the digamma factor
    have hpsi : |realDigamma (x + (k : ℝ))| ≤ C + (k : ℝ) / (a / 2) :=
      abs_realDigamma_add_nat_le h₀ ⟨hx0.le, hx1.le⟩ k
    -- the reciprocal-gamma factor
    have hinvG : (Real.Gamma (x + (k : ℝ)))⁻¹ ≤ D := by
      rw [hD]; exact inv_Gamma_add_nat_le h₀ hx0 (hKle x ⟨hx0.le, hx1.le⟩) k
    have hzabs : ‖zterm x lam k‖ ≤ D * (|lam| ^ k / (Nat.factorial k : ℝ)) :=
      norm_zterm_le hxpos k hinvG
    -- assemble
    have hk2 : (k : ℝ) ≤ 2 ^ k := by
      exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    calc ‖-realDigamma (x + (k : ℝ)) * zterm x lam k‖
        = |realDigamma (x + (k : ℝ))| * ‖zterm x lam k‖ := by
          rw [norm_mul, norm_neg, Real.norm_eq_abs]
      _ ≤ (C + (k : ℝ) / (a / 2)) * (D * (|lam| ^ k / (Nat.factorial k : ℝ))) := by
          apply mul_le_mul hpsi hzabs (norm_nonneg _)
          have : (0 : ℝ) ≤ (k : ℝ) / (a / 2) := by positivity
          linarith
      _ ≤ (C + 1 / (a / 2)) * D * ((2 * |lam|) ^ k / (Nat.factorial k : ℝ)) := by
          have hpow : (2 * |lam|) ^ k = 2 ^ k * |lam| ^ k := by rw [mul_pow]
          have hfac : (C + (k : ℝ) / (a / 2)) ≤ (C + 1 / (a / 2)) * 2 ^ k := by
            have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
            have : (k : ℝ) / (a / 2) ≤ (1 / (a / 2)) * 2 ^ k := by
              rw [div_eq_mul_inv, one_div, mul_comm]
              exact mul_le_mul_of_nonneg_left hk2 (by positivity)
            nlinarith [hC0]
          rw [hpow]
          have hrest : (0 : ℝ) ≤ D * (|lam| ^ k / (Nat.factorial k : ℝ)) := by positivity
          calc (C + (k : ℝ) / (a / 2)) * (D * (|lam| ^ k / (Nat.factorial k : ℝ)))
              ≤ ((C + 1 / (a / 2)) * 2 ^ k) * (D * (|lam| ^ k / (Nat.factorial k : ℝ))) :=
                mul_le_mul_of_nonneg_right hfac hrest
            _ = (C + 1 / (a / 2)) * D * (2 ^ k * |lam| ^ k / (Nat.factorial k : ℝ)) := by ring
  exact ⟨u, hu, hbound⟩

/-- **`∂_a Z(a,λ)` is the termwise derivative** (`eq:Zdef`, the parameter half of
`thm:coefficients`).  The `a`-derivative of the reciprocal-gamma series may be taken
under the sum: `∂_a Z(a,λ) = -∑_k ψ(a+k) λ^k/(k!Γ(a+k))`.  The domination is uniform on
`(a/2, a+1)`, which is all the paper's local statements need. -/
theorem hasDerivAt_Zfun_param (ha : 0 < a) (lam : ℝ) :
    HasDerivAt (fun x : ℝ => Zfun x lam)
      (∑' k : ℕ, -realDigamma (a + (k : ℝ)) * zterm a lam k) a := by
  have h₀ : 0 < a / 2 := by linarith
  have hmem : a ∈ Ioo (a / 2) (a + 1) := ⟨by linarith, by linarith⟩
  obtain ⟨u, hu, hbound⟩ := exists_dzterm_bound ha lam
  have := hasDerivAt_tsum_of_isPreconnected (u := u) (g := fun k x => zterm x lam k)
    (g' := fun k x => -realDigamma (x + (k : ℝ)) * zterm x lam k) (t := Ioo (a / 2) (a + 1))
    (y₀ := a) (y := a) hu isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun k x hx => hasDerivAt_zterm (lt_trans h₀ hx.1) lam k) hbound hmem
    (summable_zterm ha lam) hmem
  simpa [Zfun] using this

/-- The termwise `a`-derivative of `Z` is summable. -/
theorem summable_dzterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k : ℕ => -realDigamma (a + (k : ℝ)) * zterm a lam k) := by
  obtain ⟨u, hu, hbound⟩ := exists_dzterm_bound ha lam
  exact Summable.of_norm_bounded hu (fun k => hbound k a ⟨by linarith, by linarith⟩)


/-- The derivative form of `hasDerivAt_Zfun_param`. -/
theorem deriv_Zfun_param (ha : 0 < a) (lam : ℝ) :
    deriv (fun x : ℝ => Zfun x lam) a
      = ∑' k : ℕ, -realDigamma (a + (k : ℝ)) * zterm a lam k :=
  (hasDerivAt_Zfun_param ha lam).deriv

/-! ### The regularized digamma series -/

/-- The regularized series `∑_{n≥0} (1/(n+1) - 1/(y+n))`, which is `ψ(y) + γ`.  It is
introduced only to carry the trigamma derivative and the digamma recurrence at once. -/
noncomputable def digammaSeries (y : ℝ) : ℝ := ∑' n : ℕ, (((n : ℝ) + 1)⁻¹ - (y + (n : ℝ))⁻¹)

theorem summable_digammaTerm (hy : 0 < y) :
    Summable (fun n : ℕ => ((n : ℝ) + 1)⁻¹ - (y + (n : ℝ))⁻¹) := by
  have hm : 0 < min y 1 := lt_min hy one_pos
  refine Summable.of_norm_bounded (g := fun n : ℕ => |y - 1| * (min y 1 + (n : ℝ))⁻¹ ^ 2)
    ((trigamma_summable hm).mul_left _) (fun n => ?_)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h2 : (0 : ℝ) < y + (n : ℝ) := by linarith
  have hmn : (0 : ℝ) < min y 1 + (n : ℝ) := by linarith
  have hmy : min y 1 ≤ y := min_le_left _ _
  have hm1 : min y 1 ≤ 1 := min_le_right _ _
  have hkey : ‖((n : ℝ) + 1)⁻¹ - (y + (n : ℝ))⁻¹‖
      = |y - 1| / (((n : ℝ) + 1) * (y + (n : ℝ))) := by
    rw [Real.norm_eq_abs, inv_sub_inv h1.ne' h2.ne', abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) * (y + (n : ℝ)))]
    congr 1
    rw [show y + (n : ℝ) - ((n : ℝ) + 1) = y - 1 by ring]
  change ‖((n : ℝ) + 1)⁻¹ - (y + (n : ℝ))⁻¹‖ ≤ |y - 1| * (min y 1 + (n : ℝ))⁻¹ ^ 2
  rw [hkey, div_le_iff₀ (by positivity)]
  have hge : (1 : ℝ) ≤ (min y 1 + (n : ℝ))⁻¹ ^ 2 * (((n : ℝ) + 1) * (y + (n : ℝ))) := by
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    nlinarith
  calc |y - 1| = |y - 1| * 1 := (mul_one _).symm
    _ ≤ |y - 1| * ((min y 1 + (n : ℝ))⁻¹ ^ 2 * (((n : ℝ) + 1) * (y + (n : ℝ)))) :=
        mul_le_mul_of_nonneg_left hge (abs_nonneg _)
    _ = |y - 1| * (min y 1 + (n : ℝ))⁻¹ ^ 2 * (((n : ℝ) + 1) * (y + (n : ℝ))) := by ring

/-- **`ψ` and the regularized series differ by a constant: the derivative is `trigamma`.**
Termwise differentiation of `digammaSeries`, dominated on a compact interval. -/
theorem hasDerivAt_digammaSeries (hy : 0 < y) :
    HasDerivAt digammaSeries (trigamma y) y := by
  set b₀ : ℝ := min y 1 / 2 with hb₀
  set b₁ : ℝ := max y 1 + 1 with hb₁
  have hm : 0 < min y 1 := lt_min hy one_pos
  have h₀ : 0 < b₀ := by rw [hb₀]; linarith
  have hy₁ : y ≤ max y 1 := le_max_left _ _
  have h1₁ : (1 : ℝ) ≤ max y 1 := le_max_right _ _
  have hmy : min y 1 ≤ y := min_le_left _ _
  have hm1 : min y 1 ≤ 1 := min_le_right _ _
  have hmemy : y ∈ Ioo b₀ b₁ := ⟨by rw [hb₀]; linarith, by rw [hb₁]; linarith⟩
  have hmem1 : (1 : ℝ) ∈ Ioo b₀ b₁ := ⟨by rw [hb₀]; linarith, by rw [hb₁]; linarith⟩
  have hterm : ∀ (n : ℕ) (x : ℝ), x ∈ Ioo b₀ b₁ →
      HasDerivAt (fun z : ℝ => ((n : ℝ) + 1)⁻¹ - (z + (n : ℝ))⁻¹) ((x + (n : ℝ))⁻¹ ^ 2) x := by
    intro n x hx
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hxn : (0 : ℝ) < x + (n : ℝ) := by have := hx.1; rw [hb₀] at this; linarith
    have hne : x + (n : ℝ) ≠ 0 := hxn.ne'
    have hinv := (((hasDerivAt_id x).add_const (n : ℝ)).inv hne)
    refine (hinv.const_sub (((n : ℝ) + 1)⁻¹)).congr_deriv ?_
    simp only [id_eq, inv_pow]
    field_simp
  have hbound : ∀ (n : ℕ) (x : ℝ), x ∈ Ioo b₀ b₁ →
      ‖(x + (n : ℝ))⁻¹ ^ 2‖ ≤ (b₀ + (n : ℝ))⁻¹ ^ 2 := by
    intro n x hx
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hb : (0 : ℝ) < b₀ + (n : ℝ) := by linarith
    have hxn : b₀ + (n : ℝ) ≤ x + (n : ℝ) := by have := hx.1.le; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow, inv_pow]
    exact inv_anti₀ (by positivity) (by nlinarith)
  have hzero : Summable (fun n : ℕ => ((n : ℝ) + 1)⁻¹ - ((1 : ℝ) + (n : ℝ))⁻¹) := by
    refine summable_zero.congr (fun n => ?_)
    rw [show (1 : ℝ) + (n : ℝ) = (n : ℝ) + 1 by ring, sub_self]
  have key := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => (b₀ + (n : ℝ))⁻¹ ^ 2)
    (g := fun n x => ((n : ℝ) + 1)⁻¹ - (x + (n : ℝ))⁻¹)
    (g' := fun n x => (x + (n : ℝ))⁻¹ ^ 2) (t := Ioo b₀ b₁) (y₀ := 1) (y := y)
    (trigamma_summable h₀) isOpen_Ioo (convex_Ioo _ _).isPreconnected hterm hbound hmem1
    hzero hmemy
  simpa [digammaSeries, trigamma] using key

/-- `digammaSeries` satisfies the digamma recurrence. -/
theorem digammaSeries_add_one (hy : 0 < y) :
    digammaSeries (y + 1) = digammaSeries y + 1 / y := by
  have h1 : HasSum (fun n : ℕ => ((n : ℝ) + 1)⁻¹ - (y + 1 + (n : ℝ))⁻¹) (digammaSeries (y + 1)) :=
    (summable_digammaTerm (by linarith : (0 : ℝ) < y + 1)).hasSum
  have h2 : HasSum (fun n : ℕ => ((n : ℝ) + 1)⁻¹ - (y + (n : ℝ))⁻¹) (digammaSeries y) :=
    (summable_digammaTerm hy).hasSum
  have hsub := h1.sub h2
  have hcongr : (fun n : ℕ => (((n : ℝ) + 1)⁻¹ - (y + 1 + (n : ℝ))⁻¹)
      - (((n : ℝ) + 1)⁻¹ - (y + (n : ℝ))⁻¹))
      = fun n : ℕ => (y + (n : ℝ))⁻¹ - (y + (n : ℝ) + 1)⁻¹ := by
    funext n
    rw [show y + 1 + (n : ℝ) = y + (n : ℝ) + 1 by ring]
    ring
  rw [hcongr] at hsub
  have := hsub.unique (telescope_hasSum hy)
  rw [one_div]
  linarith

/-! ### `ψ' = ψ₁`: the trigamma connection -/

theorem hasDerivAt_realDigamma' (hy : 0 < y) :
    HasDerivAt realDigamma (deriv realDigamma y) y :=
  (differentiableAt_realDigamma hy).hasDerivAt

/-- `ψ' ≥ 0` on `(0,∞)`: `ψ` is monotone there. -/
theorem deriv_realDigamma_nonneg (hy : 0 < y) : 0 ≤ deriv realDigamma y := by
  have hd := hasDerivAt_realDigamma' hy
  rw [hasDerivAt_iff_tendsto_slope] at hd
  refine ge_of_tendsto hd ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hy), self_mem_nhdsWithin] with z hz hzne
  have hzne' : z ≠ y := hzne
  have hz0 : 0 < z := hz
  rw [slope_def_field]
  rcases lt_or_gt_of_ne hzne' with h | h
  · have h1 : realDigamma z ≤ realDigamma y :=
      realDigamma_monotoneOn (mem_Ioi.2 hz0) (mem_Ioi.2 hy) h.le
    rw [div_nonneg_iff]
    exact Or.inr ⟨by linarith, by linarith⟩
  · have h1 : realDigamma y ≤ realDigamma z :=
      realDigamma_monotoneOn (mem_Ioi.2 hy) (mem_Ioi.2 hz0) h.le
    exact div_nonneg (by linarith) (by linarith)

/-- The trigamma recurrence for `ψ'`, obtained by differentiating `ψ(y+1) = ψ(y)+1/y`. -/
theorem deriv_realDigamma_add_one (hy : 0 < y) :
    deriv realDigamma y = deriv realDigamma (y + 1) + (y⁻¹) ^ 2 := by
  have hy1 : (0 : ℝ) < y + 1 := by linarith
  have hL : HasDerivAt (fun x : ℝ => realDigamma (x + 1)) (deriv realDigamma (y + 1)) y := by
    simpa using (hasDerivAt_realDigamma' hy1).comp y ((hasDerivAt_id y).add_const 1)
  have hR : HasDerivAt (fun x : ℝ => realDigamma x + x⁻¹)
      (deriv realDigamma y + -(y ^ 2)⁻¹) y :=
    (hasDerivAt_realDigamma' hy).add (hasDerivAt_inv hy.ne')
  have heq : (fun x : ℝ => realDigamma (x + 1)) =ᶠ[𝓝 y] fun x : ℝ => realDigamma x + x⁻¹ := by
    filter_upwards [eventually_gt_nhds hy] with x hx
    rw [realDigamma_add_one hx, one_div]
  have hu := (hR.congr_of_eventuallyEq heq).unique hL
  rw [inv_pow]
  linarith

/-- The partial sums of the trigamma series are all below `ψ'`. -/
private theorem partial_le_deriv_realDigamma (hy : 0 < y) (N : ℕ) :
    ∑ n ∈ Finset.range N, (y + (n : ℝ))⁻¹ ^ 2 ≤ deriv realDigamma y := by
  have key : ∀ M : ℕ, deriv realDigamma y
      = (∑ n ∈ Finset.range M, (y + (n : ℝ))⁻¹ ^ 2) + deriv realDigamma (y + (M : ℝ)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        have hyM : 0 < y + (M : ℝ) := by
          have := Nat.cast_nonneg (α := ℝ) M; linarith
        rw [ih, Finset.sum_range_succ, deriv_realDigamma_add_one hyM,
          show y + ((M + 1 : ℕ) : ℝ) = y + (M : ℝ) + 1 by push_cast; ring]
        ring
  have hyN : 0 < y + (N : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) N; linarith
  have := deriv_realDigamma_nonneg hyN
  rw [key N]; linarith

/-- `ψ₁ ≤ ψ'` on `(0,∞)`. -/
theorem trigamma_le_deriv_realDigamma (hy : 0 < y) :
    trigamma y ≤ deriv realDigamma y :=
  le_of_tendsto (trigamma_summable hy).hasSum.tendsto_sum_nat
    (Eventually.of_forall fun N => partial_le_deriv_realDigamma hy N)

/-- The gap `ψ - (ψ + γ)`: periodic by the shared recurrence, monotone by `ψ₁ ≤ ψ'`. -/
private noncomputable def digammaGap (y : ℝ) : ℝ := realDigamma y - digammaSeries y

private theorem hasDerivAt_digammaGap (hy : 0 < y) :
    HasDerivAt digammaGap (deriv realDigamma y - trigamma y) y :=
  (hasDerivAt_realDigamma' hy).sub (hasDerivAt_digammaSeries hy)

private theorem deriv_digammaGap (hy : 0 < y) :
    deriv digammaGap y = deriv realDigamma y - trigamma y := (hasDerivAt_digammaGap hy).deriv

private theorem digammaGap_add_one (hy : 0 < y) :
    digammaGap (y + 1) = digammaGap y := by
  rw [digammaGap, digammaGap, realDigamma_add_one hy, digammaSeries_add_one hy]; ring

private theorem digammaGap_add_nat (hy : 0 < y) (N : ℕ) :
    digammaGap (y + (N : ℝ)) = digammaGap y := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hyN : 0 < y + (N : ℝ) := by
        have := Nat.cast_nonneg (α := ℝ) N; linarith
      rw [show y + ((N + 1 : ℕ) : ℝ) = y + (N : ℝ) + 1 by push_cast; ring,
        digammaGap_add_one hyN, ih]

private theorem digammaGap_monotoneOn : MonotoneOn digammaGap (Ioi (0 : ℝ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ?_)
  · exact (hasDerivAt_digammaGap hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi] at hx
    exact (hasDerivAt_digammaGap hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi] at hx
    rw [deriv_digammaGap hx]
    linarith [trigamma_le_deriv_realDigamma hx]

/-- A monotone function of period `1` on `(0,∞)` is constant. -/
private theorem digammaGap_eq_of_le {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    digammaGap y = digammaGap z := by
  obtain ⟨N, hN⟩ := exists_nat_ge (z - y)
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  have hyN : 0 < y + (N : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) N; linarith
  have h1 : digammaGap y ≤ digammaGap z :=
    digammaGap_monotoneOn (mem_Ioi.2 hy) (mem_Ioi.2 hz) hyz
  have h2 : digammaGap z ≤ digammaGap (y + (N : ℝ)) :=
    digammaGap_monotoneOn (mem_Ioi.2 hz) (mem_Ioi.2 hyN) (by linarith)
  rw [digammaGap_add_nat hy N] at h2
  linarith

/-- **`ψ'(y) = ψ₁(y)` for `y > 0`.**  The from-scratch trigamma of `Trigamma` is the
derivative of the digamma function: `ψ` and the regularized series `∑(1/(n+1)-1/(y+n))`
satisfy the same recurrence, so their difference has period `1`; it is monotone because
`ψ' ≥ ψ₁` termwise, and a monotone function of period `1` is constant. -/
theorem deriv_realDigamma_eq_trigamma (hy : 0 < y) :
    deriv realDigamma y = trigamma y := by
  have hconst : digammaGap =ᶠ[𝓝 y] fun _ => digammaGap y := by
    filter_upwards [eventually_gt_nhds hy] with x hx
    rcases le_total y x with h | h
    · exact (digammaGap_eq_of_le hy h).symm
    · exact digammaGap_eq_of_le hx h
  have hd : deriv digammaGap y = 0 := by rw [hconst.deriv_eq]; simp
  rw [deriv_digammaGap hy] at hd
  linarith

/-- **`(Complex.digamma)' = ψ₁` on the positive reals.**  This is the statement that ties
Mathlib's `digamma` to the `trigamma` of `Trigamma`, on which `lem:trigamma-bounds` and the
normalization `turanCoeffFactor` of the paper depend. -/
theorem deriv_digamma_ofReal (hy : 0 < y) :
    deriv Complex.digamma (y : ℂ) = ((trigamma y : ℝ) : ℂ) := by
  have hC : HasDerivAt Complex.digamma (deriv Complex.digamma (y : ℂ)) (y : ℂ) :=
    (differentiableAt_complex_digamma (by simpa using hy)).hasDerivAt
  have h1 : HasDerivAt (fun x : ℝ => Complex.digamma (x : ℂ))
      (deriv Complex.digamma (y : ℂ)) y := hC.comp_ofReal
  have h2 : HasDerivAt (fun x : ℝ => ((realDigamma x : ℝ) : ℂ)) ((trigamma y : ℝ) : ℂ) y :=
    ((hasDerivAt_realDigamma' hy).congr_deriv (deriv_realDigamma_eq_trigamma hy)).ofReal_comp
  refine h1.unique (h2.congr_of_eventuallyEq ?_)
  filter_upwards [eventually_gt_nhds hy] with x hx
  rw [digamma_ofReal hx]

/-- `ψ(1) = -γ`, transported from `Complex.digamma_one`. -/
theorem realDigamma_one : realDigamma 1 = -Real.eulerMascheroniConstant := by
  have h := digamma_ofReal (y := 1) one_pos
  rw [Complex.ofReal_one, Complex.digamma_one] at h
  exact_mod_cast h.symm

/-- The regularized series vanishes at `y = 1`: every term is `1/(n+1) - 1/(1+n)`. -/
theorem digammaSeries_one : digammaSeries 1 = 0 := by
  rw [digammaSeries, tsum_congr (fun n : ℕ => ?_), tsum_zero]
  rw [show (1 : ℝ) + (n : ℝ) = (n : ℝ) + 1 by ring, sub_self]

/-- **Gauss's series for the digamma function**: `ψ(y) = -γ + ∑_{n≥0}(1/(n+1) - 1/(y+n))`
for `y > 0`.  The gap is constant by `deriv_realDigamma_eq_trigamma`'s argument and is
evaluated at `y = 1`, where the series vanishes and `ψ(1) = -γ`. -/
theorem realDigamma_eq_gauss (hy : 0 < y) :
    realDigamma y = -Real.eulerMascheroniConstant + digammaSeries y := by
  have hgap : digammaGap y = digammaGap 1 := by
    rcases le_total y 1 with h | h
    · exact digammaGap_eq_of_le hy h
    · exact (digammaGap_eq_of_le one_pos h).symm
  rw [digammaGap, digammaGap, realDigamma_one, digammaSeries_one] at hgap
  linarith

/-! ### The second parameter derivative -/

/-- `ψ₁` is antitone on `(0,∞)`: every term of `∑(y+n)⁻²` decreases in `y`. -/
theorem trigamma_anti {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) : trigamma z ≤ trigamma y := by
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  refine Summable.tsum_le_tsum (fun n => ?_) (trigamma_summable hz) (trigamma_summable hy)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hyn : (0 : ℝ) < y + (n : ℝ) := by linarith
  rw [inv_pow, inv_pow]
  exact inv_anti₀ (pow_pos hyn 2) (by nlinarith)

/-- **`∂_a²` of the `k`-th term of `Z`.**  `∂_a²[λ^k/(k!Γ(a+k))] = (ψ(a+k)² -
ψ₁(a+k))·λ^k/(k!Γ(a+k))`. -/
theorem hasDerivAt_dzterm (ha : 0 < a) (lam : ℝ) (k : ℕ) :
    HasDerivAt (fun x : ℝ => -realDigamma (x + (k : ℝ)) * zterm x lam k)
      ((realDigamma (a + (k : ℝ)) ^ 2 - trigamma (a + (k : ℝ))) * zterm a lam k) a := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hak : 0 < a + (k : ℝ) := by linarith
  have hpsi : HasDerivAt (fun x : ℝ => realDigamma (x + (k : ℝ))) (trigamma (a + (k : ℝ))) a := by
    rw [← deriv_realDigamma_eq_trigamma hak]
    simpa using (hasDerivAt_realDigamma' hak).comp a ((hasDerivAt_id a).add_const (k : ℝ))
  refine (hpsi.neg.mul (hasDerivAt_zterm ha lam k)).congr_deriv ?_
  simp only [Pi.neg_apply]
  ring

/-- A summable majorant for the second termwise `a`-derivative, uniform on `(a/2, a+1)`. -/
private theorem exists_ddzterm_bound (ha : 0 < a) (lam : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ (k : ℕ) (x : ℝ), x ∈ Ioo (a / 2) (a + 1) →
      ‖(realDigamma (x + (k : ℝ)) ^ 2 - trigamma (x + (k : ℝ))) * zterm x lam k‖ ≤ u k := by
  have h₀ : 0 < a / 2 := by linarith
  have hle : a / 2 ≤ a + 1 := by linarith
  obtain ⟨K, hK, hKle⟩ := exists_inv_Gamma_bound h₀ hle
  set C : ℝ := |realDigamma (a / 2)| + |realDigamma (a + 1)| with hC
  have hC0 : 0 ≤ C := by positivity
  set T : ℝ := trigamma (a / 2) with hT
  have hT0 : 0 ≤ T := (trigamma_pos h₀).le
  set D : ℝ := K / min (a / 2) 1 with hD
  have hmin0 : 0 < min (a / 2) 1 := lt_min h₀ one_pos
  have hD0 : 0 < D := div_pos hK hmin0
  set u : ℕ → ℝ :=
    fun k => ((C + 1 / (a / 2)) ^ 2 + T) * D * ((4 * |lam|) ^ k / (Nat.factorial k : ℝ))
    with hu_def
  have hu : Summable u := (Real.summable_pow_div_factorial (4 * |lam|)).mul_left _
  have hbound : ∀ (k : ℕ) (x : ℝ), x ∈ Ioo (a / 2) (a + 1) →
      ‖(realDigamma (x + (k : ℝ)) ^ 2 - trigamma (x + (k : ℝ))) * zterm x lam k‖ ≤ u k := by
    intro k x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hxpos : 0 < x := lt_trans h₀ hx0
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hxk : 0 < x + (k : ℝ) := by linarith
    have hnn : (0 : ℝ) ≤ C + (k : ℝ) / (a / 2) := by positivity
    have hpsi : |realDigamma (x + (k : ℝ))| ≤ C + (k : ℝ) / (a / 2) :=
      abs_realDigamma_add_nat_le h₀ ⟨hx0.le, hx1.le⟩ k
    have htri : trigamma (x + (k : ℝ)) ≤ T := trigamma_anti h₀ (by linarith)
    have htri0 : 0 ≤ trigamma (x + (k : ℝ)) := (trigamma_pos hxk).le
    have hsq : realDigamma (x + (k : ℝ)) ^ 2 ≤ (C + (k : ℝ) / (a / 2)) ^ 2 := by
      rw [← sq_abs (realDigamma (x + (k : ℝ)))]
      exact pow_le_pow_left₀ (abs_nonneg _) hpsi 2
    have hpar : |realDigamma (x + (k : ℝ)) ^ 2 - trigamma (x + (k : ℝ))|
        ≤ (C + (k : ℝ) / (a / 2)) ^ 2 + T := by
      rw [abs_le]
      exact ⟨by linarith [sq_nonneg (realDigamma (x + (k : ℝ))),
        sq_nonneg (C + (k : ℝ) / (a / 2))], by linarith⟩
    have hinvG : (Real.Gamma (x + (k : ℝ)))⁻¹ ≤ D := by
      rw [hD]; exact inv_Gamma_add_nat_le h₀ hx0 (hKle x ⟨hx0.le, hx1.le⟩) k
    have hzabs : ‖zterm x lam k‖ ≤ D * (|lam| ^ k / (Nat.factorial k : ℝ)) :=
      norm_zterm_le hxpos k hinvG
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h4k : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have h4 : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
    have hk2 : (k : ℝ) ≤ 2 ^ k := by
      have : (k : ℕ) ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
      exact_mod_cast this
    have hfac : (C + (k : ℝ) / (a / 2)) ≤ (C + 1 / (a / 2)) * 2 ^ k := by
      have hCle : C ≤ C * 2 ^ k := le_mul_of_one_le_right hC0 h2k
      have hdle : (k : ℝ) / (a / 2) ≤ 1 / (a / 2) * 2 ^ k := by
        rw [div_eq_mul_inv, one_div, mul_comm]
        exact mul_le_mul_of_nonneg_left hk2 (by positivity)
      have hexp : (C + 1 / (a / 2)) * 2 ^ k = C * 2 ^ k + 1 / (a / 2) * 2 ^ k := by ring
      rw [hexp]; linarith
    have hfac2 : (C + (k : ℝ) / (a / 2)) ^ 2 + T ≤ ((C + 1 / (a / 2)) ^ 2 + T) * 4 ^ k := by
      have hsq2 : (C + (k : ℝ) / (a / 2)) ^ 2 ≤ (C + 1 / (a / 2)) ^ 2 * 4 ^ k := by
        calc (C + (k : ℝ) / (a / 2)) ^ 2 ≤ ((C + 1 / (a / 2)) * 2 ^ k) ^ 2 :=
              pow_le_pow_left₀ hnn hfac 2
          _ = (C + 1 / (a / 2)) ^ 2 * 4 ^ k := by rw [mul_pow, h4]
      have hTle : T ≤ T * 4 ^ k := le_mul_of_one_le_right hT0 h4k
      have hexp : ((C + 1 / (a / 2)) ^ 2 + T) * 4 ^ k
          = (C + 1 / (a / 2)) ^ 2 * 4 ^ k + T * 4 ^ k := by ring
      rw [hexp]; linarith
    calc ‖(realDigamma (x + (k : ℝ)) ^ 2 - trigamma (x + (k : ℝ))) * zterm x lam k‖
        = |realDigamma (x + (k : ℝ)) ^ 2 - trigamma (x + (k : ℝ))| * ‖zterm x lam k‖ := by
          rw [norm_mul, Real.norm_eq_abs]
      _ ≤ ((C + (k : ℝ) / (a / 2)) ^ 2 + T) * (D * (|lam| ^ k / (Nat.factorial k : ℝ))) := by
          refine mul_le_mul hpar hzabs (norm_nonneg _) (by positivity)
      _ ≤ (((C + 1 / (a / 2)) ^ 2 + T) * 4 ^ k) * (D * (|lam| ^ k / (Nat.factorial k : ℝ))) :=
          mul_le_mul_of_nonneg_right hfac2 (by positivity)
      _ = ((C + 1 / (a / 2)) ^ 2 + T) * D * ((4 * |lam|) ^ k / (Nat.factorial k : ℝ)) := by
          rw [mul_pow]; ring
  exact ⟨u, hu, hbound⟩

/-- **`∂_a² Z(a,λ)` is the termwise second derivative.**  This is the input to
`eq:A-second-delta` of `sec:coefficients`: `A = Z Z_aa - Z_a²` is assembled from these two series.
-/
theorem hasDerivAt_deriv_Zfun_param (ha : 0 < a) (lam : ℝ) :
    HasDerivAt (fun x : ℝ => ∑' k : ℕ, -realDigamma (x + (k : ℝ)) * zterm x lam k)
      (∑' k : ℕ, (realDigamma (a + (k : ℝ)) ^ 2 - trigamma (a + (k : ℝ))) * zterm a lam k) a := by
  have h₀ : 0 < a / 2 := by linarith
  have hmem : a ∈ Ioo (a / 2) (a + 1) := ⟨by linarith, by linarith⟩
  obtain ⟨u, hu, hbound⟩ := exists_ddzterm_bound ha lam
  exact hasDerivAt_tsum_of_isPreconnected (u := u)
    (g := fun k x => -realDigamma (x + (k : ℝ)) * zterm x lam k)
    (g' := fun k x => (realDigamma (x + (k : ℝ)) ^ 2 - trigamma (x + (k : ℝ))) * zterm x lam k)
    (t := Ioo (a / 2) (a + 1)) (y₀ := a) (y := a) hu isOpen_Ioo
    (convex_Ioo _ _).isPreconnected
    (fun k x hx => hasDerivAt_dzterm (lt_trans h₀ hx.1) lam k) hbound hmem
    (summable_dzterm ha lam) hmem

/-- `∂_a² Z(a,λ) = ∑_k (ψ(a+k)² - ψ₁(a+k)) λ^k/(k!Γ(a+k))`, as an iterated `deriv`. -/
theorem hasDerivAt_deriv_Zfun (ha : 0 < a) (lam : ℝ) :
    HasDerivAt (deriv fun x : ℝ => Zfun x lam)
      (∑' k : ℕ, (realDigamma (a + (k : ℝ)) ^ 2 - trigamma (a + (k : ℝ))) * zterm a lam k) a := by
  refine (hasDerivAt_deriv_Zfun_param ha lam).congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds ha] with x hx
  exact deriv_Zfun_param hx lam

theorem deriv_deriv_Zfun_param (ha : 0 < a) (lam : ℝ) :
    deriv (deriv fun x : ℝ => Zfun x lam) a
      = ∑' k : ℕ, (realDigamma (a + (k : ℝ)) ^ 2 - trigamma (a + (k : ℝ))) * zterm a lam k :=
  (hasDerivAt_deriv_Zfun ha lam).deriv

/-! ### The `δ`-deformation of the convolution weight (`eq:F-second-delta`) -/

/-- `δ ↦ [Γ(y+δ)Γ(y-δ)]⁻¹`, the `δ`-deformed weight of `eq:Fdelta`. -/
noncomputable def gammaPairInv (y d : ℝ) : ℝ := (Real.Gamma (y + d) * Real.Gamma (y - d))⁻¹

theorem hasDerivAt_gammaPairInv {y d : ℝ} (h₁ : 0 < y + d) (h₂ : 0 < y - d) :
    HasDerivAt (gammaPairInv y)
      ((-realDigamma (y + d) + realDigamma (y - d)) * gammaPairInv y d) d := by
  have hG1 : Real.Gamma (y + d) ≠ 0 := (Real.Gamma_pos_of_pos h₁).ne'
  have hG2 : Real.Gamma (y - d) ≠ 0 := (Real.Gamma_pos_of_pos h₂).ne'
  have hu : HasDerivAt (fun e : ℝ => (Real.Gamma (y + e))⁻¹)
      (-realDigamma (y + d) / Real.Gamma (y + d)) d := by
    simpa using (hasDerivAt_inv_Gamma h₁).comp d ((hasDerivAt_id d).const_add y)
  have hv : HasDerivAt (fun e : ℝ => (Real.Gamma (y - e))⁻¹)
      (realDigamma (y - d) / Real.Gamma (y - d)) d := by
    have hcomp := (hasDerivAt_inv_Gamma h₂).comp d ((hasDerivAt_id d).const_sub y)
    simp only [Function.comp_def] at hcomp
    refine hcomp.congr_deriv ?_
    field_simp
  have hmul := hu.mul hv
  have hfun : gammaPairInv y
      =ᶠ[𝓝 d] ((fun e : ℝ => (Real.Gamma (y + e))⁻¹) * fun e : ℝ => (Real.Gamma (y - e))⁻¹) := by
    filter_upwards with e
    simp [gammaPairInv, Pi.mul_apply, mul_comm]
  refine (hmul.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [gammaPairInv]
  field_simp

/-- **`eq:F-second-delta`.**  `∂_δ²|_0 [Γ(y+δ)Γ(y-δ)]⁻¹ = -2ψ₁(y)/Γ(y)²`: the score
`-ψ(y+δ)+ψ(y-δ)` vanishes at `δ=0`, so only the second log-derivative survives. -/
theorem hasDerivAt_deriv_gammaPairInv (hy : 0 < y) :
    HasDerivAt (deriv (gammaPairInv y)) (-2 * trigamma y / Real.Gamma y ^ 2) 0 := by
  have hG : Real.Gamma y ≠ 0 := (Real.Gamma_pos_of_pos hy).ne'
  have hnbhd : Ioo (-y) y ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hy
  -- the score, and its derivative at `δ = 0`
  have hbase1 : HasDerivAt realDigamma (trigamma y) (y + id (0 : ℝ)) := by
    simp only [id_eq, add_zero]
    rw [← deriv_realDigamma_eq_trigamma hy]
    exact hasDerivAt_realDigamma' hy
  have hs1 : HasDerivAt (fun d : ℝ => realDigamma (y + d)) (trigamma y) 0 := by
    simpa using hbase1.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add y)
  have hbase2 : HasDerivAt realDigamma (trigamma y) (y - id (0 : ℝ)) := by
    simp only [id_eq, sub_zero]
    rw [← deriv_realDigamma_eq_trigamma hy]
    exact hasDerivAt_realDigamma' hy
  have hs2 : HasDerivAt (fun d : ℝ => realDigamma (y - d)) (-trigamma y) 0 := by
    simpa using hbase2.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_sub y)
  have hscore : HasDerivAt (fun d : ℝ => -realDigamma (y + d) + realDigamma (y - d))
      (-2 * trigamma y) 0 := by
    have h := hs1.neg.add hs2
    refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
    filter_upwards with e
    simp
  have hg0 : HasDerivAt (gammaPairInv y)
      ((-realDigamma (y + 0) + realDigamma (y - 0)) * gammaPairInv y 0) 0 :=
    hasDerivAt_gammaPairInv (by linarith) (by linarith)
  have hprod0 := hscore.mul hg0
  have hprod : HasDerivAt
      (fun d : ℝ => (-realDigamma (y + d) + realDigamma (y - d)) * gammaPairInv y d)
      ((-2 * trigamma y) * gammaPairInv y 0
        + (-realDigamma (y + 0) + realDigamma (y - 0))
          * ((-realDigamma (y + 0) + realDigamma (y - 0)) * gammaPairInv y 0)) 0 := by
    refine hprod0.congr_of_eventuallyEq ?_
    filter_upwards with e
    simp [Pi.mul_apply]
  have hval : (-2 * trigamma y) * gammaPairInv y 0
      + (-realDigamma (y + 0) + realDigamma (y - 0))
        * ((-realDigamma (y + 0) + realDigamma (y - 0)) * gammaPairInv y 0)
      = -2 * trigamma y / Real.Gamma y ^ 2 := by
    rw [gammaPairInv]
    simp only [add_zero, sub_zero]
    field
  rw [hval] at hprod
  refine hprod.congr_of_eventuallyEq ?_
  filter_upwards [hnbhd] with d hd
  exact (hasDerivAt_gammaPairInv (by linarith [hd.1]) (by linarith [hd.2])).deriv

theorem deriv_deriv_gammaPairInv (hy : 0 < y) :
    deriv (deriv (gammaPairInv y)) 0 = -2 * trigamma y / Real.Gamma y ^ 2 :=
  (hasDerivAt_deriv_gammaPairInv hy).deriv

/-- **`F_m''(0) = -2 S_m ψ₁(a+m)`** (`eq:F-second-delta`), for the closed form `eq:Fdelta`
`F_m(δ) = (2a+m-1)_m / (m! Γ(a+m+δ)Γ(a+m-δ))` supplied by `lem:convolution`. -/
theorem deriv_deriv_Fdelta (ha : 0 < a) (m : ℕ) :
    deriv (deriv fun d : ℝ =>
        poch (2 * a + (m : ℝ) - 1) m / (Nat.factorial m : ℝ) * gammaPairInv (a + (m : ℝ)) d) 0
      = -2 * (sweight a m * trigamma (a + (m : ℝ))) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have ham : 0 < a + (m : ℝ) := by linarith
  have hG : Real.Gamma (a + (m : ℝ)) ≠ 0 := (Real.Gamma_pos_of_pos ham).ne'
  have hfm : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  set c : ℝ := poch (2 * a + (m : ℝ) - 1) m / (Nat.factorial m : ℝ) with hc
  have hinner : ∀ d : ℝ, -(a + (m : ℝ)) < d → d < a + (m : ℝ) →
      deriv (fun e : ℝ => c * gammaPairInv (a + (m : ℝ)) e) d
        = c * deriv (gammaPairInv (a + (m : ℝ))) d := by
    intro d h1 h2
    have hg := hasDerivAt_gammaPairInv (y := a + (m : ℝ)) (d := d) (by linarith) (by linarith)
    rw [(hg.const_mul c).deriv, hg.deriv]
  have houter : HasDerivAt (fun d : ℝ => c * deriv (gammaPairInv (a + (m : ℝ))) d)
      (c * (-2 * trigamma (a + (m : ℝ)) / Real.Gamma (a + (m : ℝ)) ^ 2)) 0 :=
    (hasDerivAt_deriv_gammaPairInv ham).const_mul c
  have heq : deriv (fun e : ℝ => c * gammaPairInv (a + (m : ℝ)) e)
      =ᶠ[𝓝 (0 : ℝ)] fun d : ℝ => c * deriv (gammaPairInv (a + (m : ℝ))) d := by
    filter_upwards [Ioo_mem_nhds (show -(a + (m : ℝ)) < 0 by linarith) ham] with d hd
    exact hinner d hd.1 hd.2
  rw [(houter.congr_of_eventuallyEq heq).deriv, sweight, hc]
  field_simp

end TuranBessel
