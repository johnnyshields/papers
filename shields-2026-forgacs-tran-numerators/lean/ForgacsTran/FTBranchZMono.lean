/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchProp1
import ForgacsTran.FTBranchCritical
import ForgacsTran.FTBranchPencil
import ForgacsTran.ComplexPart

/-!
# `z(θ)` is strictly monotone

`Forgacs2017RationalDenominator` Lemma 4(ii): the branch value `z(θ; l)` is
strictly monotone across the viewing arc.  This is the hypothesis
`ftProp1_closing` and `FTMinModulus` carry, and it had no supplier.

## Main statements

* `ftSigma` — `Σ(t) = ∑_k t/(τ_k - t) + r`, the bracket of their Eq. (23), and
  `ftSigma_im_neg`: its imaginary part is strictly negative on the lower half
  plane, which is their `-π < Arg(·) < 0` step made explicit.
* `eval_ftCritical_ftRootPoly` — `E(t) = -Σ(t) P(t)`, so `Σ ≠ 0` is what keeps
  the branch point off the critical set.
* `hasDerivAt_ftBranchZ` — the derivative of the branch value, and
  `ftBranchZ_deriv_mul_im` the identity `z'(θ) · Im Σ = -z(θ) |Σ|²` that fixes
  its sign.
* `ftBranchZ_strictMonoOn` — Lemma 4(ii) at even `n + l + 1`.

## Implementation notes

**Differs from the paper's route.**  They differentiate their closed form (21)
logarithmically and eliminate `dτ` through (11), arriving at (23).  Here `z` is
differentiated as a composite instead: `z(θ) = g(t₊(θ))` with `g(t) = -P(t)/t^r`
and `t₊` the branch point, both already differentiable, so the chain rule gives
`z'(θ)` at once.  Their (11)--(12) is an *elimination* of `τ'(θ)`; that step is
replaced here by a fact about the codomain.  Because `z` is real-valued, the
imaginary part of the composite derivative vanishes, and that vanishing **is**
the relation `τ'(θ) Im Σ = τ(θ) Re Σ` between `τ'` and `Σ` that their
computation extracts by hand.  This is a simplification and not a repackaging:
nothing is eliminated, the relation is read off the fact that `z` lands in `ℝ`.
Neither the closed form (21) nor the differentiated branch relation (11) is
used anywhere below.

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

spectral parameter, monotonicity, branch
-/

namespace ForgacsTran

open Real Set Polynomial

/-- `Σ(t) = ∑_k t/(τ_k - t) + r`, the bracket of `Forgacs2017RationalDenominator`
Eq. (23). -/
noncomputable def ftSigma {n : ℕ} (a : Fin n → ℝ) (r : ℕ) (t : ℂ) : ℂ :=
  (∑ k, t / ((a k : ℂ) - t)) + r

theorem ftSigma_im {n : ℕ} (a : Fin n → ℝ) (r : ℕ) {t : ℂ} (_h : ∀ k, ((a k : ℂ)) - t ≠ 0) :
    (ftSigma a r t).im = ∑ k, a k * t.im / Complex.normSq ((a k : ℂ) - t) := by
  simp only [ftSigma, Complex.add_im, Complex.natCast_im, add_zero, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.div_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, zero_sub]
  field

/-- **Their `-π < Arg < 0` step.**  On the lower half plane every summand of `Σ`
has strictly negative imaginary part, so `Σ ≠ 0`. -/
theorem ftSigma_im_neg {n r : ℕ} (hn : 0 < n) {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) {t : ℂ}
    (ht : t.im < 0) : (ftSigma a r t).im < 0 := by
  have hne : ∀ k, ((a k : ℂ)) - t ≠ 0 := by
    intro k hk
    have := congrArg Complex.im hk
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at this
    exact absurd this (ne_of_lt ht)
  rw [ftSigma_im a r hne]
  refine Finset.sum_neg (fun k _ => ?_) (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  have hpos : 0 < Complex.normSq ((a k : ℂ) - t) := Complex.normSq_pos.2 (hne k)
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (ha k) ht) hpos

theorem ftSigma_ne_zero {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) {r : ℕ} {t : ℂ}
    (ht : t.im < 0) : ftSigma a r t ≠ 0 := by
  intro h
  have := ftSigma_im_neg (n := n) (r := r) hn ha ht
  rw [h] at this
  simp at this

/-- **`E(t) = -Σ(t) P(t)`.**  The critical polynomial of `Geometry` factors through
`Σ`, so the branch point avoids the critical set exactly because `Σ ≠ 0` there. -/
theorem eval_ftCritical_ftRootPoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (r : ℕ) {t : ℂ}
    (h : ∀ k, ((a k : ℂ)) - t ≠ 0) :
    (ftCritical (ftRootPoly c a) r).eval t = -(ftSigma a r t) * (ftRootPoly c a).eval t := by
  classical
  have hd : (derivative (ftRootPoly c a)).eval t
      = -((∑ k, 1 / ((a k : ℂ) - t)) * ((c : ℂ) * ∏ k, ((a k : ℂ) - t))) := by
    rw [ftRootPoly, derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C,
      eval_derivative_prod_sub _ (fun k => ((a k : ℝ) : ℂ)) t fun k _ => h k]
    ring
  rw [eval_ftCritical, hd, eval_ftRootPoly, ftSigma]
  have hsum : ∑ k, t / ((a k : ℂ) - t) = t * ∑ k, 1 / ((a k : ℂ) - t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_one_div]
  rw [hsum]
  ring

/-! ### The derivative of the branch value -/

/-- `t₊'(θ)`, from `hasDerivAt_ftBranchPoint`. -/
noncomputable def ftBranchPointDeriv {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℂ :=
  ((ftTauDeriv a r l θ : ℂ) - (ftTau a r l θ : ℂ) * Complex.I)
    * Complex.exp (-(θ : ℂ) * Complex.I)

/-- The branch value as a complex-valued function of `θ`; `ftZFun_eq` identifies it
with the real `ftBranchZ`. -/
noncomputable def ftZFun {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) (θ : ℝ) : ℂ :=
  -((ftRootPoly c a).eval (ftBranchPoint a r l θ)) / (ftBranchPoint a r l θ) ^ r

theorem ftBranchPoint_im {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) :
    (ftBranchPoint a r l θ).im = -(ftTau a r l θ * Real.sin θ) := by
  simp only [ftBranchPoint, ftArcPoint, exp_neg_ofReal_mul_I, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem ftBranchPoint_im_neg {n : ℕ} {a : Fin n → ℝ} {r l : ℕ} {θ : ℝ} (hθ : θ ∈ Ioo 0 π)
    (h : FTBranchAt a r l θ) : (ftBranchPoint a r l θ).im < 0 := by
  rw [ftBranchPoint_im]
  exact neg_neg_of_pos
    (mul_pos (ftTau_pos h) (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2))

theorem ftBranchPoint_ne_zero {n : ℕ} {a : Fin n → ℝ} {r l : ℕ} {θ : ℝ} (hθ : θ ∈ Ioo 0 π)
    (h : FTBranchAt a r l θ) : ftBranchPoint a r l θ ≠ 0 := by
  intro hz
  have := ftBranchPoint_im_neg hθ h
  rw [hz] at this
  simp at this

theorem ftZFun_eq {n r l : ℕ} {a : Fin n → ℝ} (c : ℝ) (ha : ∀ k, 0 < a k) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) (h : FTBranchAt a r l θ) :
    ftZFun a c r l θ = ((ftBranchZ a c r l θ : ℝ) : ℂ) := by
  rw [ftZFun, ftBranchPoint, eval_ftRootPoly]
  exact ftBranch_ftArcPoint_eq_ftBranchZ c ha hθ h

theorem hasDerivAt_ftZFun {n r l : ℕ} {a : Fin n → ℝ} (c : ℝ) (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    HasDerivAt (ftZFun a c r l)
      (-(ftBranchPointDeriv a r l θ₀)
        * (ftCritical (ftRootPoly c a) r).eval (ftBranchPoint a r l θ₀)
        / (ftBranchPoint a r l θ₀) ^ (r + 1)) θ₀ := by
  have hθπ : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hne : ftBranchPoint a r l θ₀ ≠ 0 := ftBranchPoint_ne_zero hθπ (hb θ₀ hθ₀)
  have hW : HasDerivAt (ftBranchPoint a r l) (ftBranchPointDeriv a r l θ₀) θ₀ :=
    hasDerivAt_ftBranchPoint hn ha hr hθ₀ hb
  have hnum : HasDerivAt (fun θ => -((ftRootPoly c a).eval (ftBranchPoint a r l θ)))
      (-((derivative (ftRootPoly c a)).eval (ftBranchPoint a r l θ₀)
        * ftBranchPointDeriv a r l θ₀)) θ₀ :=
    (((ftRootPoly c a).hasDerivAt (ftBranchPoint a r l θ₀)).comp θ₀ hW).neg
  have hden : HasDerivAt (fun θ => (ftBranchPoint a r l θ) ^ r)
      ((r : ℂ) * (ftBranchPoint a r l θ₀) ^ (r - 1) * ftBranchPointDeriv a r l θ₀) θ₀ :=
    (hasDerivAt_pow r (ftBranchPoint a r l θ₀)).comp θ₀ hW
  refine (hnum.div hden (pow_ne_zero _ hne)).congr_deriv ?_
  have hsplit : ∀ x : ℂ, x ^ r = x * x ^ (r - 1) :=
    fun x => (mul_pow_sub_one (by omega) x).symm
  have hsucc : (ftBranchPoint a r l θ₀) ^ (r + 1)
      = (ftBranchPoint a r l θ₀) ^ r * ftBranchPoint a r l θ₀ := pow_succ _ r
  have h1 : ((ftBranchPoint a r l θ₀) ^ r) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hne)
  have h2 : (ftBranchPoint a r l θ₀) ^ r * ftBranchPoint a r l θ₀ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hne) hne
  rw [eval_ftCritical, hsucc, div_eq_div_iff h1 h2, hsplit (ftBranchPoint a r l θ₀)]
  ring

/-! ### The sign of the derivative -/

theorem ftBranchZ_pos {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hpar : Even (n + l + 1)) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (h : FTBranchAt a r l θ) :
    0 < ftBranchZ a c r l θ := by
  rw [ftBranchZ, hpar.neg_one_pow, one_mul]
  have hprod : 0 < ∏ k, ftChord (a k) θ (ftBranchAngle a r l k θ) :=
    Finset.prod_pos fun k _ => ftChord_pos (ha k) hθ (ftAngle_mem_Ioo (ha k) (ftTau_pos h) hθ)
  exact div_pos (mul_pos hc hprod) (pow_pos (ftTau_pos h) r)

/-- `z'(θ)`, in the closed form their Eq. (23) produces. -/
noncomputable def ftBranchZDeriv {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) (θ : ℝ) : ℝ :=
  -(ftBranchZ a c r l θ) * Complex.normSq (ftSigma a r (ftBranchPoint a r l θ))
    / (ftSigma a r (ftBranchPoint a r l θ)).im

/-- **`Forgacs2017RationalDenominator` Eq. (23).**  The derivative of the branch
value is `-z |Σ|² / Im Σ`, so its sign is the sign of `z`. -/
theorem hasDerivAt_ftBranchZ {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) (hz : ftBranchZ a c r l θ₀ ≠ 0) :
    HasDerivAt (ftBranchZ a c r l) (ftBranchZDeriv a c r l θ₀) θ₀ := by
  have hθπ : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hbr := hb θ₀ hθ₀
  have hτ0 : 0 < ftTau a r l θ₀ := ftTau_pos hbr
  have hτne : ((ftTau a r l θ₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hτ0
  have htim : (ftBranchPoint a r l θ₀).im < 0 := ftBranchPoint_im_neg hθπ hbr
  have hAim : (ftSigma a r (ftBranchPoint a r l θ₀)).im < 0 := ftSigma_im_neg hn ha htim
  have hne : ∀ k, ((a k : ℂ)) - ftBranchPoint a r l θ₀ ≠ 0 := by
    intro k hk
    have := congrArg Complex.im hk
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at this
    exact absurd this (ne_of_lt htim)
  have htne : ftBranchPoint a r l θ₀ ≠ 0 := ftBranchPoint_ne_zero hθπ hbr
  -- the complex derivative and its closed form
  have hD := hasDerivAt_ftZFun c hn ha hr hθ₀ hb
  have hQ : (ftRootPoly c a).eval (ftBranchPoint a r l θ₀)
      = -((ftBranchZ a c r l θ₀ : ℝ) : ℂ) * (ftBranchPoint a r l θ₀) ^ r := by
    have h0 := ftZFun_eq c ha hθπ hbr
    rw [ftZFun, div_eq_iff (pow_ne_zero r htne)] at h0
    linear_combination -h0
  have hDval : -(ftBranchPointDeriv a r l θ₀)
        * (ftCritical (ftRootPoly c a) r).eval (ftBranchPoint a r l θ₀)
        / (ftBranchPoint a r l θ₀) ^ (r + 1)
      = -((ftBranchZ a c r l θ₀ : ℝ) : ℂ) * ftSigma a r (ftBranchPoint a r l θ₀)
        * (((ftTauDeriv a r l θ₀ : ℝ) : ℂ) - ((ftTau a r l θ₀ : ℝ) : ℂ) * Complex.I)
        / ((ftTau a r l θ₀ : ℝ) : ℂ) := by
    rw [eval_ftCritical_ftRootPoly c a r hne, hQ, ftBranchPointDeriv]
    have hexp : Complex.exp (-(θ₀ : ℂ) * Complex.I)
        = ftBranchPoint a r l θ₀ / ((ftTau a r l θ₀ : ℝ) : ℂ) := by
      rw [ftBranchPoint, ftArcPoint]
      field_simp
    rw [hexp, pow_succ]
    field_simp
  rw [hDval] at hD
  -- transfer to the real branch value
  have heq : ∀ᶠ θ in nhds θ₀, ((ftBranchZ a c r l θ : ℝ) : ℂ) = ftZFun a c r l θ := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ₀] with θ hθ
    exact (ftZFun_eq c ha (ftArc_subset hr hθ) (hb θ hθ)).symm
  have hDr := hD.congr_of_eventuallyEq heq
  have him : (-((ftBranchZ a c r l θ₀ : ℝ) : ℂ) * ftSigma a r (ftBranchPoint a r l θ₀)
      * (((ftTauDeriv a r l θ₀ : ℝ) : ℂ) - ((ftTau a r l θ₀ : ℝ) : ℂ) * Complex.I)
      / ((ftTau a r l θ₀ : ℝ) : ℂ)).im = 0 := by
    have h1 := hDr.im
    simp only [Complex.ofReal_im] at h1
    exact ((hasDerivAt_const θ₀ (0 : ℝ)).unique h1).symm
  have hre := hDr.re
  simp only [Complex.ofReal_re] at hre
  refine hre.congr_deriv ?_
  -- the algebra of `Eq. (23)`
  set A := ftSigma a r (ftBranchPoint a r l θ₀) with hAdef
  set z := ftBranchZ a c r l θ₀ with hzdef
  set τ := ftTau a r l θ₀ with hτdef
  set τ' := ftTauDeriv a r l θ₀ with hτ'def
  have hτne' : τ ≠ 0 := ne_of_gt hτ0
  have hreim1 : ∀ w : ℂ, (w / ((τ : ℝ) : ℂ)).re = w.re / τ := fun w => by
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply, mul_zero, zero_div,
      add_zero]
    field_simp
  have hreim2 : ∀ w : ℂ, (w / ((τ : ℝ) : ℂ)).im = w.im / τ := fun w => by
    rw [Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply, mul_zero, zero_div,
      sub_zero]
    field
  have hCre : (-(z : ℂ) * A * ((τ' : ℂ) - (τ : ℂ) * Complex.I)).re
      = -z * (A.re * τ' + A.im * τ) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    ring
  have hCim : (-(z : ℂ) * A * ((τ' : ℂ) - (τ : ℂ) * Complex.I)).im
      = -z * (A.im * τ' - A.re * τ) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    ring
  rw [hreim2, hCim] at him
  have hrel : A.im * τ' = A.re * τ := by
    have h2 : -z * (A.im * τ' - A.re * τ) = 0 :=
      (div_eq_zero_iff.1 him).resolve_right hτne'
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (neg_eq_zero.1 h) hz
    · linarith
  rw [ftBranchZDeriv, ← hAdef, ← hzdef, hreim1, hCre, Complex.normSq_apply]
  rw [div_eq_div_iff hτne' (ne_of_lt hAim)]
  linear_combination (-(z * A.re)) * hrel

theorem ftBranchZDeriv_pos {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) (h : FTBranchAt a r l θ)
    (hz : 0 < ftBranchZ a c r l θ) : 0 < ftBranchZDeriv a c r l θ := by
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hAim : (ftSigma a r (ftBranchPoint a r l θ)).im < 0 :=
    ftSigma_im_neg hn ha (ftBranchPoint_im_neg hθπ h)
  have hAne : ftSigma a r (ftBranchPoint a r l θ) ≠ 0 :=
    ftSigma_ne_zero hn ha (ftBranchPoint_im_neg hθπ h)
  have hns : 0 < Complex.normSq (ftSigma a r (ftBranchPoint a r l θ)) :=
    Complex.normSq_pos.2 hAne
  rw [ftBranchZDeriv]
  exact div_pos_of_neg_of_neg (by nlinarith) hAim

/-- **`Forgacs2017RationalDenominator` Lemma 4(ii).**  At even `n + l + 1` — which
is where their Proposition 1 uses it — the branch value is strictly increasing
across the viewing arc. -/
theorem ftBranchZ_strictMonoOn {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hpar : Even (n + l + 1))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    StrictMonoOn (ftBranchZ a c r l) (Ioo 0 (π / r)) := by
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      HasDerivAt (ftBranchZ a c r l) (ftBranchZDeriv a c r l θ) θ := fun θ hθ =>
    hasDerivAt_ftBranchZ hn ha hr hθ hb
      (ne_of_gt (ftBranchZ_pos ha hc hpar (ftArc_subset hr hθ) (hb θ hθ)))
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun θ hθ => ((hderiv θ hθ).continuousAt).continuousWithinAt) fun θ hθ => ?_
  rw [interior_Ioo] at hθ
  rw [(hderiv θ hθ).deriv]
  exact ftBranchZDeriv_pos hn ha hr hθ (hb θ hθ)
    (ftBranchZ_pos ha hc hpar (ftArc_subset hr hθ) (hb θ hθ))

/-- **`ftProp1_closing` with its monotonicity hypothesis discharged.**  Lemma 4(ii)
supplies `hzmono`, so the closing step of `Forgacs2017RationalDenominator`
Proposition 1 needs only the containment and the parity. -/
theorem ftProp1_angle_eq {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (hpar : Even (n + l + 1))
    {θ θ' : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) (hθ' : θ' ∈ Ioo 0 (π / r))
    (hbl : ∀ ψ ∈ Ioo 0 (π / r), FTBranchAt a r l ψ)
    (hlo : ftTau a r l θ' ≤ ftTau a r (n - 1) θ)
    (hhi : ftTau a r (n - 1) θ ≤ ftTau a r l θ)
    (hzeq : ftBranchZ a c r l θ' = ftBranchZ a c r (n - 1) θ) :
    θ' = θ :=
  ftProp1_closing hn ha hc hr hnr hpar hθ hθ' hbl
    (ftBranchZ_strictMonoOn hn ha hc hr hpar hbl) hlo hhi hzeq

/-! ### The other parity

`Forgacs2017RationalDenominator` states Lemma 4(ii) as strict monotonicity, the
direction fixed by the parity of `n - l - 1` (their footnote to Eq. (23)).  At
odd `n + l + 1` the branch value is negative, and `z' = -z|Σ|²/Im Σ` makes it
strictly decreasing. -/

theorem ftBranchZ_neg {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hpar : ¬ Even (n + l + 1)) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (h : FTBranchAt a r l θ) :
    ftBranchZ a c r l θ < 0 := by
  rw [ftBranchZ, (Nat.not_even_iff_odd.1 hpar).neg_one_pow]
  have hprod : 0 < ∏ k, ftChord (a k) θ (ftBranchAngle a r l k θ) :=
    Finset.prod_pos fun k _ => ftChord_pos (ha k) hθ (ftAngle_mem_Ioo (ha k) (ftTau_pos h) hθ)
  have hpos : 0 < c * (∏ k, ftChord (a k) θ (ftBranchAngle a r l k θ)) / ftTau a r l θ ^ r :=
    div_pos (mul_pos hc hprod) (pow_pos (ftTau_pos h) r)
  have hEq : -1 * c * (∏ k, ftChord (a k) θ (ftBranchAngle a r l k θ)) / ftTau a r l θ ^ r
      = -(c * (∏ k, ftChord (a k) θ (ftBranchAngle a r l k θ)) / ftTau a r l θ ^ r) := by
    ring
  rw [hEq]
  linarith

theorem ftBranchZDeriv_neg {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) (h : FTBranchAt a r l θ)
    (hz : ftBranchZ a c r l θ < 0) : ftBranchZDeriv a c r l θ < 0 := by
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hAim : (ftSigma a r (ftBranchPoint a r l θ)).im < 0 :=
    ftSigma_im_neg hn ha (ftBranchPoint_im_neg hθπ h)
  have hAne : ftSigma a r (ftBranchPoint a r l θ) ≠ 0 :=
    ftSigma_ne_zero hn ha (ftBranchPoint_im_neg hθπ h)
  have hns : 0 < Complex.normSq (ftSigma a r (ftBranchPoint a r l θ)) :=
    Complex.normSq_pos.2 hAne
  rw [ftBranchZDeriv]
  exact div_neg_of_pos_of_neg (by nlinarith) hAim

/-- **`Forgacs2017RationalDenominator` Lemma 4(ii) at odd `n + l + 1`.**  With
`ftBranchZ_strictMonoOn` this covers every index, so their Lemma 4(ii) is
formalized in full. -/
theorem ftBranchZ_strictAntiOn {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hpar : ¬ Even (n + l + 1))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    StrictAntiOn (ftBranchZ a c r l) (Ioo 0 (π / r)) := by
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      HasDerivAt (ftBranchZ a c r l) (ftBranchZDeriv a c r l θ) θ := fun θ hθ =>
    hasDerivAt_ftBranchZ hn ha hr hθ hb
      (ne_of_lt (ftBranchZ_neg ha hc hpar (ftArc_subset hr hθ) (hb θ hθ)))
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun θ hθ => ((hderiv θ hθ).continuousAt).continuousWithinAt) fun θ hθ => ?_
  rw [interior_Ioo] at hθ
  rw [(hderiv θ hθ).deriv]
  exact ftBranchZDeriv_neg hn ha hr hθ (hb θ hθ)
    (ftBranchZ_neg ha hc hpar (ftArc_subset hr hθ) (hb θ hθ))

end ForgacsTran
