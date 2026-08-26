/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.EndpointRegularity

/-!
# The principal amplitude and its divisor

`AttractorPole.ftAmp` is `eq:residue-amplitude`, `𝒲 = -B/∂_t D`; this module
gives its three descriptions, groups the principal conjugate pair, and reads off
the divisor of `W` along a branch.

## Main statements

* `ftAmp_eq_neg_div_derivative`, `ftAmp_eq_div_gDeriv`, `ftAmp_eq_ftCritical` —
  `eq:residue-amplitude`, `eq:W-on-g`, and the `eq:Dprime-identity` form of one
  object.
* `tendsto_residue_ftAmp` — `eq:simple-residue-amplitude`: the residue of
  `B(t)/(t^{M+1}D(t,z))` at a simple nonzero root is `-𝒲(ξ)ξ^{-M-1}`, so the
  contribution the expansion adds is `+𝒲(ξ)ξ^{-M-1}`.
* `principal_pair_contribution` — `eq:principal-decomposition`: the two
  principal residues, normalized by `τ^{M+1}`, are exactly
  `2 Re(W e^{-i(M+1)θ})`.
* `ftAmp_eq_zero_iff`, `amplitude_zero_count`, `amplitude_local_zero` —
  `eq:amplitude-zero-count` and `eq:W-local-zero`.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`,
`subsec:principal-amplitude`, `lem:amplitude-divisor`).

## Tags

principal amplitude, residue, divisor, denominator pencil, conjugate pair
-/

namespace ForgacsTran

open Polynomial Complex

/-! ### The three descriptions of the amplitude -/

/-- **`eq:residue-amplitude`.**  `𝒲(t,z) = -B(t)/∂_t D(t,z)`: the cofactor form
`ftAmp` carries and the derivative form the paper writes are the same at a
denominator zero. -/
theorem ftAmp_eq_neg_div_derivative {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℂ}
    (hroot : (ftDen Q r z).eval τ = 0) :
    ftAmp Q B r z τ = -B.eval τ / (derivative (ftDen Q r z)).eval τ := by
  rw [ftAmp, eval_derivative_ftDen hroot, neg_div]

/-- **`eq:W-on-g`.**  On the denominator curve the amplitude is
`W = B(γ)/(γ^r g'(γ))` for `g(t) = -Q(t)/t^r`.  No simplicity hypothesis is
needed: where `γ^r g'(γ)` vanishes both sides are the same junk value. -/
theorem ftAmp_eq_div_gDeriv {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℂ} (hτ : τ ≠ 0)
    (hroot : (ftDen Q r z).eval τ = 0) :
    ftAmp Q B r z τ = B.eval τ / (τ ^ r * deriv (ftBranch (fun s => Q.eval s) r) τ) := by
  rw [ftAmp_eq_neg_div_derivative hroot, eval_derivative_ftDen_eq_neg_gDeriv hτ hroot,
    div_neg, neg_div, neg_neg]

/-- **`eq:Dprime-identity` form of the amplitude.**  `W = -t B(t)/E(t)` with
`E(t) = t Q'(t) - r Q(t)`.  This is the form every order computation below runs
through, because `E` does not depend on `z`. -/
theorem ftAmp_eq_ftCritical {Q B : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r) {z τ : ℂ} (hτ : τ ≠ 0)
    (hroot : (ftDen Q r z).eval τ = 0) :
    ftAmp Q B r z τ = -(τ * B.eval τ) / (ftCritical Q r).eval τ := by
  rw [ftAmp_eq_neg_div_derivative hroot, eval_derivative_ftDen_eq_ftCritical_div hr hτ hroot,
    div_div_eq_mul_div]
  ring

/-- **`eq:simple-residue-amplitude`.**  At a simple nonzero denominator zero the
residue of `B(t)/(t^{M+1}D(t,z))` is `-𝒲(ξ)ξ^{-M-1}`; the expansion
`eq:contour-separated-expansion` subtracts it, so the contribution is
`+𝒲(ξ)ξ^{-M-1}`. -/
theorem tendsto_residue_ftAmp {Q B : Polynomial ℂ} {r M : ℕ} {z ξ : ℂ} (hξ : ξ ≠ 0)
    (hroot : (ftDen Q r z).eval ξ = 0)
    (hsimple : (derivative (ftDen Q r z)).eval ξ ≠ 0) :
    Filter.Tendsto
      (fun t => (t - ξ) * (B.eval t / (t ^ (M + 1) * (ftDen Q r z).eval t)))
      (nhdsWithin ξ {ξ}ᶜ) (nhds (-ftAmp Q B r z ξ / ξ ^ (M + 1))) := by
  have hS : (ftCofactor Q r z ξ).eval ξ ≠ 0 := by
    rwa [← eval_derivative_ftDen hroot]
  have hfac : ∀ t : ℂ, (ftDen Q r z).eval t = (t - ξ) * (ftCofactor Q r z ξ).eval t := fun t => by
    conv_lhs => rw [← ftCofactor_mul hroot]
    simp
  have hcongr : (fun t : ℂ => B.eval t / (t ^ (M + 1) * (ftCofactor Q r z ξ).eval t))
      =ᶠ[nhdsWithin ξ ({ξ}ᶜ : Set ℂ)]
      fun t : ℂ => (t - ξ) * (B.eval t / (t ^ (M + 1) * (ftDen Q r z).eval t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htξ : t - ξ ≠ 0 := sub_ne_zero.mpr ht
    rw [hfac t]
    field_simp
  have hlim : Filter.Tendsto
      (fun t : ℂ => B.eval t / (t ^ (M + 1) * (ftCofactor Q r z ξ).eval t))
      (nhds ξ) (nhds (B.eval ξ / (ξ ^ (M + 1) * (ftCofactor Q r z ξ).eval ξ))) := by
    refine Filter.Tendsto.div (B.continuous_aeval.tendsto ξ) ?_ ?_
    · exact ((continuous_pow (M + 1)).tendsto ξ).mul
        ((ftCofactor Q r z ξ).continuous_aeval.tendsto ξ)
    · exact mul_ne_zero (pow_ne_zero _ hξ) hS
  have hval : B.eval ξ / (ξ ^ (M + 1) * (ftCofactor Q r z ξ).eval ξ)
      = -ftAmp Q B r z ξ / ξ ^ (M + 1) := by
    rw [ftAmp]
    field_simp
  rw [← hval]
  exact (hlim.mono_left nhdsWithin_le_nhds).congr' hcongr

/-! ### Real coefficients and the principal conjugate pair -/

/-- A polynomial with real coefficients, viewed in `ℂ[X]`.  `eq:Q-hypotheses`
puts `Q` here, and the reduced numerator `B` of `sec:reduction` is real too. -/
def HasRealCoeffs (p : Polynomial ℂ) : Prop := ∀ n, (starRingEnd ℂ) (p.coeff n) = p.coeff n

theorem HasRealCoeffs.eval_conj {p : Polynomial ℂ} (hp : HasRealCoeffs p) (t : ℂ) :
    (starRingEnd ℂ) (p.eval t) = p.eval ((starRingEnd ℂ) t) := by
  rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
  exact Finset.sum_congr rfl fun n _ => by rw [map_mul, map_pow, hp n]

theorem HasRealCoeffs.add {p q : Polynomial ℂ} (hp : HasRealCoeffs p) (hq : HasRealCoeffs q) :
    HasRealCoeffs (p + q) := fun n => by rw [coeff_add, map_add, hp n, hq n]

theorem HasRealCoeffs.derivative {p : Polynomial ℂ} (hp : HasRealCoeffs p) :
    HasRealCoeffs (Polynomial.derivative p) := fun n => by
  rw [coeff_derivative, map_mul, hp (n + 1)]
  norm_num

theorem hasRealCoeffs_C_mul_X_pow (z : ℝ) (r : ℕ) :
    HasRealCoeffs (C (z : ℂ) * X ^ r) := fun n => by
  rw [coeff_C_mul, coeff_X_pow, map_mul, Complex.conj_ofReal]
  split <;> simp

theorem HasRealCoeffs.ftDen {Q : Polynomial ℂ} (hQ : HasRealCoeffs Q) (r : ℕ) (z : ℝ) :
    HasRealCoeffs (ForgacsTran.ftDen Q r (z : ℂ)) :=
  hQ.add (hasRealCoeffs_C_mul_X_pow z r)

/-- The conjugate of a denominator zero is a denominator zero. -/
theorem ftDen_eval_conj_eq_zero {Q : Polynomial ℂ} (hQ : HasRealCoeffs Q) {r : ℕ} {z : ℝ} {t : ℂ}
    (hroot : (ftDen Q r (z : ℂ)).eval t = 0) :
    (ftDen Q r (z : ℂ)).eval ((starRingEnd ℂ) t) = 0 := by
  rw [← (hQ.ftDen r z).eval_conj, hroot, map_zero]

/-- **The conjugate pair carries conjugate amplitudes.** -/
theorem ftAmp_conj {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) {r : ℕ}
    {z : ℝ} {t : ℂ} (hroot : (ftDen Q r (z : ℂ)).eval t = 0) :
    ftAmp Q B r (z : ℂ) ((starRingEnd ℂ) t)
      = (starRingEnd ℂ) (ftAmp Q B r (z : ℂ) t) := by
  have hrootc := ftDen_eval_conj_eq_zero hQ hroot
  rw [ftAmp_eq_neg_div_derivative hroot, ftAmp_eq_neg_div_derivative hrootc,
    map_div₀, map_neg, hB.eval_conj, (hQ.ftDen r z).derivative.eval_conj]


/-- **`eq:principal-decomposition`, the grouping.**  A conjugate pair of
denominator zeros contributes, after normalization by any real scale `τ^{M+1}`,
twice the real part of the single principal term.  Only reality of `Q`, `B` and
`z` is used. -/
theorem principal_pair_contribution {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r M : ℕ} {z τ : ℝ} {t : ℂ}
    (hroot : (ftDen Q r (z : ℂ)).eval t = 0) :
    ((τ : ℂ)) ^ (M + 1) * (ftAmp Q B r (z : ℂ) t / t ^ (M + 1))
        + ((τ : ℂ)) ^ (M + 1) *
          (ftAmp Q B r (z : ℂ) ((starRingEnd ℂ) t) / ((starRingEnd ℂ) t) ^ (M + 1))
      = ((2 * (((τ : ℂ)) ^ (M + 1) * (ftAmp Q B r (z : ℂ) t / t ^ (M + 1))).re : ℝ) : ℂ) := by
  have hsecond : ((τ : ℂ)) ^ (M + 1) *
      (ftAmp Q B r (z : ℂ) ((starRingEnd ℂ) t) / ((starRingEnd ℂ) t) ^ (M + 1))
      = (starRingEnd ℂ) (((τ : ℂ)) ^ (M + 1) * (ftAmp Q B r (z : ℂ) t / t ^ (M + 1))) := by
    rw [map_mul, map_div₀, map_pow, map_pow, Complex.conj_ofReal, ftAmp_conj hQ hB hroot]
  rw [hsecond, Complex.add_conj]

/-- **`eq:principal-decomposition`, the exponential form.**  With
`t_+ = τ e^{iθ}` and `τ > 0`, the normalization `τ^{M+1}/t_+^{M+1}` is exactly
`e^{-i(M+1)θ}`, so the pair's contribution is `2 Re(W e^{-i(M+1)θ})`. -/
theorem ofReal_pow_div_principal_pow {M : ℕ} {τ θ : ℝ} (hτ : 0 < τ) :
    ((τ : ℂ)) ^ (M + 1) / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1)
      = Complex.exp (((-(((M : ℝ) + 1) * θ) : ℝ) : ℂ) * I) := by
  have hτ0 : ((τ : ℂ)) ≠ 0 := by exact_mod_cast hτ.ne'
  have h1 : (Complex.exp ((θ : ℂ) * I)) ^ (M + 1)
      = Complex.exp (((((M : ℝ) + 1) * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow, h1, div_mul_eq_div_div, div_self (pow_ne_zero _ hτ0), one_div, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-! ### The divisor of the amplitude along the principal branch -/

/-- **`lem:amplitude-divisor`, first sentence.**  Where the principal root is
simple, `W(θ) = 0` exactly when `B(γ(θ)) = 0`. -/
theorem ftAmp_eq_zero_iff {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℂ}
    (hroot : (ftDen Q r z).eval τ = 0)
    (hsimple : (derivative (ftDen Q r z)).eval τ ≠ 0) :
    ftAmp Q B r z τ = 0 ↔ B.eval τ = 0 := by
  rw [ftAmp_eq_neg_div_derivative hroot, div_eq_zero_iff]
  simp [hsimple]

/-- **`eq:amplitude-zero-count`.**  Along an injective branch the zeros of `W`
have total multiplicity at most `deg B`: their `γ`-images are distinct zeros of
`B`, and `B` has no more than `deg B` of those. -/
theorem amplitude_zero_count {B : Polynomial ℂ} (hB : B ≠ 0) {γ : ℝ → ℂ} {S : Finset ℝ}
    (hinj : Set.InjOn γ (S : Set ℝ)) :
    ∑ θ ∈ S, B.rootMultiplicity (γ θ) ≤ B.natDegree := by
  classical
  have h1 : ∑ a ∈ S.image γ, B.roots.count a = ∑ θ ∈ S, B.roots.count (γ θ) :=
    Finset.sum_image fun x hx y hy hxy => hinj hx hy hxy
  have h2 : ∀ a : ℂ, B.rootMultiplicity a = B.roots.count a := fun a => (count_roots B).symm
  simp only [h2, ← h1]
  calc ∑ a ∈ S.image γ, B.roots.count a
      ≤ ∑ a ∈ (S.image γ) ∪ B.roots.toFinset, B.roots.count a :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ a ∈ B.roots.toFinset, B.roots.count a := by
        refine (Finset.sum_subset Finset.subset_union_right ?_).symm
        intro x _ hx
        exact Multiset.count_eq_zero.mpr (by simpa using hx)
    _ = Multiset.card B.roots := Multiset.toFinset_sum_count_eq B.roots
    _ ≤ B.natDegree := B.card_roots'

theorem continuousAt_eval_derivative_ftDen {Q : Polynomial ℂ} {r : ℕ} {γ zf : ℝ → ℂ} {θ₀ : ℝ}
    (hγ : ContinuousAt γ θ₀) (hzf : ContinuousAt zf θ₀) :
    ContinuousAt (fun θ => (derivative (ftDen Q r (zf θ))).eval (γ θ)) θ₀ := by
  simp only [eval_derivative_ftDen_formula]
  exact (((Polynomial.continuous (derivative Q)).continuousAt).comp hγ).add
    ((continuousAt_const.mul hzf).mul (hγ.pow (r - 1)))

/-- **`eq:W-local-zero`.**  At an interior parameter where the principal root is
simple, `W(θ) = (θ-θ_j)^{ν_j} U_j(θ)` with `U_j(θ_j) ≠ 0`, and `ν_j` is the
multiplicity of `γ(θ_j)` as a zero of `B`.  A nonvanishing `γ'` is what carries
the multiplicity across; nothing else about the branch is used. -/
theorem amplitude_local_zero {Q B : Polynomial ℂ} (hB : B ≠ 0) {r : ℕ} {γ zf : ℝ → ℂ}
    {θ₀ : ℝ} {γ' : ℂ} (hγ : HasDerivAt γ γ' θ₀) (hγ' : γ' ≠ 0) (hzf : ContinuousAt zf θ₀)
    (hroot : ∀ᶠ θ in nhds θ₀, (ftDen Q r (zf θ)).eval (γ θ) = 0)
    (hsimple : (derivative (ftDen Q r (zf θ₀))).eval (γ θ₀) ≠ 0) :
    ∃ U : ℝ → ℂ, ContinuousAt U θ₀ ∧ U θ₀ ≠ 0 ∧
      ∀ᶠ θ in nhds θ₀,
        ftAmp Q B r (zf θ) (γ θ)
          = ((θ : ℂ) - (θ₀ : ℂ)) ^ B.rootMultiplicity (γ θ₀) * U θ := by
  classical
  set ν := B.rootMultiplicity (γ θ₀) with hν
  set Bt := B /ₘ (X - C (γ θ₀)) ^ ν with hBt
  have hBfac : (X - C (γ θ₀)) ^ ν * Bt = B := pow_mul_divByMonic_rootMultiplicity_eq B _
  have hBtne : Bt.eval (γ θ₀) ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero _ hB
  set den : ℝ → ℂ := fun θ => (derivative (ftDen Q r (zf θ))).eval (γ θ) with hden
  have hdenne : den θ₀ ≠ 0 := hsimple
  have hdenc : ContinuousAt den θ₀ := continuousAt_eval_derivative_ftDen hγ.continuousAt hzf
  set h : ℝ → ℂ :=
    fun θ => if θ = θ₀ then γ' else (γ θ - γ θ₀) / ((θ : ℂ) - (θ₀ : ℂ)) with hh
  have hval : h θ₀ = γ' := by simp [hh]
  have hhmul : ∀ θ, γ θ - γ θ₀ = ((θ : ℂ) - (θ₀ : ℂ)) * h θ := by
    intro θ
    by_cases hθ : θ = θ₀
    · simp [hh, hθ]
    · have hne : ((θ : ℂ) - (θ₀ : ℂ)) ≠ 0 := by
        simpa [sub_eq_zero, Complex.ofReal_inj] using hθ
      rw [hh]
      simp only [if_neg hθ]
      field_simp
  have hhc : ContinuousAt h θ₀ := by
    refine continuousWithinAt_compl_self.mp ?_
    have hlim : Filter.Tendsto h (nhdsWithin θ₀ ({θ₀}ᶜ : Set ℝ)) (nhds γ') := by
      refine (hasDerivAt_iff_tendsto_slope.mp hγ).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      have hθ' : ¬ (θ = θ₀) := hθ
      simp only [hh, if_neg hθ', slope_def_module, Complex.real_smul,
        Complex.ofReal_inv, Complex.ofReal_sub, div_eq_inv_mul]
    have : ContinuousWithinAt h ({θ₀}ᶜ : Set ℝ) θ₀ := by
      rw [ContinuousWithinAt, hval]; exact hlim
    exact this
  refine ⟨fun θ => -((h θ) ^ ν * Bt.eval (γ θ)) / den θ, ?_, ?_, ?_⟩
  · exact ((hhc.pow ν).mul (((Polynomial.continuous Bt).continuousAt).comp hγ.continuousAt)).neg.div
      hdenc hdenne
  · change -((h θ₀) ^ ν * Bt.eval (γ θ₀)) / den θ₀ ≠ 0
    rw [hval]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hγ') hBtne)) hdenne
  · filter_upwards [hroot] with θ hθ
    have hBev : B.eval (γ θ) = (γ θ - γ θ₀) ^ ν * Bt.eval (γ θ) := by
      conv_lhs => rw [← hBfac]
      simp
    rw [ftAmp_eq_neg_div_derivative hθ, hBev, hhmul θ, mul_pow,
      show -((((θ : ℂ) - (θ₀ : ℂ)) ^ ν * (h θ) ^ ν) * Bt.eval (γ θ))
        = (((θ : ℂ) - (θ₀ : ℂ)) ^ ν) * (-((h θ) ^ ν * Bt.eval (γ θ))) by ring,
      mul_div_assoc]


/-! ### The endpoint exponent -/

/-- **`eq:W-endpoint-form` at a finite endpoint.**  `W = δ^p V(δ)` with
`p = ν - (k-1)`: `B` vanishes to order `ν` at the limiting principal root `t_e`,
the `z`-free factor `E` vanishes there to order exactly `k-1`
(`rootMultiplicity_ftCritical`), and the branch enters `t_e` linearly.  Stated
with the negative power cleared, since `p` is an integer that is negative
whenever `ν < k-1` — which is the generic case, `p = -1` at an ordinary double
collision with `B(t_e) ≠ 0`.

**One-sided at the endpoint, and the two halves take different domains.**  `δ` is
the angular *distance* to the endpoint, so `δ ≥ 0` throughout and a two-sided
derivative is not available: `τ` is even — the branch condition sees `θ` only
through `cos` — so the two one-sided difference quotients at the endpoint are
exact negatives and both nonzero, and `τ` has a corner there rather than a
derivative.  `lem:principal-endpoint-regularity` extends the branch to a regular
arc on the *closed* interval, which is what `Set.Ici 0` records.

The asymmetry between the two hypotheses is deliberate.  `hγ` takes `Set.Ici 0`,
because the conclusion makes claims *at* the endpoint — `V 0 ≠ 0` and the
continuity there — which a derivative on `Set.Ioi 0` alone cannot supply.  `hroot`
takes `nhdsWithin 0 (Set.Ioi 0)`, because no conclusion says anything at the
endpoint, and `nhdsWithin 0 (Set.Ici 0)` would re-import the condition at `δ = 0`
that `hk` already supplies separately.  Making the two uniform in the strong
direction is what makes the downstream binder unmeetable. -/
theorem amplitude_endpoint_form {Q B : Polynomial ℂ} (hB : B ≠ 0) {r : ℕ} (hr : 1 ≤ r)
    {γ zf : ℝ → ℂ} {te γe : ℂ} (hte : te ≠ 0) (hγe : γe ≠ 0) (hγ0 : γ 0 = te)
    (hγ : HasDerivWithinAt γ γe (Set.Ici (0 : ℝ)) 0) (hP : ftDen Q r (zf 0) ≠ 0)
    (hk : 1 ≤ (ftDen Q r (zf 0)).rootMultiplicity te)
    (hroot : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (ftDen Q r (zf δ)).eval (γ δ) = 0) :
    ∃ V : ℝ → ℂ, ContinuousWithinAt V (Set.Ici (0 : ℝ)) 0 ∧ V 0 ≠ 0 ∧
      ∀ᶠ (δ : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ((δ : ℂ)) ^ ((ftDen Q r (zf 0)).rootMultiplicity te - 1) * ftAmp Q B r (zf δ) (γ δ)
          = ((δ : ℂ)) ^ B.rootMultiplicity te * V δ := by
  classical
  set k := (ftDen Q r (zf 0)).rootMultiplicity te with hkdef
  set ν := B.rootMultiplicity te with hνdef
  obtain ⟨H, hEfac, hH⟩ := exists_ftCritical_factor hr hte hP hk
  set Bt := B /ₘ (X - C te) ^ ν with hBtdef
  have hBfac : (X - C te) ^ ν * Bt = B := pow_mul_divByMonic_rootMultiplicity_eq B _
  have hBtne : Bt.eval te ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero _ hB
  set h : ℝ → ℂ := fun δ => if δ = 0 then γe else (γ δ - te) / (δ : ℂ) with hh
  have hval : h 0 = γe := by simp [hh]
  have hhmul : ∀ δ, γ δ - te = (δ : ℂ) * h δ := by
    intro δ
    by_cases hδ : δ = 0
    · simp [hh, hδ, hγ0]
    · have hne : ((δ : ℂ)) ≠ 0 := by simpa [Complex.ofReal_eq_zero] using hδ
      rw [hh]; simp only [if_neg hδ]; field_simp
  have hhc : ContinuousWithinAt h (Set.Ici (0 : ℝ)) 0 := by
    have hγ' : HasDerivWithinAt γ γe (Set.Ioi (0 : ℝ)) 0 :=
      hγ.mono Set.Ioi_subset_Ici_self
    have hlim : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds γe) := by
      refine ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hγ').congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ' : ¬ (δ = 0) := ne_of_gt hδ
      simp only [hh, if_neg hδ', slope_def_module, Complex.real_smul,
        Complex.ofReal_inv, div_eq_inv_mul, hγ0,
        sub_zero]
    have hIoi : ContinuousWithinAt h (Set.Ioi (0 : ℝ)) 0 := by
      rw [ContinuousWithinAt, hval]; exact hlim
    rw [← Set.Ioi_union_left]
    exact hIoi.union continuousWithinAt_singleton
  have hγc : ContinuousWithinAt γ (Set.Ici (0 : ℝ)) 0 := hγ.continuousWithinAt
  have hHc : ContinuousWithinAt (fun δ => H.eval (γ δ)) (Set.Ici (0 : ℝ)) 0 :=
    ((Polynomial.continuous H).continuousAt).comp_continuousWithinAt hγc
  have hBtc : ContinuousWithinAt (fun δ => Bt.eval (γ δ)) (Set.Ici (0 : ℝ)) 0 :=
    ((Polynomial.continuous Bt).continuousAt).comp_continuousWithinAt hγc
  have hHne : H.eval (γ 0) ≠ 0 := by rwa [hγ0]
  refine ⟨fun δ => -(γ δ * ((h δ) ^ ν * Bt.eval (γ δ))) / ((h δ) ^ (k - 1) * H.eval (γ δ)),
    ?_, ?_, ?_⟩
  · exact ((hγc.mul ((hhc.pow ν).mul hBtc)).neg).div (((hhc.pow (k - 1)).mul hHc))
      (mul_ne_zero (pow_ne_zero _ (by rw [hval]; exact hγe)) hHne)
  · change -(γ 0 * ((h 0) ^ ν * Bt.eval (γ 0))) / ((h 0) ^ (k - 1) * H.eval (γ 0)) ≠ 0
    rw [hval, hγ0]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hte (mul_ne_zero (pow_ne_zero _ hγe) hBtne)))
      (mul_ne_zero (pow_ne_zero _ hγe) hH)
  · have hmono : nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
        ≤ nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)) :=
      nhdsWithin_mono _ Set.Ioi_subset_Ici_self
    have hnear : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        (ftDen Q r (zf δ)).eval (γ δ) = 0 ∧ γ δ ≠ 0 ∧ h δ ≠ 0 ∧ H.eval (γ δ) ≠ 0 := by
      filter_upwards [hroot,
        hmono (Filter.Tendsto.eventually_ne hγc (by rwa [hγ0])),
        hmono (Filter.Tendsto.eventually_ne hhc (by rw [hval]; exact hγe)),
        hmono (Filter.Tendsto.eventually_ne hHc hHne)] with δ h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    filter_upwards [hnear, self_mem_nhdsWithin] with δ hδ hδ0
    obtain ⟨hr0, hγne, hhne, hHne'⟩ := hδ
    have hδ0' : δ ≠ 0 := ne_of_gt hδ0
    have hδne : ((δ : ℂ)) ≠ 0 := by simpa [Complex.ofReal_eq_zero] using hδ0'
    have hBev : B.eval (γ δ) = ((δ : ℂ) * h δ) ^ ν * Bt.eval (γ δ) := by
      conv_lhs => rw [← hBfac]
      simp [← hhmul δ]
    have hEev : (ftCritical Q r).eval (γ δ) = ((δ : ℂ) * h δ) ^ (k - 1) * H.eval (γ δ) := by
      conv_lhs => rw [hEfac, ← hkdef]
      simp [← hhmul δ]
    rw [ftAmp_eq_ftCritical hr hγne hr0, hBev, hEev, mul_pow, mul_pow]
    field_simp

/-- **`eq:W-endpoint-form` at the unbounded upper endpoint (`r > 1`).**  There
the principal root runs into the origin as `γ = η T(η)`, `E(0) = -rQ(0) ≠ 0`,
and `B(0) ≠ 0`, so `W = η V(η)` with `V(0) ≠ 0`: the exponent is `p = 1`. -/
theorem amplitude_endpoint_form_origin {Q B : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    (hB0 : B.eval 0 ≠ 0) (hQ0 : Q.eval 0 ≠ 0) {γ zf T : ℝ → ℂ}
    (hT : ContinuousWithinAt T (Set.Ici (0 : ℝ)) 0) (hT0 : T 0 ≠ 0)
    (hγ : ∀ η, γ η = (η : ℂ) * T η)
    (hroot : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (ftDen Q r (zf η)).eval (γ η) = 0) :
    ∃ V : ℝ → ℂ, ContinuousWithinAt V (Set.Ici (0 : ℝ)) 0 ∧ V 0 ≠ 0 ∧
      ∀ᶠ (η : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ftAmp Q B r (zf η) (γ η) = (η : ℂ) * V η := by
  have hγ0 : γ 0 = 0 := by simp [hγ]
  have hγc : ContinuousWithinAt γ (Set.Ici (0 : ℝ)) 0 := by
    have hfun : γ = fun η : ℝ => (η : ℂ) * T η := funext hγ
    rw [hfun]
    exact (Complex.continuous_ofReal.continuousAt).continuousWithinAt.mul hT
  have hrne : ((r : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hE0 : (ftCritical Q r).eval (γ 0) ≠ 0 := by
    rw [hγ0, eval_ftCritical]
    simpa using mul_ne_zero hrne hQ0
  have hEc : ContinuousWithinAt (fun η => (ftCritical Q r).eval (γ η)) (Set.Ici (0 : ℝ)) 0 :=
    ((Polynomial.continuous (ftCritical Q r)).continuousAt).comp_continuousWithinAt hγc
  have hBc : ContinuousWithinAt (fun η => B.eval (γ η)) (Set.Ici (0 : ℝ)) 0 :=
    ((Polynomial.continuous B).continuousAt).comp_continuousWithinAt hγc
  refine ⟨fun η => -(T η * B.eval (γ η)) / (ftCritical Q r).eval (γ η), ?_, ?_, ?_⟩
  · exact ((hT.mul hBc).neg).div hEc hE0
  · change -(T 0 * B.eval (γ 0)) / (ftCritical Q r).eval (γ 0) ≠ 0
    rw [hγ0]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hT0 hB0)) (by rwa [hγ0] at hE0)
  · have hmono : nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
        ≤ nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)) :=
      nhdsWithin_mono _ Set.Ioi_subset_Ici_self
    have hnear : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        (ftDen Q r (zf η)).eval (γ η) = 0 ∧ T η ≠ 0 ∧ (ftCritical Q r).eval (γ η) ≠ 0 := by
      filter_upwards [hroot, hmono (Filter.Tendsto.eventually_ne hT hT0),
        hmono (Filter.Tendsto.eventually_ne hEc hE0)] with η h1 h2 h3
      exact ⟨h1, h2, h3⟩
    filter_upwards [hnear, self_mem_nhdsWithin] with η hη hη0
    obtain ⟨hr0, hTne, hEne⟩ := hη
    have hη0' : η ≠ 0 := ne_of_gt hη0
    have hηne : ((η : ℂ)) ≠ 0 := by simpa [Complex.ofReal_eq_zero] using hη0'
    have hγne : γ η ≠ 0 := by rw [hγ]; exact mul_ne_zero hηne hTne
    rw [ftAmp_eq_ftCritical hr hγne hr0, hγ]
    field_simp

/-- **`lem:amplitude-divisor` at the unbounded upper endpoint**, in the form
`thm:weighted-dominance` uses it: `Aη \le |W(η)|` on a one-sided window.

The exponent is `1` **unconditionally** — no `ν_B`, no `k - 1`.  That is not a
simplification but the geometry: the principal root runs into the *origin*, where
`B(0) \ne 0` and `E(0) = -rQ(0) \ne 0`, so neither `B` nor the `z`-free factor
vanishes at the limit point and there is no order to subtract.  The manuscript
says the same thing in one sentence — `B(0) \ne 0` means `B` does not vanish on
the upper cluster at all.

This is the twin of `DominanceFT.amplitude_lower_bound_of_endpoint_form`, and the
two are not interchangeable: that one needs `t_e \ne 0`, which
`FTBranchUpperRefutation.not_upper_endpoint_datum_ne_zero` refutes for every
`n \ge 2` and `r \ge 2`.  The fact that refutes it — `t_e = 0` — is exactly the
`γ(0) = 0` this route requires. -/
theorem amplitude_lower_bound_of_origin_form {Q B : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    (hB0 : B.eval 0 ≠ 0) (hQ0 : Q.eval 0 ≠ 0) {γ zf T : ℝ → ℂ}
    (hT : ContinuousWithinAt T (Set.Ici (0 : ℝ)) 0) (hT0 : T 0 ≠ 0)
    (hγ : ∀ η, γ η = (η : ℂ) * T η)
    (hroot : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (ftDen Q r (zf η)).eval (γ η) = 0) :
    ∃ A > (0 : ℝ), ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A * η ≤ ‖ftAmp Q B r (zf η) (γ η)‖ := by
  classical
  obtain ⟨V, hVc, hV0, hVeq⟩ :=
    amplitude_endpoint_form_origin hr hB0 hQ0 hT hT0 hγ hroot
  set A : ℝ := ‖V 0‖ / 2 with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hmono : nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
      ≤ nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)) :=
    nhdsWithin_mono _ Set.Ioi_subset_Ici_self
  have hVbd : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)), A < ‖V η‖ := by
    refine (hVc.norm).eventually_const_lt ?_
    rw [hAdef]
    have : 0 < ‖V 0‖ := norm_pos_iff.mpr hV0
    linarith
  have hev : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ftAmp Q B r (zf η) (γ η) = (η : ℂ) * V η ∧ A < ‖V η‖ :=
    hVeq.and (hmono hVbd)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨A, hApos, min (ε₀ / 2) 1, lt_min (by linarith) one_pos, ?_⟩
  intro η hη hηe
  have hη0 : dist η (0 : ℝ) < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hη]
    have h1 : η ≤ ε₀ / 2 := le_trans hηe (min_le_left _ _)
    linarith
  obtain ⟨hid, hVη⟩ := hball hη0 (Set.mem_Ioi.mpr hη)
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  calc A * η ≤ ‖V η‖ * η := mul_le_mul_of_nonneg_right hVη.le hη.le
    _ = η * ‖V η‖ := by ring

/-! ### The phase derivative -/

/-- **`eq:phase-derivative-bound`, the cancellation.**  Through an amplitude zero
the logarithmic derivative acquires the singular term `ν/(θ-θ_j)`, which is
*real*, so it does not reach `ψ' = Im(W'/W)`. -/
theorem im_logDeriv_of_factor {U : ℝ → ℂ} {U' : ℂ} {θ θ₀ : ℝ} {ν : ℕ}
    (hθ : θ ≠ θ₀) (hU : HasDerivAt U U' θ) (hU0 : U θ ≠ 0) :
    (deriv (fun s : ℝ => ((s : ℂ) - (θ₀ : ℂ)) ^ ν * U s) θ
        / (((θ : ℂ) - (θ₀ : ℂ)) ^ ν * U θ)).im
      = (U' / U θ).im := by
  have hne : ((θ : ℂ) - (θ₀ : ℂ)) ≠ 0 := by simpa [sub_eq_zero, Complex.ofReal_inj] using hθ
  have hcoe : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp
  have hbase : HasDerivAt (fun s : ℝ => (s : ℂ) - (θ₀ : ℂ)) 1 θ := hcoe.sub_const _
  have hpow : HasDerivAt (fun s : ℝ => ((s : ℂ) - (θ₀ : ℂ)) ^ ν)
      ((ν : ℂ) * ((θ : ℂ) - (θ₀ : ℂ)) ^ (ν - 1) * 1) θ := hbase.pow ν
  have hW : HasDerivAt (fun s : ℝ => ((s : ℂ) - (θ₀ : ℂ)) ^ ν * U s)
      ((ν : ℂ) * ((θ : ℂ) - (θ₀ : ℂ)) ^ (ν - 1) * 1 * U θ + ((θ : ℂ) - (θ₀ : ℂ)) ^ ν * U') θ :=
    hpow.mul hU
  have hsplit : deriv (fun s : ℝ => ((s : ℂ) - (θ₀ : ℂ)) ^ ν * U s) θ
      / (((θ : ℂ) - (θ₀ : ℂ)) ^ ν * U θ)
      = (((ν : ℝ) / (θ - θ₀) : ℝ) : ℂ) + U' / U θ := by
    rw [hW.deriv]
    have hpne : (((θ : ℂ) - (θ₀ : ℂ)) ^ ν) ≠ 0 := pow_ne_zero _ hne
    have hpsucc : ((θ : ℂ) - (θ₀ : ℂ)) ^ ν
        = ((θ : ℂ) - (θ₀ : ℂ)) * ((θ : ℂ) - (θ₀ : ℂ)) ^ (ν - 1) ∨ ν = 0 := by
      rcases Nat.eq_zero_or_pos ν with h | h
      · exact Or.inr h
      · left; conv_lhs => rw [show ν = 1 + (ν - 1) by omega]
        rw [pow_add, pow_one]
    push_cast
    rcases hpsucc with hps | hps
    · rw [hps]; field_simp
    · subst hps; simp
  rw [hsplit, Complex.add_im, Complex.ofReal_im, zero_add]

/-- **`eq:phase-derivative-bound`.**  On a compact subarc on which the cofactor
`U` is differentiable and nonvanishing, `|ψ'| = |Im(W'/W)|` is bounded, the
amplitude zero at `θ₀` notwithstanding. -/
theorem exists_phase_derivative_bound {U dU : ℝ → ℂ} {θ₀ a b : ℝ} {ν : ℕ}
    (hU : ∀ θ ∈ Set.Icc a b, HasDerivAt U (dU θ) θ)
    (hcont : ContinuousOn (fun θ => (dU θ / U θ).im) (Set.Icc a b))
    (hU0 : ∀ θ ∈ Set.Icc a b, U θ ≠ 0) :
    ∃ κ : ℝ, ∀ θ ∈ Set.Icc a b, θ ≠ θ₀ →
      |(deriv (fun s : ℝ => ((s : ℂ) - (θ₀ : ℂ)) ^ ν * U s) θ
          / (((θ : ℂ) - (θ₀ : ℂ)) ^ ν * U θ)).im| ≤ κ := by
  obtain ⟨κ, hκ⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨κ, fun θ hθ hθ₀ => ?_⟩
  rw [im_logDeriv_of_factor hθ₀ (hU θ hθ) (hU0 θ hθ)]
  simpa [Real.norm_eq_abs] using hκ θ hθ

/-- **`eq:phase-derivative-bound`, the identity `ψ' = Im(W'/W)`.**  For a
differentiable polar representation `W = ρ e^{iψ}` with `ρ` real and nonzero,
the imaginary part of the logarithmic derivative *is* the phase derivative. -/
theorem im_logDeriv_eq_phase_deriv {ρ ψ : ℝ → ℝ} {θ ρ' ψ' : ℝ}
    (hρ : HasDerivAt ρ ρ' θ) (hψ : HasDerivAt ψ ψ' θ) (hρ0 : ρ θ ≠ 0) :
    (deriv (fun s : ℝ => ((ρ s : ℂ)) * Complex.exp (((ψ s : ℝ) : ℂ) * I)) θ
        / (((ρ θ : ℂ)) * Complex.exp (((ψ θ : ℝ) : ℂ) * I))).im = ψ' := by
  have hρc : HasDerivAt (fun s : ℝ => ((ρ s : ℂ))) ((ρ' : ℂ)) θ := hρ.ofReal_comp
  have hψc : HasDerivAt (fun s : ℝ => ((ψ s : ℝ) : ℂ) * I) ((ψ' : ℂ) * I) θ :=
    hψ.ofReal_comp.mul_const I
  have hexp := hψc.cexp
  have hW : HasDerivAt (fun s : ℝ => ((ρ s : ℂ)) * Complex.exp (((ψ s : ℝ) : ℂ) * I))
      ((ρ' : ℂ) * Complex.exp (((ψ θ : ℝ) : ℂ) * I)
        + (ρ θ : ℂ) * (Complex.exp (((ψ θ : ℝ) : ℂ) * I) * ((ψ' : ℂ) * I))) θ :=
    hρc.mul hexp
  have hρ0' : ((ρ θ : ℂ)) ≠ 0 := by simpa using hρ0
  have hexpne : Complex.exp (((ψ θ : ℝ) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  rw [hW.deriv]
  have : ((ρ' : ℂ) * Complex.exp (((ψ θ : ℝ) : ℂ) * I)
        + (ρ θ : ℂ) * (Complex.exp (((ψ θ : ℝ) : ℂ) * I) * ((ψ' : ℂ) * I)))
      / ((ρ θ : ℂ) * Complex.exp (((ψ θ : ℝ) : ℂ) * I))
      = ((ρ' / ρ θ : ℝ) : ℂ) + (ψ' : ℂ) * I := by
    push_cast
    field_simp
  rw [this, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im]
  simp


/-- The conjugate of a point in polar form. -/
theorem conj_polar (τ θ : ℝ) :
    (starRingEnd ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
      = (τ : ℂ) * Complex.exp (-(θ : ℂ) * I) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp [Complex.conj_I, mul_comm]

/-- **`eq:principal-decomposition`, assembled.**  Once the coefficient is written
as its two principal contributions plus a remainder, normalizing by `τ^{M+1}`
turns the pair into `2 Re(W e^{-i(M+1)θ})` and leaves `τ^{M+1}E_M`, which is what
the paper calls `R_M` when the retained cluster is the principal pair alone.

The expansion `hexp` is the **one** input taken on faith here.  It is
`eq:contour-separated-expansion` of `lem:contour-separation` restricted to a
contour enclosing only the principal pair; neither that identity nor its decay
half `eq:contour-remainder-bound` is formalized in this tree, and
`AttractorPole.norm_ftCoeff_sub_amp_le` does not supply it because that result
assumes a *uniquely* dominant root, whereas here two roots sit inside the
separating circle.  Everything else in the display is proved. -/
theorem principal_decomposition {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r M : ℕ} {τ θ z : ℝ} (hτ : 0 < τ) {FM EM : ℂ}
    (hroot : (ftDen Q r (z : ℂ)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) = 0)
    (hexp : FM
      = ftAmp Q B r (z : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
          / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1)
        + ftAmp Q B r (z : ℂ) ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
          / ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)) ^ (M + 1)
        + EM) :
    ((τ : ℂ)) ^ (M + 1) * FM
      = ((2 * (ftAmp Q B r (z : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
            * Complex.exp (((-(((M : ℝ) + 1) * θ) : ℝ) : ℂ) * I)).re : ℝ) : ℂ)
        + ((τ : ℂ)) ^ (M + 1) * EM := by
  have hpair := principal_pair_contribution (Q := Q) (B := B) hQ hB (r := r) (M := M)
    (z := z) (τ := τ) hroot
  rw [conj_polar τ θ] at hpair
  have hnorm : ((τ : ℂ)) ^ (M + 1)
      * (ftAmp Q B r (z : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
          / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1))
      = ftAmp Q B r (z : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
          * Complex.exp (((-(((M : ℝ) + 1) * θ) : ℝ) : ℂ) * I) := by
    rw [show ((τ : ℂ)) ^ (M + 1)
        * (ftAmp Q B r (z : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
            / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1))
        = ftAmp Q B r (z : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
            * (((τ : ℂ)) ^ (M + 1) / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1)) from by
      ring, ofReal_pow_div_principal_pow (M := M) (τ := τ) (θ := θ) hτ]
  rw [hexp, mul_add, mul_add, ← hnorm, hpair, hnorm]

/-- **`eq:W-endpoint-form` from the endpoint order alone.**  The same conclusion
as `Amplitude.amplitude_endpoint_form`, but with `γ_e ≠ 0` and
`1 ≤ rootMultiplicity` *derived* rather than assumed: the first from
`finiteEndpoint_leadingCoeff_pow` and the second from
`rootMultiplicity_pos_of_branch`.  What is supplied in their place is
`eq:z-endpoint-order`, which is what `Forgacs2017RationalDenominator` Prop. 3
produces by construction — its parameter is *defined* by `z - z_e = ε y^k`. -/
theorem amplitude_endpoint_form_of_order {Q B : Polynomial ℂ} (hB : B ≠ 0) {r : ℕ}
    (hr : 1 ≤ r) {γ zf c : ℝ → ℂ} {te γe : ℂ} (hte : te ≠ 0) (hγ0 : γ 0 = te)
    (hγ : HasDerivWithinAt γ γe (Set.Ici (0 : ℝ)) 0) (hP : ftDen Q r (zf 0) ≠ 0)
    (hc : ContinuousWithinAt c (Set.Ici (0 : ℝ)) 0) (hc0 : c 0 ≠ 0)
    (hroot : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)),
      (ftDen Q r (zf δ)).eval (γ δ) = 0)
    (hz : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)),
      zf δ - zf 0 = (δ : ℂ) ^ ((ftDen Q r (zf 0)).rootMultiplicity te) * c δ) :
    ∃ V : ℝ → ℂ, ContinuousWithinAt V (Set.Ici (0 : ℝ)) 0 ∧ V 0 ≠ 0 ∧
      ∀ᶠ (δ : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ((δ : ℂ)) ^ ((ftDen Q r (zf 0)).rootMultiplicity te - 1)
            * ftAmp Q B r (zf δ) (γ δ)
          = ((δ : ℂ)) ^ B.rootMultiplicity te * V δ := by
  have hk : 1 ≤ (ftDen Q r (zf 0)).rootMultiplicity te :=
    rootMultiplicity_pos_of_branch hP hγ0 hroot
  obtain ⟨G, hfac, hG⟩ :=
    exists_endpointFactor (Q := Q) (r := r) (ze := zf 0) (te := te) hP
  have hmono : nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
      ≤ nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)) :=
    nhdsWithin_mono _ Set.Ioi_subset_Ici_self
  obtain ⟨-, hγe⟩ :=
    finiteEndpoint_leadingCoeff_pow hte hG hk hfac hγ0 hγ hc hc0 (hmono hroot) (hmono hz)
  exact amplitude_endpoint_form hB hr hte hγe hγ0 hγ hP hk (hmono hroot)


/-- **`eq:W-local-zero` on a whole subarc.**  `amplitude_local_zero` states the
factorization near `θ₀` because its root hypothesis is only eventual.  Where the
branch is a simple denominator zero *throughout* a compact subarc — which is the
compact-interior situation — the same `U` works on all of it, which is the form
`exists_amplitude_divisor_lower_bound` consumes. -/
theorem exists_amplitude_factor_on {Q B : Polynomial ℂ} (hB : B ≠ 0) {r : ℕ}
    {γ zf : ℝ → ℂ} {a b θ₀ : ℝ} {γ' : ℂ}
    (hγ : HasDerivAt γ γ' θ₀) (hγ' : γ' ≠ 0) (hzf : ContinuousAt zf θ₀)
    (hroot : ∀ θ ∈ Set.Icc a b, (ftDen Q r (zf θ)).eval (γ θ) = 0)
    (hsimple : ∀ θ ∈ Set.Icc a b, (derivative (ftDen Q r (zf θ))).eval (γ θ) ≠ 0)
    (hθ₀ : θ₀ ∈ Set.Icc a b) :
    ∃ U : ℝ → ℂ, ContinuousWithinAt U (Set.Icc a b) θ₀ ∧ U θ₀ ≠ 0 ∧
      ∀ θ ∈ Set.Icc a b,
        ftAmp Q B r (zf θ) (γ θ)
          = (((θ - θ₀ : ℝ)) : ℂ) ^ B.rootMultiplicity (γ θ₀) * U θ := by
  classical
  set ν := B.rootMultiplicity (γ θ₀) with hν
  set Bt := B /ₘ (X - C (γ θ₀)) ^ ν with hBt
  have hBfac : (X - C (γ θ₀)) ^ ν * Bt = B := pow_mul_divByMonic_rootMultiplicity_eq B _
  have hBtne : Bt.eval (γ θ₀) ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero _ hB
  set den : ℝ → ℂ := fun θ => (derivative (ftDen Q r (zf θ))).eval (γ θ) with hden
  have hdenne : den θ₀ ≠ 0 := hsimple θ₀ hθ₀
  have hdenc : ContinuousAt den θ₀ := continuousAt_eval_derivative_ftDen hγ.continuousAt hzf
  obtain ⟨h, hhc, hh0, hhmul⟩ := exists_linearFactor hγ
  refine ⟨fun θ => -((h θ) ^ ν * Bt.eval (γ θ)) / den θ, ?_, ?_, ?_⟩
  · exact (((hhc.pow ν).mul
      (((Polynomial.continuous Bt).continuousAt).comp hγ.continuousAt)).neg.div
      hdenc hdenne).continuousWithinAt
  · change -((h θ₀) ^ ν * Bt.eval (γ θ₀)) / den θ₀ ≠ 0
    rw [hh0]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hγ') hBtne)) hdenne
  · intro θ hθ
    have hBev : B.eval (γ θ) = (γ θ - γ θ₀) ^ ν * Bt.eval (γ θ) := by
      conv_lhs => rw [← hBfac]
      simp
    rw [ftAmp_eq_neg_div_derivative (hroot θ hθ), hBev, hhmul θ, mul_pow,
      show -((((θ : ℂ) - (θ₀ : ℂ)) ^ ν * (h θ) ^ ν) * Bt.eval (γ θ))
        = (((θ : ℂ) - (θ₀ : ℂ)) ^ ν) * (-((h θ) ^ ν * Bt.eval (γ θ))) by ring,
      mul_div_assoc]
    norm_cast

/-! ### `eq:amplitude-deletion` — the amplitude floor off the deleted windows -/

/-- A compact set on which `W` does not vanish carries a positive lower bound. -/
private theorem exists_floor_on_compact {W : ℝ → ℂ} {T : Set ℝ} (hT : IsCompact T)
    (hWc : ContinuousOn W T) (hne : ∀ θ ∈ T, W θ ≠ 0) :
    ∃ m > (0 : ℝ), ∀ θ ∈ T, m ≤ ‖W θ‖ := by
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨θ₀, hθ₀, hmin⟩ := hT.exists_isMinOn hTne hWc.norm
  exact ⟨‖W θ₀‖, norm_pos_iff.mpr (hne θ₀ hθ₀), fun θ hθ => hmin hθ⟩

/-- **`lem:amplitude-divisor` in product form.**  On a compact subarc the
amplitude is bounded below by its own divisor: `A·∏_j|θ-θ_j|^{ν_j} ≤ |W(θ)|`,
with the product over the amplitude zeros on the arc and `ν_j` their orders.

This is the primitive form of the interior amplitude supply.  It says nothing
about `M`; the deleted windows of `eq:amplitude-deletion` turn it into a floor by
bounding each `|θ - θ_j|` from below, and the `1/ν_j` in the window width is what
makes every factor contribute the same `e^{-cM}` whatever its order.

The proof is a collar decomposition: near a zero the factorization
`W = (θ-θ_j)^{ν_j}U_j` carries the vanishing and `U_j` is bounded below, while
the other factors are bounded above by the diameter; away from every zero `W` is
continuous and nonvanishing on a compact set.  No disjointness of the collars is
needed.  The number of zeros is bounded by `deg B` through
`amplitude_zero_count`, which is what makes `S` finite.
**Differs from the paper's route.**  `thm:weighted-dominance` chooses *pairwise disjoint*
neighborhoods of
the `θ_j` and raises `M_0` until every deleted window sits inside its own.  Here
the collars need not be disjoint and there is no threshold in `M`: the factors
away from the collar containing `θ` are bounded above by the arc's diameter
rather than separated from it, so one constant serves every `M`.  The conclusion
is correspondingly the `M`-free product form rather than the `e^{-cM}` floor.
-/
theorem exists_amplitude_divisor_lower_bound {a b : ℝ} {W : ℝ → ℂ} {S : Finset ℝ}
    {ν : ℝ → ℕ} {U : ℝ → ℝ → ℂ}
    (hWc : ContinuousOn W (Set.Icc a b)) (hSsub : ↑S ⊆ Set.Icc a b)
    (hzeros : ∀ θ ∈ Set.Icc a b, W θ = 0 → θ ∈ S)
    (hUc : ∀ θj ∈ S, ContinuousWithinAt (U θj) (Set.Icc a b) θj)
    (hU0 : ∀ θj ∈ S, U θj θj ≠ 0)
    (hUeq : ∀ θj ∈ S, ∀ θ ∈ Set.Icc a b, W θ = (((θ - θj : ℝ)) : ℂ) ^ ν θj * U θj θ) :
    ∃ A > (0 : ℝ), ∀ θ ∈ Set.Icc a b,
      A * ∏ θj ∈ S, |θ - θj| ^ ν θj ≤ ‖W θ‖ := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · have hWne : ∀ θ ∈ Set.Icc a b, W θ ≠ 0 := fun θ hθ hW0 => by
      simpa using hzeros θ hθ hW0
    obtain ⟨m, hmpos, hm⟩ := exists_floor_on_compact isCompact_Icc hWc hWne
    exact ⟨m, hmpos, fun θ hθ => by simpa using hm θ hθ⟩
  set D : ℝ := max (b - a) 1 with hDdef
  have hD1 : (1 : ℝ) ≤ D := le_max_right _ _
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hDbd : ∀ θ ∈ Set.Icc a b, ∀ θk ∈ S, |θ - θk| ≤ D := by
    intro θ hθ θk hk
    have hk' : θk ∈ Set.Icc a b := hSsub hk
    refine le_trans ?_ (le_max_left _ _)
    rw [abs_le]
    constructor <;> [linarith [hθ.1, hk'.2]; linarith [hθ.2, hk'.1]]
  set Dp : ℝ := ∏ θk ∈ S, D ^ ν θk with hDpdef
  have hDp1 : (1 : ℝ) ≤ Dp := by
    rw [hDpdef]
    calc (1 : ℝ) = ∏ _θk ∈ S, (1 : ℝ) := by simp
      _ ≤ ∏ θk ∈ S, D ^ ν θk :=
          Finset.prod_le_prod (fun _ _ => zero_le_one) fun θk _ => one_le_pow₀ hD1
  have hDp0 : (0 : ℝ) < Dp := lt_of_lt_of_le one_pos hDp1
  have hprodle : ∀ θ ∈ Set.Icc a b, ∏ θk ∈ S, |θ - θk| ^ ν θk ≤ Dp := by
    intro θ hθ
    refine Finset.prod_le_prod (fun θk _ => by positivity) fun θk hk => ?_
    exact pow_le_pow_left₀ (abs_nonneg _) (hDbd θ hθ θk hk) _
  -- collars on which each cofactor stays above half its value at the zero
  have hball : ∀ θj : ℝ, ∃ ρj : ℝ, 0 < ρj ∧ (θj ∈ S → ∀ θ ∈ Set.Icc a b,
      |θ - θj| < ρj → ‖U θj θj‖ / 2 ≤ ‖U θj θ‖) := by
    intro θj
    by_cases hj : θj ∈ S
    · have hcont : ContinuousWithinAt (fun θ => ‖U θj θ‖) (Set.Icc a b) θj := (hUc θj hj).norm
      have hpos : ‖U θj θj‖ / 2 < ‖U θj θj‖ := by
        have := norm_pos_iff.mpr (hU0 θj hj); linarith
      have hev : ∀ᶠ θ in nhdsWithin θj (Set.Icc a b), ‖U θj θj‖ / 2 < ‖U θj θ‖ :=
        hcont (isOpen_Ioi.mem_nhds hpos)
      rw [eventually_nhdsWithin_iff] at hev
      obtain ⟨ρj, hρj, hb⟩ := Metric.eventually_nhds_iff.mp hev
      exact ⟨ρj, hρj, fun _ θ hθ hlt => le_of_lt (hb (by rwa [Real.dist_eq]) hθ)⟩
    · exact ⟨1, one_pos, fun h => absurd h hj⟩
  choose ρf hρf hρball using hball
  set ρ : ℝ := S.inf' hSne ρf with hρdef
  have hρpos : 0 < ρ := (Finset.lt_inf'_iff hSne).2 fun θj _ => hρf θj
  have hρle : ∀ θj ∈ S, ρ ≤ ρf θj := fun θj hj => Finset.inf'_le _ hj
  set uf : ℝ → ℝ := fun θj => ‖U θj θj‖ / 2 with hufdef
  set u : ℝ := S.inf' hSne uf with hudef
  have hupos : 0 < u := by
    refine (Finset.lt_inf'_iff hSne).2 fun θj hj => ?_
    have := norm_pos_iff.mpr (hU0 θj hj)
    simp only [hufdef]; linarith
  have hule : ∀ θj ∈ S, u ≤ uf θj := fun θj hj => Finset.inf'_le _ hj
  -- the part of the arc away from every zero
  set T : Set ℝ := Set.Icc a b ∩ {θ : ℝ | ∀ θj ∈ S, ρ ≤ |θ - θj|} with hTdef
  have hTclosed : IsClosed {θ : ℝ | ∀ θj ∈ S, ρ ≤ |θ - θj|} := by
    have hrw : {θ : ℝ | ∀ θj ∈ S, ρ ≤ |θ - θj|} = ⋂ θj ∈ S, {θ : ℝ | ρ ≤ |θ - θj|} := by
      ext θ; simp
    rw [hrw]
    exact isClosed_biInter fun θj _ =>
      isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)
  have hTcpt : IsCompact T := isCompact_Icc.inter_right hTclosed
  have hWne : ∀ θ ∈ T, W θ ≠ 0 := by
    intro θ hθ hW0
    have h2 := hθ.2 θ (hzeros θ hθ.1 hW0)
    simp at h2
    linarith
  obtain ⟨m, hmpos, hm⟩ := exists_floor_on_compact hTcpt (hWc.mono Set.inter_subset_left) hWne
  refine ⟨min m u / Dp, by positivity, fun θ hθ => ?_⟩
  by_cases hfar : ∀ θj ∈ S, ρ ≤ |θ - θj|
  · calc min m u / Dp * ∏ θk ∈ S, |θ - θk| ^ ν θk
        ≤ min m u / Dp * Dp :=
          mul_le_mul_of_nonneg_left (hprodle θ hθ) (by positivity)
      _ = min m u := by field_simp
      _ ≤ m := min_le_left _ _
      _ ≤ ‖W θ‖ := hm θ ⟨hθ, hfar⟩
  · push Not at hfar
    obtain ⟨θj, hj, hlt⟩ := hfar
    have hUlow : uf θj ≤ ‖U θj θ‖ := hρball θj hj θ hθ (lt_of_lt_of_le hlt (hρle θj hj))
    have hsplit : ∏ θk ∈ S, |θ - θk| ^ ν θk
        = |θ - θj| ^ ν θj * ∏ θk ∈ S.erase θj, |θ - θk| ^ ν θk :=
      (Finset.mul_prod_erase S _ hj).symm
    have herase : ∏ θk ∈ S.erase θj, |θ - θk| ^ ν θk ≤ Dp := by
      calc ∏ θk ∈ S.erase θj, |θ - θk| ^ ν θk
          ≤ ∏ θk ∈ S.erase θj, D ^ ν θk :=
            Finset.prod_le_prod (fun θk _ => by positivity)
              (fun θk hk => pow_le_pow_left₀ (abs_nonneg _)
                (hDbd θ hθ θk (Finset.mem_of_mem_erase hk)) _)
        _ ≤ ∏ θk ∈ S, D ^ ν θk := by
            rw [← Finset.mul_prod_erase S (fun θk => D ^ ν θk) hj]
            have h1 : (1 : ℝ) ≤ D ^ ν θj := one_le_pow₀ hD1
            have h2 : (0 : ℝ) ≤ ∏ θk ∈ S.erase θj, D ^ ν θk :=
              Finset.prod_nonneg fun _ _ => by positivity
            nlinarith
        _ = Dp := rfl
    have hWval : ‖W θ‖ = |θ - θj| ^ ν θj * ‖U θj θ‖ := by
      rw [hUeq θj hj θ hθ, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [hsplit, hWval]
    calc min m u / Dp * (|θ - θj| ^ ν θj * ∏ θk ∈ S.erase θj, |θ - θk| ^ ν θk)
        ≤ min m u / Dp * (|θ - θj| ^ ν θj * Dp) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left herase (by positivity)
      _ = min m u * |θ - θj| ^ ν θj := by field_simp
      _ ≤ ‖U θj θ‖ * |θ - θj| ^ ν θj := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact le_trans (min_le_right _ _) (le_trans (hule θj hj) hUlow)
      _ = |θ - θj| ^ ν θj * ‖U θj θ‖ := by ring

end ForgacsTran
