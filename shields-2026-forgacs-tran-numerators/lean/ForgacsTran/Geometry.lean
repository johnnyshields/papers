/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.AttractorPole

/-!
# Denominator pencil geometry

The denominator pencil `D(t,z) = Q(t) + z t^r` and the two algebraic facts the
whole section rests on.

## Main statements

* `eval_derivative_ftDen_of_isRoot` — `eq:Dprime-identity`, the elimination of
  `z` from `∂_t D` at a nonzero denominator zero.
* `ftCritical` — `E(t) = t Q'(t) - r Q(t)`, the `z`-free numerator of
  `t ∂_t D`.  `ftCritical_ftDen` is the elimination in polynomial form and
  `rootMultiplicity_ftCritical` is the order statement the endpoint exponent of
  `lem:amplitude-divisor` consumes: a denominator collision of multiplicity `k`
  at `t_e ≠ 0` makes `E` vanish there to order exactly `k - 1`.
* `eval_derivative_ftDen_eq_neg_gDeriv` — `∂_t D(t,z) = -t^r g'(t)` for
  `g(t) = -Q(t)/t^r`, which is `eq:W-on-g` before the numerator is divided in.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `subsec:FT-geometry`,
`thm:FT-geometry`, `eq:Dprime-identity`).

## Tags

denominator pencil, critical polynomial, root multiplicity
-/

namespace ForgacsTran

open Polynomial

theorem ftDen_eq_zero_iff_ftBranch {Q : Polynomial ℂ} {r : ℕ} {z t : ℂ} (ht : t ≠ 0) :
    (ftDen Q r z).eval t = 0 ↔ z = ftBranch (fun s => Q.eval s) r t := by
  have := ftDenomFn_eq_zero_iff (fun s => Q.eval s) r (z := z) ht
  simpa [ftDenomFn] using this

/-- `∂_t D(t,z) = Q'(t) + r z t^{r-1}`. -/
theorem eval_derivative_ftDen_formula (Q : Polynomial ℂ) (r : ℕ) (z t : ℂ) :
    (derivative (ftDen Q r z)).eval t
      = (derivative Q).eval t + (r : ℂ) * z * t ^ (r - 1) := by
  simp only [ftDen, derivative_add, derivative_C_mul, derivative_X_pow, eval_add,
    eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- **`eq:Dprime-identity`.**  At a *nonzero* denominator zero the spectral
parameter drops out of `∂_t D`:
`Q'(t) + r z t^{r-1} = Q'(t) - r Q(t)/t`.

This is pure algebra from `z t^r = -Q(t)`; the paper uses it repeatedly, both for
the principal root and for a general cluster member. -/
theorem eval_derivative_ftDen_of_isRoot {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    {z t : ℂ} (ht : t ≠ 0) (hroot : (ftDen Q r z).eval t = 0) :
    (derivative (ftDen Q r z)).eval t = (derivative Q).eval t - (r : ℂ) * Q.eval t / t := by
  have hpow : t * t ^ (r - 1) = t ^ r := by
    conv_rhs => rw [show r = 1 + (r - 1) by omega]
    rw [pow_add, pow_one]
  rw [ftDen_eval] at hroot
  have key : z * t ^ (r - 1) = -Q.eval t / t := by
    rw [eq_div_iff ht]
    calc z * t ^ (r - 1) * t = z * (t * t ^ (r - 1)) := by ring
      _ = z * t ^ r := by rw [hpow]
      _ = -Q.eval t := by linear_combination hroot
  rw [eval_derivative_ftDen_formula, mul_assoc, key]
  ring

/-- **`eq:Dprime-identity`, polynomial form.**  `E(t) = t Q'(t) - r Q(t)`: the
`z`-free numerator of `t ∂_t D(t,z)`.  Its zeros off the origin are the critical
points of `g(t) = -Q(t)/t^r`, which is how `eq:ab-def` reads the endpoints of
`I_{Q,r}` off `t^{r-1}(rQ(t) - tQ'(t))`. -/
noncomputable def ftCritical (Q : Polynomial ℂ) (r : ℕ) : Polynomial ℂ :=
  X * derivative Q - C (r : ℂ) * Q

@[simp] theorem eval_ftCritical (Q : Polynomial ℂ) (r : ℕ) (t : ℂ) :
    (ftCritical Q r).eval t = t * (derivative Q).eval t - (r : ℂ) * Q.eval t := by
  simp [ftCritical]

/-- **The elimination, in polynomial form.**  `E` is unchanged by the pencil:
`t D'(t,z) - r D(t,z) = t Q'(t) - r Q(t)`, the `z t^r` terms cancelling exactly.
Everything the paper deduces from `eq:Dprime-identity` about the *order* of the
derivative factor is therefore a statement about the single polynomial `E`. -/
theorem ftCritical_ftDen (Q : Polynomial ℂ) {r : ℕ} (hr : 1 ≤ r) (z : ℂ) :
    ftCritical (ftDen Q r z) r = ftCritical Q r := by
  have hpow : (X : Polynomial ℂ) * X ^ (r - 1) = X ^ r := by
    conv_rhs => rw [show r = 1 + (r - 1) by omega]
    rw [pow_add, pow_one]
  have hd : derivative (ftDen Q r z) = derivative Q + C z * (C (r : ℂ) * X ^ (r - 1)) := by
    simp [ftDen, derivative_X_pow]
  have key : (X : Polynomial ℂ) * (C z * (C (r : ℂ) * X ^ (r - 1)))
      = C (r : ℂ) * (C z * X ^ r) := by
    rw [show (X : Polynomial ℂ) * (C z * (C (r : ℂ) * X ^ (r - 1)))
        = C (r : ℂ) * C z * (X * X ^ (r - 1)) by ring, hpow]
    ring
  rw [ftCritical, ftCritical, hd, ftDen]
  linear_combination key

/-- **`eq:Dprime-identity` as a quotient.**  At a nonzero denominator zero,
`∂_t D(t,z) = E(t)/t`. -/
theorem eval_derivative_ftDen_eq_ftCritical_div {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    {z t : ℂ} (ht : t ≠ 0) (hroot : (ftDen Q r z).eval t = 0) :
    (derivative (ftDen Q r z)).eval t = (ftCritical Q r).eval t / t := by
  rw [eval_derivative_ftDen_of_isRoot hr ht hroot, eval_ftCritical]
  field_simp


/-- **`eq:W-on-g`, the denominator half.**  At a nonzero denominator zero,
`∂_t D(t,z) = -t^r g'(t)` for the fiber map `g(t) = -Q(t)/t^r`.  This is what
turns the residue form `eq:residue-amplitude` of the amplitude into its form on
the denominator curve. -/
theorem hasDerivAt_ftBranch_ftDen {Q : Polynomial ℂ} {r : ℕ} {z t : ℂ} (ht : t ≠ 0)
    (hroot : (ftDen Q r z).eval t = 0) :
    HasDerivAt (ftBranch (fun s => Q.eval s) r)
      (-(derivative (ftDen Q r z)).eval t / t ^ r) t := by
  have hz : z = ftBranch (fun s => Q.eval s) r t := (ftDen_eq_zero_iff_ftBranch ht).1 hroot
  have h := deriv_ftBranch (Q := fun s => Q.eval s) (r := r) (t₀ := t) (analyticAt_eval Q t) ht
  have hD : ftDenomFnDeriv (fun s => Q.eval s) r t = (derivative (ftDen Q r z)).eval t := by
    rw [ftDenomFnDeriv, eval_derivative_ftDen_formula, ← hz, Polynomial.deriv]
    ring
  rwa [hD] at h

/-- `t^r g'(t) = -∂_t D(t,z)` at a nonzero denominator zero. -/
theorem eval_derivative_ftDen_eq_neg_gDeriv {Q : Polynomial ℂ} {r : ℕ} {z t : ℂ} (ht : t ≠ 0)
    (hroot : (ftDen Q r z).eval t = 0) :
    (derivative (ftDen Q r z)).eval t
      = -(t ^ r * deriv (ftBranch (fun s => Q.eval s) r) t) := by
  rw [(hasDerivAt_ftBranch_ftDen ht hroot).deriv]
  field_simp

/-- **The order of the derivative factor at an endpoint collision.**  If the
denominator `D(·,z_e)` has a zero of multiplicity `k ≥ 1` at `t_e ≠ 0`, then
`E(t) = t Q'(t) - r Q(t)` factors as `(t - t_e)^{k-1} H(t)` with `H(t_e) ≠ 0`.

The paper reads this as "`z_e - g(t)` vanishes to order `k` at `t_e`, so
`t^r g'(t)` vanishes there to order `k-1`" in the proof of
`lem:amplitude-divisor`; `ftCritical_ftDen` makes it a statement about a
single polynomial, and the factorization is what the endpoint exponent
`p = ν - (k-1)` of `eq:W-endpoint-form` is computed from. -/
theorem exists_ftCritical_factor {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r) {z te : ℂ}
    (hte : te ≠ 0) (hP : ftDen Q r z ≠ 0)
    (hk : 1 ≤ (ftDen Q r z).rootMultiplicity te) :
    ∃ H : Polynomial ℂ,
      ftCritical Q r = (X - C te) ^ ((ftDen Q r z).rootMultiplicity te - 1) * H ∧
        H.eval te ≠ 0 := by
  set P := ftDen Q r z with hPdef
  set k := P.rootMultiplicity te with hkdef
  set G := P /ₘ (X - C te) ^ k with hGdef
  have hfac : (X - C te) ^ k * G = P := pow_mul_divByMonic_rootMultiplicity_eq P te
  have hG : G.eval te ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero te hP
  have hsplit : (X - C te) ^ k = (X - C te) ^ (k - 1) * (X - C te) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  refine ⟨X * C (k : ℂ) * G + (X - C te) * (X * derivative G - C (r : ℂ) * G), ?_, ?_⟩
  · have hdP : derivative P
        = C (k : ℂ) * (X - C te) ^ (k - 1) * G + (X - C te) ^ k * derivative G := by
      rw [← hfac, derivative_mul, derivative_pow]
      simp
    rw [← ftCritical_ftDen Q hr z, ← hPdef, ftCritical, hdP, ← hfac, hsplit]
    ring
  · have hkne : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
    exact mul_ne_zero (mul_ne_zero hte hkne) hG

/-- **`lem:amplitude-divisor`, the order of `E` at a collision.**  A denominator
collision of multiplicity `k` at `t_e ≠ 0` makes `E(t) = t Q'(t) - r Q(t)` vanish
there to order exactly `k - 1`.
**Differs from the paper's route.**  `lem:amplitude-divisor` reads this order off the fiber map:
`z_e -
g(t)` vanishes to order `k` at `t_e`, hence `t^r g'(t)` to order `k-1`.  Here it
is a statement about the single polynomial `E`, whose independence of `z` is
`ftCritical_ftDen`, so the order is exact arithmetic on a factorization and no
derivative of a quotient is formed.
-/
theorem rootMultiplicity_ftCritical {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r) {z te : ℂ}
    (hte : te ≠ 0) (hP : ftDen Q r z ≠ 0)
    (hk : 1 ≤ (ftDen Q r z).rootMultiplicity te) :
    (ftCritical Q r).rootMultiplicity te = (ftDen Q r z).rootMultiplicity te - 1 := by
  obtain ⟨H, hfac, hH⟩ := exists_ftCritical_factor hr hte hP hk
  have hHne : H ≠ 0 := fun h => hH (by simp [h])
  have hpne : ((X - C te) ^ ((ftDen Q r z).rootMultiplicity te - 1) : Polynomial ℂ) ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero te)
  have hH0 : rootMultiplicity te H = 0 := rootMultiplicity_eq_zero hH
  rw [hfac, rootMultiplicity_mul (mul_ne_zero hpne hHne), rootMultiplicity_X_sub_C_pow, hH0,
    add_zero]



/-- **`exists_linearFactor` on a closed half-window.**  The same factorization from
a one-sided derivative, with the conclusion one-sided to match.

`Set.Ici` and not `Set.Ioi`: the cofactor's value *at* `a` is `f'`, and that value
is what every consumer uses, so a derivative on the punctured side alone would
say nothing there.  A branch parameterized by its distance to an endpoint has no
two-sided derivative — `τ` is even, so the one-sided quotients are exact
negatives — which is why the two-sided form is unusable at an endpoint however
natural it looks. -/
theorem exists_linearFactor_within {f : ℝ → ℂ} {a : ℝ} {f' : ℂ}
    (hf : HasDerivWithinAt f f' (Set.Ici a) a) :
    ∃ h : ℝ → ℂ, ContinuousWithinAt h (Set.Ici a) a ∧ h a = f' ∧
      ∀ x : ℝ, f x - f a = ((x : ℂ) - (a : ℂ)) * h x := by
  classical
  refine ⟨fun x => if x = a then f' else (f x - f a) / ((x : ℂ) - (a : ℂ)), ?_, by simp, ?_⟩
  · have hval : (if a = a then f' else (f a - f a) / ((a : ℂ) - (a : ℂ))) = f' := by simp
    have hf' : HasDerivWithinAt f f' (Set.Ioi a) a := hf.mono Set.Ioi_subset_Ici_self
    have hlim : Filter.Tendsto
        (fun x => if x = a then f' else (f x - f a) / ((x : ℂ) - (a : ℂ)))
        (nhdsWithin a (Set.Ioi a)) (nhds f') := by
      refine ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hf').congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : ¬ (x = a) := ne_of_gt hx
      simp only [if_neg hx', slope_def_module, Complex.real_smul,
        Complex.ofReal_inv, Complex.ofReal_sub, div_eq_inv_mul]
    have hIoi : ContinuousWithinAt
        (fun x => if x = a then f' else (f x - f a) / ((x : ℂ) - (a : ℂ)))
        (Set.Ioi a) a := by
      rw [ContinuousWithinAt, hval]; exact hlim
    rw [← Set.Ioi_union_left]
    exact hIoi.union continuousWithinAt_singleton
  · intro x
    by_cases hx : x = a
    · simp [hx]
    · have hne : ((x : ℂ) - (a : ℂ)) ≠ 0 := by
        simpa [sub_eq_zero, Complex.ofReal_inj] using hx
      simp only [if_neg hx]
      field_simp

/-- **The linear factor of a differentiable germ.**  `f x - f a = (x - a) h x` with
`h` continuous at `a` and `h a = f'`.  This is how every `O(δ²)` expansion in the
endpoint analysis is carried without a Landau symbol: the remainder lives in the
continuity of `h`, and `h a ≠ 0` is the nonvanishing of the leading coefficient. -/
theorem exists_linearFactor {f : ℝ → ℂ} {a : ℝ} {f' : ℂ} (hf : HasDerivAt f f' a) :
    ∃ h : ℝ → ℂ, ContinuousAt h a ∧ h a = f' ∧
      ∀ x : ℝ, f x - f a = ((x : ℂ) - (a : ℂ)) * h x := by
  classical
  refine ⟨fun x => if x = a then f' else (f x - f a) / ((x : ℂ) - (a : ℂ)), ?_, by simp, ?_⟩
  · refine continuousWithinAt_compl_self.mp ?_
    have hval : (if a = a then f' else (f a - f a) / ((a : ℂ) - (a : ℂ))) = f' := by simp
    have hlim : Filter.Tendsto
        (fun x => if x = a then f' else (f x - f a) / ((x : ℂ) - (a : ℂ)))
        (nhdsWithin a ({a}ᶜ : Set ℝ)) (nhds f') := by
      refine (hasDerivAt_iff_tendsto_slope.mp hf).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : ¬ (x = a) := hx
      simp only [if_neg hx', slope_def_module, Complex.real_smul,
        Complex.ofReal_inv, Complex.ofReal_sub, div_eq_inv_mul]
    rw [ContinuousWithinAt, hval]
    exact hlim
  · intro x
    by_cases hx : x = a
    · simp [hx]
    · have hne : ((x : ℂ) - (a : ℂ)) ≠ 0 := by
        simpa [sub_eq_zero, Complex.ofReal_inj] using hx
      simp only [if_neg hx]
      field_simp

/-! ### Endpoint separation

`thm:FT-geometry` imports the parameterization and the endpoint expansions from
`Forgacs2017RationalDenominator`; what the paper adds is the *uniform*
separation extracted from them.  The sign fact that does the work is that among
the `ρ`-th roots of `-1` the principal pair `e^{±iπ/ρ}` is the unique maximizer
of the real part, so the linear coefficient
`(cos(π/ρ) - Re ω_j)/sin(π/ρ)` vanishes exactly there. -/

/-- A root of `-1` has modulus one. -/
theorem norm_eq_one_of_pow_eq_neg_one {ρ : ℕ} (hρ : 1 ≤ ρ) {ω : ℂ} (hω : ω ^ ρ = -1) :
    ‖ω‖ = 1 := by
  have h1 : ‖ω‖ ^ ρ = 1 := by rw [← norm_pow, hω, norm_neg, norm_one]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : ‖ω‖ ^ ρ < 1 := pow_lt_one₀ (norm_nonneg _) h (by omega)
    linarith
  · have : 1 < ‖ω‖ ^ ρ := one_lt_pow₀ h (by omega)
    linarith

/-- The argument of a `ρ`-th root of `-1` is an odd multiple of `π/ρ`; in
particular its modulus is at least `π/ρ`. -/
theorem pi_div_le_abs_arg_of_pow_eq_neg_one {ρ : ℕ} (hρ : 1 ≤ ρ) {ω : ℂ} (hω : ω ^ ρ = -1) :
    Real.pi / ρ ≤ |ω.arg| := by
  have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hnorm : ‖ω‖ = 1 := norm_eq_one_of_pow_eq_neg_one hρ hω
  have hωne : ω ≠ 0 := by intro h; rw [h] at hnorm; simp at hnorm
  have hpolar : ω = Complex.exp ((ω.arg : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ω]
    rw [hnorm]; simp
  have hexp : Complex.exp (((ρ : ℂ)) * ((ω.arg : ℂ) * Complex.I))
      = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [Complex.exp_nat_mul, ← hpolar, hω, Complex.exp_pi_mul_I]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
  have h3 : (((ρ : ℝ) * ω.arg : ℝ) : ℂ) * Complex.I
      = ((Real.pi + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    push_cast
    linear_combination hn
  have h4 : (ρ : ℝ) * ω.arg = Real.pi + n * (2 * Real.pi) := by
    have := mul_right_cancel₀ Complex.I_ne_zero h3
    exact_mod_cast this
  have h5 : (ρ : ℝ) * ω.arg = ((2 * n + 1 : ℤ) : ℝ) * Real.pi := by push_cast; linarith
  have habs : (1 : ℝ) ≤ |((2 * n + 1 : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |2 * n + 1| := Int.one_le_abs (by omega)
    calc (1:ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|2 * n + 1| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |((2 * n + 1 : ℤ) : ℝ)| := by push_cast [Int.cast_abs]; ring_nf
  have hkey : (ρ : ℝ) * |ω.arg| = |((2 * n + 1 : ℤ) : ℝ)| * Real.pi := by
    rw [← abs_of_pos hρ0, ← abs_mul, h5, abs_mul, abs_of_pos Real.pi_pos]
  rw [div_le_iff₀ hρ0, mul_comm]
  calc Real.pi = 1 * Real.pi := (one_mul _).symm
    _ ≤ |((2 * n + 1 : ℤ) : ℝ)| * Real.pi := by
        exact mul_le_mul_of_nonneg_right habs Real.pi_pos.le
    _ = (ρ : ℝ) * |ω.arg| := hkey.symm

/-- **The sign fact behind `eq:endpoint-linear-gap`.**  Among the `ρ`-th roots
of `-1`, `cos(π/ρ)` bounds the real part, and equality forces the principal
pair. -/
theorem re_le_cos_pi_div {ρ : ℕ} (hρ : 1 ≤ ρ) {ω : ℂ} (hω : ω ^ ρ = -1) :
    ω.re ≤ Real.cos (Real.pi / ρ) := by
  have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hnorm : ‖ω‖ = 1 := norm_eq_one_of_pow_eq_neg_one hρ hω
  have hωne : ω ≠ 0 := by intro h; rw [h] at hnorm; simp at hnorm
  have hre : Real.cos ω.arg = ω.re := by
    rw [Complex.cos_arg hωne, hnorm, div_one]
  have hlow : Real.pi / ρ ≤ |ω.arg| := pi_div_le_abs_arg_of_pow_eq_neg_one hρ hω
  have hhigh : |ω.arg| ≤ Real.pi := Complex.abs_arg_le_pi ω
  have : Real.cos |ω.arg| ≤ Real.cos (Real.pi / ρ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hhigh hlow
  rwa [Real.cos_abs, hre] at this

/-- The strict half: a *nonprincipal* `ρ`-th root of `-1` has real part strictly
below `cos(π/ρ)`. -/
theorem re_lt_cos_pi_div {ρ : ℕ} (hρ : 1 ≤ ρ) {ω : ℂ} (hω : ω ^ ρ = -1)
    (hne : ω ≠ Complex.exp (((Real.pi / ρ : ℝ) : ℂ) * Complex.I))
    (hne' : ω ≠ Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * Complex.I)) :
    ω.re < Real.cos (Real.pi / ρ) := by
  have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hnorm : ‖ω‖ = 1 := norm_eq_one_of_pow_eq_neg_one hρ hω
  have hωne : ω ≠ 0 := by intro h; rw [h] at hnorm; simp at hnorm
  have hpolar : ω = Complex.exp ((ω.arg : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ω]
    rw [hnorm]; simp
  have hlow : Real.pi / ρ ≤ |ω.arg| := pi_div_le_abs_arg_of_pow_eq_neg_one hρ hω
  have hhigh : |ω.arg| ≤ Real.pi := Complex.abs_arg_le_pi ω
  have hstrict : Real.pi / ρ < |ω.arg| := by
    rcases lt_or_eq_of_le hlow with h | h
    · exact h
    · exfalso
      rcases abs_eq (by positivity : (0:ℝ) ≤ Real.pi / ρ) |>.1 h.symm with h1 | h1
      · exact hne (by rw [hpolar, h1])
      · exact hne' (by rw [hpolar, h1])
  have hre : Real.cos ω.arg = ω.re := by rw [Complex.cos_arg hωne, hnorm, div_one]
  have : Real.cos |ω.arg| < Real.cos (Real.pi / ρ) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) hhigh hstrict
  rwa [Real.cos_abs, hre] at this

/-- **`eq:endpoint-linear-gap`, the linear coefficient.**  For `ρ ≥ 2` the
coefficient `(cos(π/ρ) - Re ω_j)/sin(π/ρ)` of the normalized cluster expansion
is strictly positive at every nonprincipal index. -/
theorem endpoint_linear_coeff_pos {ρ : ℕ} (hρ : 2 ≤ ρ) {ω : ℂ} (hω : ω ^ ρ = -1)
    (hne : ω ≠ Complex.exp (((Real.pi / ρ : ℝ) : ℂ) * Complex.I))
    (hne' : ω ≠ Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * Complex.I)) :
    0 < (Real.cos (Real.pi / ρ) - ω.re) / Real.sin (Real.pi / ρ) := by
  have hρ0 : (0 : ℝ) < ρ := by positivity
  have hlt : Real.pi / ρ < Real.pi := by
    rw [div_lt_iff₀ hρ0]
    calc Real.pi = Real.pi * 1 := (mul_one _).symm
      _ < Real.pi * ρ := by
          exact mul_lt_mul_of_pos_left (by exact_mod_cast (by omega : 1 < ρ)) Real.pi_pos
  have hsin : 0 < Real.sin (Real.pi / ρ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) hlt
  exact div_pos (sub_pos.mpr (re_lt_cos_pi_div (by omega) hω hne hne')) hsin

/-- **`eq:endpoint-linear-gap`.**  A finite cluster whose normalized members
expand as `ζ_j(δ) = 1 + c_jδ + O(δ²)` with every `c_j > 0` obeys a single linear
modulus gap `|ζ_j(δ)| ≥ 1 + c_0δ`, uniformly in `j` and in `δ` small.  Finiteness
of the cluster is what makes the positive coefficients have a positive minimum,
and it is the whole of the paper's extraction step. -/
theorem exists_endpoint_linear_gap {ι : Type*} {J : Finset ι} {ζ : ι → ℝ → ℂ} {cf : ι → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hcf : ∀ j ∈ J, 0 < cf j)
    (hexp : ∀ j ∈ J, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ‖ζ j δ - ((1 + cf j * δ : ℝ) : ℂ)‖ ≤ C * δ ^ 2) :
    ∃ c₀ > 0, ∃ δ₀ > 0, ∀ j ∈ J, ∀ δ : ℝ, 0 < δ → δ < δ₀ → 1 + c₀ * δ ≤ ‖ζ j δ‖ := by
  classical
  obtain ⟨cmin, hcmin_pos, hcmin⟩ : ∃ c : ℝ, 0 < c ∧ ∀ j ∈ J, c ≤ cf j := by
    rcases J.eq_empty_or_nonempty with rfl | hJ
    · exact ⟨1, one_pos, by simp⟩
    · exact ⟨J.inf' hJ cf, (Finset.lt_inf'_iff hJ).2 hcf, fun j hj => Finset.inf'_le _ hj⟩
  refine ⟨cmin / 2, by positivity, min 1 (cmin / (2 * (C + 1))), by positivity, ?_⟩
  intro j hj δ hδ hδ₀
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδ₀ (min_le_left _ _))
  have hδC : δ < cmin / (2 * (C + 1)) := lt_of_lt_of_le hδ₀ (min_le_right _ _)
  have hbound := hexp j hj δ hδ hδ1
  have hpos : (0 : ℝ) < 1 + cf j * δ := by nlinarith [hcf j hj]
  have hnorm1 : ‖((1 + cf j * δ : ℝ) : ℂ)‖ = 1 + cf j * δ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have hlow : 1 + cf j * δ - C * δ ^ 2 ≤ ‖ζ j δ‖ := by
    have := norm_sub_norm_le (((1 + cf j * δ : ℝ) : ℂ)) (ζ j δ)
    rw [hnorm1] at this
    rw [← norm_neg (((1 + cf j * δ : ℝ) : ℂ) - ζ j δ), neg_sub] at this
    linarith [this, hbound]
  have hcj : cmin ≤ cf j := hcmin j hj
  have hCδ : C * δ ≤ cmin / 2 := by
    have h1 : C * δ ≤ (C + 1) * δ := by nlinarith
    have h2 : (C + 1) * δ < (C + 1) * (cmin / (2 * (C + 1))) :=
      mul_lt_mul_of_pos_left hδC (by positivity)
    have h3 : (C + 1) * (cmin / (2 * (C + 1))) = cmin / 2 := by field_simp
    linarith
  nlinarith [hlow, hCδ, hδ, hcj]



/-- **`eq:endpoint-linear-gap` from the expansion in modulus.**  The same
conclusion as `exists_endpoint_linear_gap`, but taking the hypothesis on
`‖ζ_j(δ)‖` rather than on `ζ_j(δ)` itself.

This is the form the endpoint expansion can actually supply.
`Forgacs2017RationalDenominator` Prop. 3 gives `ζ_j(θ) = 1 + c_jθ + O(θ²)` with
`c_j = (cos(π/ρ) - ω_j)/sin(π/ρ)` **complex**, so `ζ_j(δ) - (1 + (Re c_j)δ)` is of
exact order `δ` whenever `ω_j` is nonreal and no `O(δ²)` bound on it can hold.
It is the modulus that satisfies the real-coefficient bound, and
`FTMinModulus.abs_norm_sub_one_add_re_mul_le` is the passage from one to the
other.

The window is supplied rather than fixed at `(0,1]`, because every supplier
produces its own: the cluster's members exist only for small `δ`, so the
expansion holds where the family exists.  `weighted_dominance_of_branch`'s
`hexp₁` is stated on its own `e₁` for that reason, and this is what it calls. -/
theorem exists_endpoint_linear_gap_of_norm_on {ι : Type*} {J : Finset ι} {ζ : ι → ℝ → ℂ}
    {cf : ι → ℝ} {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hcf : ∀ j ∈ J, 0 < cf j)
    (hexp : ∀ j ∈ J, ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      |‖ζ j δ‖ - (1 + cf j * δ)| ≤ C * δ ^ 2) :
    ∃ c₀ > 0, ∃ δ₀ > 0, ∀ j ∈ J, ∀ δ : ℝ, 0 < δ → δ < δ₀ → 1 + c₀ * δ ≤ ‖ζ j δ‖ := by
  classical
  obtain ⟨cmin, hcmin_pos, hcmin⟩ : ∃ c : ℝ, 0 < c ∧ ∀ j ∈ J, c ≤ cf j := by
    rcases J.eq_empty_or_nonempty with rfl | hJ
    · exact ⟨1, one_pos, by simp⟩
    · exact ⟨J.inf' hJ cf, (Finset.lt_inf'_iff hJ).2 hcf, fun j hj => Finset.inf'_le _ hj⟩
  refine ⟨cmin / 2, by positivity, min ε (cmin / (2 * (C + 1))), by positivity, ?_⟩
  intro j hj δ hδ hδ₀
  have hδ1 : δ ≤ ε := le_of_lt (lt_of_lt_of_le hδ₀ (min_le_left _ _))
  have hδC : δ < cmin / (2 * (C + 1)) := lt_of_lt_of_le hδ₀ (min_le_right _ _)
  have hlow : 1 + cf j * δ - C * δ ^ 2 ≤ ‖ζ j δ‖ := by
    have := abs_le.1 (hexp j hj δ hδ hδ1)
    linarith [this.1]
  have hcj : cmin ≤ cf j := hcmin j hj
  have hCδ : C * δ ≤ cmin / 2 := by
    have h1 : C * δ ≤ (C + 1) * δ := by nlinarith
    have h2 : (C + 1) * δ < (C + 1) * (cmin / (2 * (C + 1))) :=
      mul_lt_mul_of_pos_left hδC (by positivity)
    have h3 : (C + 1) * (cmin / (2 * (C + 1))) = cmin / 2 := by field_simp
    linarith
  nlinarith [hlow, hCδ, hδ, hcj]

/-! ### `lem:amplitude-divisor`, the endpoint multiplicity `k`

`rootMultiplicity_ftCritical` already says `k - 1` is the multiplicity of `t_e`
as a zero of the `z`-free `E = ftCritical Q r`, so the lemma's `k` is a fact
about `E` alone.  What is added here is the value of that multiplicity at a zero
of `Q`, which is what turns `k` into `ρ`. -/

/-- `E = XQ' - rQ` factors through a zero of `Q` of multiplicity `ρ`: with
`Q = (X-x_1)^ρ q`, one has `E = (X-x_1)^{ρ-1}G` with
`G = ρ Xq + (X-x_1)(Xq' - rq)`, and `G(x_1) = ρ x_1q(x_1)`. -/
theorem ftCritical_factor_of_rootFactor {Q q : ℂ[X]} {x₁ : ℂ} {ρ r : ℕ} (hρ : 1 ≤ ρ)
    (hQ : Q = (X - C x₁) ^ ρ * q) :
    ftCritical Q r
      = (X - C x₁) ^ (ρ - 1)
        * (C (ρ : ℂ) * X * q + (X - C x₁) * (X * derivative q - C (r : ℂ) * q)) := by
  have hsplit : (X - C x₁) ^ ρ = (X - C x₁) ^ (ρ - 1) * (X - C x₁) := by
    conv_lhs => rw [show ρ = (ρ - 1) + 1 by omega]
    rw [pow_succ]
  have hd : derivative Q
      = C (ρ : ℂ) * (X - C x₁) ^ (ρ - 1) * q + (X - C x₁) ^ ρ * derivative q := by
    rw [hQ, derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C]
    ring
  rw [ftCritical, hd, hQ, hsplit]
  ring

/-- **`lem:amplitude-divisor`, `k = ρ` at a zero of `Q`.**  Where the endpoint
root `x_1` is a zero of `Q` of multiplicity `ρ`, the denominator's
multiplicity there is exactly `ρ`.  The `z` is not free: `x_1` being a
denominator root forces `z = -Q(x_1)/x_1^r = 0`, so the pencil member *is* `Q` —
but the proof does not need that, since `rootMultiplicity_ftCritical` reduces the
question to `E`, and `ftCritical_factor_of_rootFactor` evaluates it. -/
theorem rootMultiplicity_ftDen_eq_of_rootFactor {Q q : ℂ[X]} {x₁ : ℂ} {ρ r : ℕ}
    (hr : 1 ≤ r) (hρ : 1 ≤ ρ) (hx₁ : x₁ ≠ 0) (hQ : Q = (X - C x₁) ^ ρ * q)
    (hq : q.eval x₁ ≠ 0) {z : ℂ} (hP : ftDen Q r z ≠ 0)
    (hk : 1 ≤ (ftDen Q r z).rootMultiplicity x₁) :
    (ftDen Q r z).rootMultiplicity x₁ = ρ := by
  classical
  set G : ℂ[X] := C (ρ : ℂ) * X * q + (X - C x₁) * (X * derivative q - C (r : ℂ) * q) with hG
  have hGval : G.eval x₁ = (ρ : ℂ) * x₁ * q.eval x₁ := by simp [hG]
  have hρ0 : ((ρ : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hGne0 : G.eval x₁ ≠ 0 := by
    rw [hGval]; exact mul_ne_zero (mul_ne_zero hρ0 hx₁) hq
  have hGne : G ≠ 0 := fun h => hGne0 (by rw [h]; simp)
  have hfac := ftCritical_factor_of_rootFactor (Q := Q) (q := q) (r := r) hρ hQ
  have hEne : ftCritical Q r ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero x₁)) hGne
  have hprodne : (X - C x₁) ^ (ρ - 1) * G ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero x₁)) hGne
  have hEmul : (ftCritical Q r).rootMultiplicity x₁ = ρ - 1 := by
    rw [hfac, rootMultiplicity_mul hprodne, rootMultiplicity_X_sub_C_pow,
      rootMultiplicity_eq_zero hGne0, Nat.add_zero]
  have hrm := rootMultiplicity_ftCritical hr hx₁ hP hk
  omega

/-- **`lem:amplitude-divisor`, the `2` in `max\{ρ,2\}`.**  Any endpoint whose
root is a zero of the `z`-free `E` carries `k ≥ 2` — that is the whole content
of "the limiting principal root is a multiple zero", and it is why the exponent
never drops below `2` however simple the zero of `Q` is. -/
theorem two_le_rootMultiplicity_ftDen_of_ftCritical {Q : ℂ[X]} {r : ℕ} (hr : 1 ≤ r)
    {z te : ℂ} (hte : te ≠ 0) (hP : ftDen Q r z ≠ 0) (hEne : ftCritical Q r ≠ 0)
    (hk : 1 ≤ (ftDen Q r z).rootMultiplicity te)
    (hE : (ftCritical Q r).eval te = 0) :
    2 ≤ (ftDen Q r z).rootMultiplicity te := by
  have hpos : 0 < (ftCritical Q r).rootMultiplicity te :=
    (rootMultiplicity_pos hEne).2 hE
  have hrm := rootMultiplicity_ftCritical hr hte hP hk
  omega

/-- **`lem:amplitude-divisor`, the upper endpoint at `r = 1`: what `k ≥ 3`
costs.**  At `r = 1` the pencil member differs from `Q` by the linear `zt`, so
its second derivative *is* `Q''`.  A triple denominator root therefore forces
`Q''(t_e) = 0` — which is exactly the identity
`Forgacs2017RationalDenominator` Case 3 contradicts at `t_e ≤ 0`, since the
zeros of `Q''` are positive. -/
theorem eval_derivative_two_eq_zero_of_three_le_rootMultiplicity {Q : ℂ[X]} {z te : ℂ}
    (h : 3 ≤ (ftDen Q 1 z).rootMultiplicity te) :
    (derivative (derivative Q)).eval te = 0 := by
  have h2 : (derivative^[2] (ftDen Q 1 z)).IsRoot te :=
    isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega)
  have hd : derivative^[2] (ftDen Q 1 z) = derivative (derivative Q) := by
    simp [ftDen, Function.iterate_succ]
  rwa [hd] at h2

/-- **The positivity `Forgacs2017RationalDenominator` Case 3 runs on.**  A
product of factors `X + a` with every `a > 0` is positive at every `s ≥ 0`,
its derivative is positive as soon as there is one factor, and its second
derivative is positive as soon as there are two.  This is the normalized form of
"the zeros of `Q`, `Q'` and `Q''` are all positive": under `t = -s` a polynomial
with only positive zeros becomes this product, and `t ≤ 0` becomes `s ≥ 0`.

**Differs from the paper's route.**  The paper (and
`Forgacs2017RationalDenominator`) invokes the interlacing of the zeros of `Q'`
and `Q''` with those of `Q`.  Here nothing about zeros is used: the product rule
gives `R'' = 2R_0' + (X+a)R_0''` at each step, so the three sign facts prove
themselves together by induction on the factors, and no root-counting or Rolle
argument is needed.

The five clauses are one theorem because the strict `R''` step consumes the
strict `R'` of the tail: split into three lemmas, the `R''` induction has no
hypothesis strong enough to start from.  Do not factor it apart. -/
theorem posShiftProd_deriv_pos {xs : Multiset ℝ} (hxs : ∀ a ∈ xs, 0 < a) {s : ℝ}
    (hs : 0 ≤ s) :
    0 < ((xs.map (fun a : ℝ => X + C a)).prod).eval s
      ∧ (xs ≠ 0 → 0 < (derivative ((xs.map (fun a : ℝ => X + C a)).prod)).eval s)
      ∧ 0 ≤ (derivative ((xs.map (fun a : ℝ => X + C a)).prod)).eval s
      ∧ (2 ≤ Multiset.card xs →
          0 < (derivative (derivative ((xs.map (fun a : ℝ => X + C a)).prod))).eval s)
      ∧ 0 ≤ (derivative (derivative ((xs.map (fun a : ℝ => X + C a)).prod))).eval s := by
  induction xs using Multiset.induction_on with
  | empty => simp
  | cons a ys ih =>
    have ha : 0 < a := hxs a (Multiset.mem_cons_self a ys)
    have hys : ∀ b ∈ ys, 0 < b := fun b hb => hxs b (Multiset.mem_cons_of_mem hb)
    obtain ⟨hA, hC, hB, hE, hD⟩ := ih hys
    set R : ℝ[X] := (ys.map (fun a : ℝ => X + C a)).prod with hR
    have hmap : ((a ::ₘ ys).map (fun a : ℝ => X + C a)).prod = (X + C a) * R := by
      rw [Multiset.map_cons, Multiset.prod_cons]
    have hd1 : derivative ((X + C a) * R) = R + (X + C a) * derivative R := by
      rw [derivative_mul, derivative_add, derivative_X, derivative_C, add_zero, one_mul]
    have hd2 : derivative (derivative ((X + C a) * R))
        = 2 * derivative R + (X + C a) * derivative (derivative R) := by
      rw [hd1, derivative_add, derivative_mul, derivative_add, derivative_X, derivative_C,
        add_zero, one_mul]
      ring
    have hsa : 0 < s + a := by linarith
    have hev : ((X + C a) : ℝ[X]).eval s = s + a := by simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hmap, eval_mul, hev]; positivity
    · intro _
      rw [hmap, hd1, eval_add, eval_mul, hev]
      nlinarith [hA, hB, hsa]
    · rw [hmap, hd1, eval_add, eval_mul, hev]
      nlinarith [hA, hB, hsa]
    · intro hcard
      have hne : ys ≠ 0 := by
        intro h
        rw [h] at hcard
        simp at hcard
      have hBpos : 0 < (derivative R).eval s := hC hne
      rw [hmap, hd2, eval_add, eval_mul, eval_mul, hev]
      simp only [eval_ofNat]
      nlinarith [hBpos, hD, hsa]
    · rw [hmap, hd2, eval_add, eval_mul, eval_mul, hev]
      simp only [eval_ofNat]
      nlinarith [hB, hD, hsa]

/-- **The same induction on the factors as they actually appear.**  `Q` is
`c∏(a_k - t)`, not `c∏(t + a_k)`, and below every zero the signs are
uniform without any substitution: every factor is positive, so `R > 0`, `R' < 0`
and `R'' > 0`, the alternation coming from `\frac{d}{dt}(a - t) = -1` rather than
from any parity of the degree.  The hypothesis is `t < a` for every root `a`, of
which `t ≤ 0` under positive roots is the special case
`Forgacs2017RationalDenominator` Case 3 uses; the general form is what places the
smallest zero of `Q'` above the smallest zero of `Q`.  This is the form `ftRootPolyReal` presents,
so
it needs no `comp(-X)` transport; `posShiftProd_deriv_pos` is the same fact
normalized, and the two are stated separately because neither derives from the
other without that transport.

The five clauses are one theorem for the same reason as there: the strict `R''`
step consumes the strict `R'` of the tail. -/
theorem negShiftProd_deriv_sign {xs : Multiset ℝ} {t : ℝ} (ht : ∀ a ∈ xs, t < a) :
    0 < ((xs.map (fun a : ℝ => C a - X)).prod).eval t
      ∧ (xs ≠ 0 → (derivative ((xs.map (fun a : ℝ => C a - X)).prod)).eval t < 0)
      ∧ (derivative ((xs.map (fun a : ℝ => C a - X)).prod)).eval t ≤ 0
      ∧ (2 ≤ Multiset.card xs →
          0 < (derivative (derivative ((xs.map (fun a : ℝ => C a - X)).prod))).eval t)
      ∧ 0 ≤ (derivative (derivative ((xs.map (fun a : ℝ => C a - X)).prod))).eval t := by
  induction xs using Multiset.induction_on with
  | empty => simp
  | cons a ys ih =>
    have ha : t < a := ht a (Multiset.mem_cons_self a ys)
    have hys : ∀ b ∈ ys, t < b := fun b hb => ht b (Multiset.mem_cons_of_mem hb)
    obtain ⟨hA, hC, hB, hE, hD⟩ := ih hys
    set R : ℝ[X] := (ys.map (fun a : ℝ => C a - X)).prod with hR
    have hmap : ((a ::ₘ ys).map (fun a : ℝ => C a - X)).prod = (C a - X) * R := by
      rw [Multiset.map_cons, Multiset.prod_cons]
    have hd1 : derivative ((C a - X) * R) = -R + (C a - X) * derivative R := by
      rw [derivative_mul, derivative_sub, derivative_X, derivative_C, zero_sub]
      ring
    have hd2 : derivative (derivative ((C a - X) * R))
        = -(2 * derivative R) + (C a - X) * derivative (derivative R) := by
      rw [hd1, derivative_add, derivative_neg, derivative_mul, derivative_sub, derivative_X,
        derivative_C, zero_sub]
      ring
    have hat : 0 < a - t := by linarith
    have hev : ((C a - X) : ℝ[X]).eval t = a - t := by simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hmap, eval_mul, hev]; nlinarith [hA, hat]
    · intro _
      rw [hmap, hd1, eval_add, eval_neg, eval_mul, hev]
      nlinarith [hA, hB, hat]
    · rw [hmap, hd1, eval_add, eval_neg, eval_mul, hev]
      nlinarith [hA, hB, hat]
    · intro hcard
      have hne : ys ≠ 0 := by
        intro h; rw [h] at hcard; simp at hcard
      have hBneg : (derivative R).eval t < 0 := hC hne
      rw [hmap, hd2, eval_add, eval_neg, eval_mul, eval_mul, hev]
      simp only [eval_ofNat]
      nlinarith [hBneg, hD, hat]
    · rw [hmap, hd2, eval_add, eval_neg, eval_mul, eval_mul, hev]
      simp only [eval_ofNat]
      nlinarith [hB, hD, hat]

/-! ### `lem:amplitude-divisor` at the lower endpoint: locating the zeros of `Q'`

The `ρ = 1` case of `Forgacs2017RationalDenominator` Case 2 places the
endpoint between the smallest zeros of `Q` and of `Q'`.  The first half of that
is here: the smallest zero of `Q'` lies strictly between the smallest two
distinct zeros of `Q`.

**Differs from the paper's route.**  The classical statement is the interlacing
of the zeros of `Q'` with those of `Q`, proved by applying Rolle in every gap and
then counting degrees to see that those are all of them — which needs the zeros
of `Q` to be distinct.  Here only *one* gap is used, and nothing below it is
counted: `negShiftProd_deriv_sign` rules out a zero of `Q'` below the smallest
zero of `Q` by the same uniform-sign argument as at the upper endpoint, and Rolle
supplies one in the first gap.  **No degree count and no distinctness hypothesis
enter**, which matters because `eq:Q-hypotheses` does not give distinct zeros —
`ρ` is exactly the multiplicity the paper allows. -/

/-- Rolle between two zeros of a real polynomial. -/
theorem exists_eval_derivative_eq_zero_between {P : ℝ[X]} {x₁ x₂ : ℝ} (h12 : x₁ < x₂)
    (h1 : P.eval x₁ = 0) (h2 : P.eval x₂ = 0) :
    ∃ y ∈ Set.Ioo x₁ x₂, (derivative P).eval y = 0 := by
  obtain ⟨y, hy, hy0⟩ := exists_deriv_eq_zero (f := fun x : ℝ => P.eval x) h12
    (P.continuous_aeval.continuousOn) (by rw [h1, h2])
  exact ⟨y, hy, by rwa [Polynomial.deriv] at hy0⟩

/-- **`Q'` does not vanish below every zero of `Q`.**  The nonvanishing half of
the location statement, from the uniform-sign induction rather than from
counting. -/
theorem eval_derivative_ne_zero_of_lt_roots {xs : Multiset ℝ} (hne : xs ≠ 0) {c t : ℝ}
    (hc : c ≠ 0) (ht : ∀ a ∈ xs, t < a) :
    (derivative (C c * (xs.map (fun a : ℝ => C a - X)).prod)).eval t ≠ 0 := by
  obtain ⟨-, hstrict, -, -, -⟩ := negShiftProd_deriv_sign ht
  rw [derivative_C_mul, eval_mul, eval_C]
  exact mul_ne_zero hc (ne_of_lt (hstrict hne))

/-! ### The log-derivative of a root product

`Forgacs2017RationalDenominator` Case 2's `ρ = 1` obstruction is an identity
between `P`, `P'` and `P''` at an interior point.  Divided by `P(t) ≠ 0` it
becomes an identity between `S_1 = ∑(t-a)^{-1}` and `S_2 = ∑(t-a)^{-2}`,
which is where the sign of the interval enters.

Two Mathlib shapes to know here, both found the hard way.  `eval_multiset_sum`
does **not** exist at the pin — only `eval_multiset_prod` does, and the
symmetric name is the obvious wrong guess; the sum goes through
`map_multiset_sum (Polynomial.evalRingHom t)` after
`← Polynomial.coe_evalRingHom`.  And `HasDerivAt.sum` is `Finset`-only, so
`hasDerivAt_multiset_sum` below supplies the multiset form rather than routing
through `Multiset.toFinset`, which would collapse repeated roots. -/

/-- **`HasDerivAt` through a `Multiset` sum.**  Mathlib carries `HasDerivAt.sum`
for a `Finset` only; there is no `Multiset` counterpart at the pin, and
`Multiset.toFinset` is not a substitute here because it collapses repeated
roots, which `eq:Q-hypotheses` allows.  Two lines by induction on the multiset,
and reusable anywhere a root product is differentiated with multiplicity. -/
theorem hasDerivAt_multiset_sum {ι : Type*} {s : Multiset ι} {f : ι → ℝ → ℝ} {f' : ι → ℝ}
    {x : ℝ} (h : ∀ i ∈ s, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun y : ℝ => (s.map (fun i => f i y)).sum) ((s.map f').sum) x := by
  induction s using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const x (0 : ℝ)
  | cons a t ih =>
    have ha : HasDerivAt (f a) (f' a) x := h a (Multiset.mem_cons_self a t)
    have ht : ∀ i ∈ t, HasDerivAt (f i) (f' i) x := fun i hi =>
      h i (Multiset.mem_cons_of_mem hi)
    have hsum : HasDerivAt (fun y : ℝ => f a y + (t.map (fun i => f i y)).sum)
        (f' a + (t.map f').sum) x := HasDerivAt.add ha (ih ht)
    simpa [Multiset.map_cons, Multiset.sum_cons] using hsum

/-- `P'(t) = P(t)S_1(t)` at a non-root, with the roots counted with
multiplicity.  One application of `Polynomial.derivative_prod`; the erased
factor is restored by `Multiset.prod_map_erase`. -/
theorem eval_derivative_eq_mul_logDeriv {xs : Multiset ℝ} {c t : ℝ}
    (ht : ∀ a ∈ xs, t ≠ a) :
    (derivative (C c * (xs.map (fun a : ℝ => C a - X)).prod)).eval t
      = (C c * (xs.map (fun a : ℝ => C a - X)).prod).eval t
        * (xs.map (fun a : ℝ => (t - a)⁻¹)).sum := by
  classical
  set Q : ℝ[X] := (xs.map (fun a : ℝ => C a - X)).prod with hQ
  have hQe : Q.eval t = (xs.map (fun a : ℝ => a - t)).prod := by
    rw [hQ, eval_multiset_prod, Multiset.map_map]
    simp
  have hterm : ∀ a ∈ xs,
      (((xs.erase a).map (fun b : ℝ => C b - X)).prod * derivative (C a - X)).eval t
        = Q.eval t * (t - a)⁻¹ := by
    intro a ha
    have hne : a - t ≠ 0 := sub_ne_zero.2 (Ne.symm (ht a ha))
    have herase : ((xs.erase a).map (fun b : ℝ => C b - X)).prod.eval t
        = ((xs.erase a).map (fun b : ℝ => b - t)).prod := by
      rw [eval_multiset_prod, Multiset.map_map]
      simp
    have hsplit : (a - t) * ((xs.erase a).map (fun b : ℝ => b - t)).prod = Q.eval t := by
      rw [hQe]
      exact Multiset.prod_map_erase (f := fun b : ℝ => b - t) ha
    have htne : t - a ≠ 0 := sub_ne_zero.2 (ht a ha)
    rw [eval_mul, herase, derivative_sub, derivative_C, derivative_X, zero_sub, eval_neg,
      eval_one, ← hsplit]
    field
  have hsum : (derivative Q).eval t = Q.eval t * (xs.map (fun a : ℝ => (t - a)⁻¹)).sum := by
    rw [hQ, derivative_prod, ← Polynomial.coe_evalRingHom,
      map_multiset_sum (Polynomial.evalRingHom t), Multiset.map_map]
    have hcongr : (xs.map (⇑(Polynomial.evalRingHom t) ∘ fun a : ℝ =>
        ((xs.erase a).map (fun b : ℝ => C b - X)).prod * derivative (C a - X)))
        = xs.map (fun a : ℝ => Q.eval t * (t - a)⁻¹) :=
      Multiset.map_congr rfl (fun a ha => hterm a ha)
    rw [hcongr]
    exact Multiset.sum_map_mul_left
  rw [derivative_C_mul, eval_mul, eval_mul, eval_C, hsum]
  ring

/-- **`P''(t) = P(t)(S_1(t)^2 - S_2(t))` at a non-root.**

**Differs from the paper's route.**  The leave-two-out form of
`Polynomial.derivative_prod` would have to separate the diagonal terms — erasing
one element twice — from the off-diagonal ones, and repeated roots are the
normal case under `eq:Q-hypotheses`, not an edge one.  Here the first identity
is *differentiated* instead: `P' = P\,S_1` holds on the whole non-root set, which
is open, so the product rule gives `P'' = P\,S_1^2 + P\,S_1'` with `S_1' = -S_2`,
and the `S_1^2 - S_2` shape falls out rather than being assembled. -/
theorem eval_derivative_two_eq_mul_logDeriv {xs : Multiset ℝ} {c t : ℝ} (hc : c ≠ 0)
    (ht : ∀ a ∈ xs, t ≠ a) :
    (derivative (derivative (C c * (xs.map (fun a : ℝ => C a - X)).prod))).eval t
      = (C c * (xs.map (fun a : ℝ => C a - X)).prod).eval t
        * ((xs.map (fun a : ℝ => (t - a)⁻¹)).sum ^ 2
           - (xs.map (fun a : ℝ => ((t - a) ^ 2)⁻¹)).sum) := by
  classical
  set P : ℝ[X] := C c * (xs.map (fun a : ℝ => C a - X)).prod with hPdef
  -- a point is a root exactly when it meets one of the `a`
  have hnr : ∀ y : ℝ, P.eval y ≠ 0 → ∀ a ∈ xs, y ≠ a := by
    intro y hy a ha hya
    refine hy ?_
    rw [hPdef, eval_mul, eval_multiset_prod, Multiset.map_map]
    refine mul_eq_zero_of_right _ (Multiset.prod_eq_zero ?_)
    exact Multiset.mem_map.2 ⟨a, ha, by simp [hya]⟩
  have hPt : P.eval t ≠ 0 := by
    rw [hPdef, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    refine mul_ne_zero hc (Multiset.prod_ne_zero ?_)
    intro h0
    obtain ⟨a, ha, hae⟩ := Multiset.mem_map.1 h0
    exact ht a ha (by simpa [eq_comm, sub_eq_zero] using hae.symm)
  -- `S₁` is differentiable with derivative `-S₂`
  have hS : HasDerivAt (fun y : ℝ => (xs.map (fun a : ℝ => (y - a)⁻¹)).sum)
      ((xs.map (fun a : ℝ => -((t - a) ^ 2)⁻¹)).sum) t := by
    refine hasDerivAt_multiset_sum ?_
    intro a ha
    have hta : t - a ≠ 0 := sub_ne_zero.2 (ht a ha)
    have h1 : HasDerivAt (fun y : ℝ => y - a) 1 t := (hasDerivAt_id t).sub_const a
    have h2 : HasDerivAt (fun y : ℝ => (y - a)⁻¹) (-1 / (t - a) ^ 2) t := HasDerivAt.inv h1 hta
    have h3 : -1 / (t - a) ^ 2 = -((t - a) ^ 2)⁻¹ := by field_simp
    rwa [h3] at h2
  -- the first identity, on a neighborhood
  have hev : ∀ᶠ y : ℝ in nhds t,
      (derivative P).eval y = P.eval y * (xs.map (fun a : ℝ => (y - a)⁻¹)).sum := by
    have hcont : ContinuousAt (fun y : ℝ => P.eval y) t := P.continuousAt_aeval
    filter_upwards [hcont.eventually_ne hPt] with y hy
    exact eval_derivative_eq_mul_logDeriv (hnr y hy)
  -- differentiate it
  have hd1 : HasDerivAt (fun y : ℝ => (derivative P).eval y)
      ((derivative (derivative P)).eval t) t := (derivative P).hasDerivAt t
  have hprod : HasDerivAt
      (fun y : ℝ => P.eval y * (xs.map (fun a : ℝ => (y - a)⁻¹)).sum)
      ((derivative P).eval t * (xs.map (fun a : ℝ => (t - a)⁻¹)).sum
        + P.eval t * (xs.map (fun a : ℝ => -((t - a) ^ 2)⁻¹)).sum) t :=
    HasDerivAt.mul (P.hasDerivAt t) hS
  have hEq := hd1.unique (hprod.congr_of_eventuallyEq hev)
  have hfirst : (derivative P).eval t
      = P.eval t * (xs.map (fun a : ℝ => (t - a)⁻¹)).sum :=
    eval_derivative_eq_mul_logDeriv ht
  have hnegsum : ∀ (m : Multiset ℝ) (g : ℝ → ℝ),
      (m.map (fun a => -g a)).sum = -(m.map g).sum := by
    intro m g
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [Multiset.map_cons, Multiset.sum_cons, ih]; ring
  have hneg : (xs.map (fun a : ℝ => -((t - a) ^ 2)⁻¹)).sum
      = -(xs.map (fun a : ℝ => ((t - a) ^ 2)⁻¹)).sum :=
    hnegsum xs (fun a : ℝ => ((t - a) ^ 2)⁻¹)
  rw [hEq, hfirst, hneg]
  ring

/-- **The lower-endpoint contradiction, in three inequalities.**
`Forgacs2017RationalDenominator` Case 2 at `ρ = 1`: a triple denominator root
at an interior critical point cannot happen.

The interval enters once and only once — through the sign split.  At
`t ∈ (x_1,x_2)` exactly one factor of `Q` is negative, so
`S_1 = A - ∑β` and `S_2 = A^2 + ∑β^2` with `A = (t-x_1)^{-1} > 0`
and `β_b = (b-t)^{-1} > 0`.  The critical-point equation `tS_1 = r` then reads
`A = r/t + ∑β`, and the `k ≥ 3` obstruction reads `t^2S_2 = r`.  Those
are incompatible:

* `∑β ≥ 0` gives `A ≥ r/t`, hence `t^2A^2 ≥ r^2`;
* `r ≥ 1` gives `r^2 ≥ r`;
* `∑β^2 > 0` — which needs a second root, i.e. `deg Q ≥ 2` — makes the
  last step strict.

Each hypothesis is spent in exactly one place, which is why the statement carries
them separately rather than as one combined bound. -/
theorem not_triple_root_of_interior {A S₂ sβ sβ2 t r : ℝ} (ht : 0 < t) (hr : 1 ≤ r)
    (hA : A = r / t + sβ) (hsβ : 0 ≤ sβ) (hsβ2 : 0 < sβ2)
    (hS₂ : S₂ = A ^ 2 + sβ2) (heq : t ^ 2 * S₂ = r) : False := by
  have hrt : 0 < r / t := div_pos (by linarith) ht
  have hAge : r / t ≤ A := by rw [hA]; linarith
  have hApos : 0 < A := lt_of_lt_of_le hrt hAge
  have hsq : (r / t) ^ 2 ≤ A ^ 2 := by nlinarith
  have hrr : r ≤ r ^ 2 := by nlinarith
  have hkey : t ^ 2 * (r / t) ^ 2 = r ^ 2 := by field_simp
  nlinarith [hS₂, heq, hsq, hrr, hkey, hsβ2, sq_nonneg t, mul_pos (mul_pos ht ht) hsβ2]

/-- **The critical point lies in the first gap.**  `E = tQ' - rQ` is negative at
the smallest zero of `Q` — where `Q` vanishes and `Q'` is already negative — and
positive at the smallest zero of `Q'`, where `E = -rQ` and `Q` has gone negative.
The intermediate value theorem puts a zero of `E` strictly between them.

This is what `exists_eval_derivative_eq_zero_between` and
`eval_derivative_ne_zero_of_lt_roots` were for: they place the zero of `Q'` in
`(x_1,x_2)`, and this places `t_a` below it. -/
theorem exists_ftCritical_zero_in_gap {Q : ℝ[X]} {x₁ y r : ℝ} (hx₁ : 0 < x₁)
    (hxy : x₁ < y) (hr : 0 < r) (hQx : Q.eval x₁ = 0)
    (hQ'x : (derivative Q).eval x₁ < 0) (hQy : Q.eval y < 0)
    (hQ'y : (derivative Q).eval y = 0) :
    ∃ ta ∈ Set.Ioo x₁ y, ta * (derivative Q).eval ta - r * Q.eval ta = 0 := by
  set E : ℝ → ℝ := fun t => t * (derivative Q).eval t - r * Q.eval t with hE
  have hcont : ContinuousOn E (Set.Icc x₁ y) :=
    ((continuous_id.mul (derivative Q).continuous_aeval).sub
      (continuous_const.mul Q.continuous_aeval)).continuousOn
  have hEx : E x₁ < 0 := by
    rw [hE]
    simp only [hQx, mul_zero, sub_zero]
    exact mul_neg_of_pos_of_neg hx₁ hQ'x
  have hEy : 0 < E y := by
    rw [hE]
    simp only [hQ'y, mul_zero, zero_sub, neg_pos]
    exact mul_neg_of_pos_of_neg hr hQy
  obtain ⟨ta, hta, hta0⟩ :=
    intermediate_value_Ioo hxy.le hcont (Set.mem_Ioo.2 ⟨hEx, hEy⟩)
  exact ⟨ta, hta, hta0⟩

/-- `Q'` is negative at the smallest zero of `Q` when that zero is simple: the
`(x_1 - t)` factor contributes `-1` and every other factor is positive there.
Supplies `exists_ftCritical_zero_in_gap`'s `hQ'x`. -/
theorem eval_derivative_neg_at_smallest_root {xs : Multiset ℝ} {c x₁ : ℝ} (hc : 0 < c)
    (hmem : x₁ ∈ xs) (hgap : ∀ a ∈ xs.erase x₁, x₁ < a) :
    (derivative (C c * (xs.map (fun a : ℝ => C a - X)).prod)).eval x₁ < 0 := by
  classical
  set ys : Multiset ℝ := xs.erase x₁ with hys
  have hxs : xs = x₁ ::ₘ ys := by rw [hys, Multiset.cons_erase hmem]
  set R : ℝ[X] := (ys.map (fun a : ℝ => C a - X)).prod with hR
  have hsplit : (xs.map (fun a : ℝ => C a - X)).prod = (C x₁ - X) * R := by
    rw [hxs, Multiset.map_cons, Multiset.prod_cons]
  have hd : derivative (C c * ((C x₁ - X) * R))
      = C c * (-R + (C x₁ - X) * derivative R) := by
    rw [derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C,
      zero_sub]
    ring
  obtain ⟨hRpos, -, -, -, -⟩ := negShiftProd_deriv_sign (xs := ys) (t := x₁) hgap
  rw [hsplit, hd, eval_mul, eval_C, eval_add, eval_neg, eval_mul, eval_sub, eval_C, eval_X,
    sub_self, zero_mul, add_zero]
  exact mul_neg_of_pos_of_neg hc (by linarith [hRpos])

/-- `Q < 0` strictly between the smallest zero and the next distinct one: the
`(x_1 - t)` factor has turned negative and every other factor is still
positive. -/
theorem eval_neg_in_gap {xs : Multiset ℝ} {c x₁ y : ℝ} (hc : 0 < c) (hmem : x₁ ∈ xs)
    (hxy : x₁ < y) (hgap : ∀ a ∈ xs.erase x₁, y < a) :
    (C c * (xs.map (fun a : ℝ => C a - X)).prod).eval y < 0 := by
  classical
  set ys : Multiset ℝ := xs.erase x₁ with hys
  have hxs : xs = x₁ ::ₘ ys := by rw [hys, Multiset.cons_erase hmem]
  obtain ⟨hRpos, -, -, -, -⟩ := negShiftProd_deriv_sign (xs := ys) (t := y) hgap
  rw [hxs, Multiset.map_cons, Multiset.prod_cons, eval_mul, eval_C, eval_mul, eval_sub,
    eval_C, eval_X]
  have hneg : x₁ - y < 0 := by linarith
  exact mul_neg_of_pos_of_neg hc (mul_neg_of_neg_of_pos hneg hRpos)

/-- **Connector (4), wired — and the non-vacuity witness for the wrapper.**  The
critical point of `-Q/t^r` lies strictly between the smallest zero of `Q` and the
next distinct one, with no zero of `Q'` assumed: Rolle supplies it in the first
gap, the sign lemmas fix the three signs, and `exists_ftCritical_zero_in_gap`
runs the intermediate value theorem.

**Nothing calls this, and that is correct.**
`FTMinModulus.not_three_le_rootMultiplicity_of_gap` *takes* a point of the first
gap as a hypothesis; if no such point existed, that theorem would be true,
guarded, green, and about nothing.  This is what rules that out — it proves such
a point exists and that it is where the critical point lives.  A non-vacuity
witness is never called by the theorem it protects, so a zero consumer count here
is expected rather than dead weight.  Deleting it would silently convert a real
theorem into a possibly vacuous one, with nothing failing. -/
theorem exists_ftCritical_zero_in_first_gap {xs : Multiset ℝ} {c x₁ x₂ r : ℝ}
    (hc : 0 < c) (hx₁ : 0 < x₁) (hr : 0 < r) (hmem : x₁ ∈ xs) (hmem₂ : x₂ ∈ xs)
    (hxx : x₁ < x₂) (hgap : ∀ a ∈ xs.erase x₁, x₂ ≤ a) :
    ∃ ta ∈ Set.Ioo x₁ x₂,
      ta * (derivative (C c * (xs.map (fun a : ℝ => C a - X)).prod)).eval ta
        - r * (C c * (xs.map (fun a : ℝ => C a - X)).prod).eval ta = 0 := by
  classical
  set Q : ℝ[X] := C c * (xs.map (fun a : ℝ => C a - X)).prod with hQ
  have hroot : ∀ a ∈ xs, Q.eval a = 0 := by
    intro a ha
    rw [hQ, eval_mul, eval_multiset_prod, Multiset.map_map]
    refine mul_eq_zero_of_right _ (Multiset.prod_eq_zero ?_)
    exact Multiset.mem_map.2 ⟨a, ha, by simp⟩
  obtain ⟨y, hy, hy0⟩ :=
    exists_eval_derivative_eq_zero_between hxx (hroot x₁ hmem) (hroot x₂ hmem₂)
  have hgapy : ∀ a ∈ xs.erase x₁, y < a := fun a ha => lt_of_lt_of_le hy.2 (hgap a ha)
  have hQ'x : (derivative Q).eval x₁ < 0 :=
    eval_derivative_neg_at_smallest_root hc hmem
      (fun a ha => lt_of_lt_of_le hxx (hgap a ha))
  have hQy : Q.eval y < 0 := eval_neg_in_gap hc hmem hy.1 hgapy
  obtain ⟨ta, hta, hta0⟩ :=
    exists_ftCritical_zero_in_gap (Q := Q) (r := r) hx₁ hy.1 hr (hroot x₁ hmem) hQ'x hQy hy0
  exact ⟨ta, ⟨hta.1, lt_trans hta.2 hy.2⟩, hta0⟩

/-- **Connector (1), the sign split.**  At `t` strictly between the smallest root
`x_1` and every other root, `S_1 = A - ∑β` and `S_2 = A^2 + ∑β^2`
with `A = (t-x_1)^{-1}` and `β_b = (b-t)^{-1} > 0`.  The interval is used
here and nowhere else: it is what makes exactly one term of each sum come from
the far side.

The two rewrites are unconditional — `(t-b)^{-1} = -(b-t)^{-1}` holds even at a
coincidence, since `0⁻¹ = 0`, and `(t-b)^2 = (b-t)^2` always — so no
non-vanishing hypothesis is spent on them. -/
theorem logDeriv_split_in_gap {ys : Multiset ℝ} {x₁ t : ℝ} (hne : ys ≠ 0)
    (hgt : ∀ b ∈ ys, t < b) :
    ((x₁ ::ₘ ys).map (fun a : ℝ => (t - a)⁻¹)).sum
        = (t - x₁)⁻¹ - (ys.map (fun b : ℝ => (b - t)⁻¹)).sum
      ∧ ((x₁ ::ₘ ys).map (fun a : ℝ => ((t - a) ^ 2)⁻¹)).sum
        = ((t - x₁)⁻¹) ^ 2 + (ys.map (fun b : ℝ => ((b - t) ^ 2)⁻¹)).sum
      ∧ 0 ≤ (ys.map (fun b : ℝ => (b - t)⁻¹)).sum
      ∧ 0 < (ys.map (fun b : ℝ => ((b - t) ^ 2)⁻¹)).sum := by
  classical
  have hflip : (ys.map (fun b : ℝ => (t - b)⁻¹)).sum
      = -(ys.map (fun b : ℝ => (b - t)⁻¹)).sum := by
    have hpt : ∀ (m : Multiset ℝ) (g : ℝ → ℝ),
        (m.map (fun a => -g a)).sum = -(m.map g).sum := by
      intro m g
      induction m using Multiset.induction_on with
      | empty => simp
      | cons a s ih => simp [Multiset.map_cons, Multiset.sum_cons, ih]; ring
    rw [← hpt ys (fun b : ℝ => (b - t)⁻¹)]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun b _ => ?_)
    rw [show t - b = -(b - t) by ring, inv_neg]
  have hsq : (ys.map (fun b : ℝ => ((t - b) ^ 2)⁻¹)).sum
      = (ys.map (fun b : ℝ => ((b - t) ^ 2)⁻¹)).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun b _ => ?_)
    rw [show (t - b) ^ 2 = (b - t) ^ 2 by ring]
  have hnn : 0 ≤ (ys.map (fun b : ℝ => (b - t)⁻¹)).sum := by
    refine Multiset.sum_nonneg ?_
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    exact le_of_lt (inv_pos.2 (by linarith [hgt b hb]))
  have hpos : 0 < (ys.map (fun b : ℝ => ((b - t) ^ 2)⁻¹)).sum := by
    obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hne
    obtain ⟨zs, hzs⟩ := Multiset.exists_cons_of_mem hb
    have hbt : 0 < (b - t) ^ 2 := by nlinarith [hgt b hb]
    have hrest : 0 ≤ (zs.map (fun b : ℝ => ((b - t) ^ 2)⁻¹)).sum := by
      refine Multiset.sum_nonneg ?_
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.1 hx
      have : t < d := hgt d (by rw [hzs]; exact Multiset.mem_cons_of_mem hd)
      positivity
    rw [hzs, Multiset.map_cons, Multiset.sum_cons]
    exact add_pos_of_pos_of_nonneg (inv_pos.2 hbt) hrest
  refine ⟨?_, ?_, hnn, hpos⟩
  · rw [Multiset.map_cons, Multiset.sum_cons, hflip]; ring
  · rw [Multiset.map_cons, Multiset.sum_cons, hsq, inv_pow]

/-- **Connector (2), the triple-root obstruction at general `r`.**  A triple
denominator root forces `t_e^2Q''(t_e) = r(r-1)Q(t_e)`, from `D(t_e) = 0` giving
`z = -Q(t_e)/t_e^r` and `D''(t_e) = 0` giving `Q'' + r(r-1)zX^{r-2} = 0`.

**One statement, two proofs.**  Combining those needs `t_e^{r-2}t_e^2 = t_e^r`,
which is **false at `r = 1`**: `ℕ`-subtraction makes `r - 2 = 0`, so the
left side is `t_e^2` and the right is `t_e`.  The conclusion still holds there,
for the other reason — the coefficient `r(r-1)` vanishes and
`eval_derivative_two_eq_zero_of_three_le_rootMultiplicity` gives `Q''(t_e) = 0`.
The split is forced by the truncating subtraction, not by any mathematics. -/
theorem eval_derivative_two_relation_of_three_le_rootMultiplicity {Q : ℂ[X]} {r : ℕ}
    (hr : 1 ≤ r) {z te : ℂ} (hte : te ≠ 0)
    (h : 3 ≤ (ftDen Q r z).rootMultiplicity te) :
    te ^ 2 * (derivative (derivative Q)).eval te = (r : ℂ) * ((r : ℂ) - 1) * Q.eval te := by
  rcases eq_or_lt_of_le hr with hr1 | hr2
  · -- `r = 1`: the coefficient vanishes and the second derivative does too
    subst_vars
    rw [eval_derivative_two_eq_zero_of_three_le_rootMultiplicity (by simpa using h)]
    push_cast
    ring
  · -- `2 ≤ r`
    have hr2' : 2 ≤ r := hr2
    have h0 : (ftDen Q r z).eval te = 0 := by
      have := isRoot_iterate_derivative_of_lt_rootMultiplicity (p := ftDen Q r z) (t := te)
        (n := 0) (by omega)
      simpa using this
    have h2 : (derivative^[2] (ftDen Q r z)).eval te = 0 :=
      isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega)
    have hd2 : derivative^[2] (ftDen Q r z)
        = derivative (derivative Q)
          + C z * (C ((r : ℂ)) * (C (((r - 1 : ℕ) : ℂ)) * X ^ (r - 2))) := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
        ftDen, derivative_add, derivative_C_mul, derivative_X_pow]
      congr 3
    rw [hd2] at h2
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at h2
    rw [ftDen_eval] at h0
    have hcast : (((r - 1 : ℕ) : ℂ)) = (r : ℂ) - 1 := by
      have : (1 : ℕ) ≤ r := hr
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast] at h2
    have hpow : te ^ (r - 2) * te ^ 2 = te ^ r := by
      rw [← pow_add]
      congr 1
      omega
    -- eliminate `z`
    have hz : z * te ^ r = -Q.eval te := by linear_combination h0
    have : te ^ 2 * (derivative (derivative Q)).eval te
        + (r : ℂ) * ((r : ℂ) - 1) * (z * (te ^ (r - 2) * te ^ 2)) = 0 := by
      linear_combination te ^ 2 * h2
    rw [hpow, hz] at this
    linear_combination this

/-- **The assembly.**  `Forgacs2017RationalDenominator` Case 2 at `ρ = 1`: at a
critical point strictly between the smallest zero of `Q` and every other zero,
the denominator cannot have a triple root.

Everything above is spent here.  The two log-derivative identities turn the two
endpoint relations into `tS_1 = r` and `t^2(S_1^2 - S_2) = r(r-1)`; substituting
the first into the second gives `t^2S_2 = r`; `logDeriv_split_in_gap` splits both
sums at the smallest zero and supplies `∑β ≥ 0` and `∑β^2 > 0`;
and `not_triple_root_of_interior` closes.  No interlacing, no location of any
zero of `Q''`, and the interval is used only through the split. -/
theorem not_relations_in_gap {ys : Multiset ℝ} {c x₁ t : ℝ} {r : ℕ} (hc : c ≠ 0)
    (hr : 1 ≤ r) (ht0 : 0 < t) (hne : ys ≠ 0) (hx₁t : x₁ < t) (hgt : ∀ b ∈ ys, t < b)
    (h1 : t * (derivative (C c * (((x₁ ::ₘ ys)).map (fun a : ℝ => C a - X)).prod)).eval t
        = r * (C c * (((x₁ ::ₘ ys)).map (fun a : ℝ => C a - X)).prod).eval t)
    (h2 : t ^ 2
        * (derivative (derivative
            (C c * (((x₁ ::ₘ ys)).map (fun a : ℝ => C a - X)).prod))).eval t
        = (r : ℝ) * ((r : ℝ) - 1)
          * (C c * (((x₁ ::ₘ ys)).map (fun a : ℝ => C a - X)).prod).eval t) : False := by
  classical
  have htne : t ≠ 0 := ne_of_gt ht0
  set xs : Multiset ℝ := x₁ ::ₘ ys with hxs
  set P : ℝ[X] := C c * (xs.map (fun a : ℝ => C a - X)).prod with hP
  have hnr : ∀ a ∈ xs, t ≠ a := by
    intro a ha
    rcases Multiset.mem_cons.1 (hxs ▸ ha) with rfl | hb
    · exact ne_of_gt hx₁t
    · exact ne_of_lt (hgt a hb)
  have hPt : P.eval t ≠ 0 := by
    rw [hP, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    refine mul_ne_zero hc (Multiset.prod_ne_zero ?_)
    intro h0
    obtain ⟨a, ha, hae⟩ := Multiset.mem_map.1 h0
    exact hnr a ha (by simpa [eq_comm, sub_eq_zero] using hae.symm)
  set S₁ : ℝ := (xs.map (fun a : ℝ => (t - a)⁻¹)).sum with hS₁
  set S₂ : ℝ := (xs.map (fun a : ℝ => ((t - a) ^ 2)⁻¹)).sum with hS₂
  have hd1 : (derivative P).eval t = P.eval t * S₁ := eval_derivative_eq_mul_logDeriv hnr
  have hd2 : (derivative (derivative P)).eval t = P.eval t * (S₁ ^ 2 - S₂) :=
    eval_derivative_two_eq_mul_logDeriv hc hnr
  -- the two relations, divided by `P(t)`
  have e1 : t * S₁ = (r : ℝ) := by
    have h := h1
    rw [hd1] at h
    exact mul_left_cancel₀ hPt (by linear_combination h)
  have e2 : t ^ 2 * (S₁ ^ 2 - S₂) = (r : ℝ) * ((r : ℝ) - 1) := by
    have h := h2
    rw [hd2] at h
    exact mul_left_cancel₀ hPt (by linear_combination h)
  -- substituting the first into the second
  have e3 : t ^ 2 * S₂ = (r : ℝ) := by
    have hsq : t ^ 2 * S₁ ^ 2 = (r : ℝ) ^ 2 := by
      have hh : (t * S₁) ^ 2 = ((r : ℝ)) ^ 2 := by rw [e1]
      linear_combination hh
    linear_combination hsq - e2
  -- the split at the smallest zero
  obtain ⟨hsplit1, hsplit2, hnn, hpos⟩ := logDeriv_split_in_gap (x₁ := x₁) hne hgt
  rw [← hxs, ← hS₁] at hsplit1
  rw [← hxs, ← hS₂] at hsplit2
  have hA : (t - x₁)⁻¹ = (r : ℝ) / t + (ys.map (fun b : ℝ => (b - t)⁻¹)).sum := by
    have h := e1
    rw [hsplit1] at h
    have hb : ((t - x₁)⁻¹ - (ys.map (fun b : ℝ => (b - t)⁻¹)).sum) * t = (r : ℝ) := by
      linear_combination h
    have hd : (t - x₁)⁻¹ - (ys.map (fun b : ℝ => (b - t)⁻¹)).sum = (r : ℝ) / t :=
      (eq_div_iff htne).2 hb
    linarith
  exact not_triple_root_of_interior (t := t) (r := (r : ℝ)) ht0 (by exact_mod_cast hr)
    hA hnn hpos hsplit2 e3

/-- **The lower half of the first-gap location.**  Every positive zero of
`E = tQ' - rQ` lies strictly above the smallest zero of `Q`, when that zero is
simple.  Below `x_1` every factor of `Q` is positive, so `Q > 0` and `Q' < 0`
and `E < 0`; at `x_1` itself `Q` vanishes and `Q'` is still negative, so
`E(x_1) = x_1Q'(x_1) < 0`.  Neither case can be a zero.

`FTBranchGap.exists_tendsto_ftTau_lt_second` is the upper half, `t_a < x_2`; the
two together put the endpoint in the first gap, which is what
`FTMinModulus.not_three_le_rootMultiplicity_of_gap` consumes.

`hgap` carries the simplicity of `x_1` rather than side-conditioning it: a second
copy would sit in the erased multiset and would have to satisfy `x_1 < x_1`. -/
theorem lt_of_ftCritical_eval_eq_zero {xs : Multiset ℝ} {c x₁ L : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hmem : x₁ ∈ xs) (hgap : ∀ a ∈ xs.erase x₁, x₁ < a)
    (hL : 0 < L)
    (hE : L * (derivative (C c * (xs.map (fun a : ℝ => C a - X)).prod)).eval L
        - r * (C c * (xs.map (fun a : ℝ => C a - X)).prod).eval L = 0) :
    x₁ < L := by
  classical
  by_contra hcon
  push Not at hcon
  rcases lt_or_eq_of_le hcon with hlt | heq
  · -- `L < x₁`: every factor is positive at `L`, so `Q > 0`, `Q' < 0`, `E < 0`
    have hall : ∀ a ∈ xs, L < a := by
      intro a ha
      rcases eq_or_ne a x₁ with rfl | hne
      · exact hlt
      · exact lt_trans hlt (hgap a (Multiset.mem_erase_of_ne hne |>.2 ha))
    obtain ⟨hRpos, hRstrict, -, -, -⟩ := negShiftProd_deriv_sign hall
    have hne0 : xs ≠ 0 := fun h => by simp [h] at hmem
    have hQ : 0 < (C c * (xs.map (fun a : ℝ => C a - X)).prod).eval L := by
      rw [eval_mul, eval_C]; exact mul_pos hc hRpos
    have hQ' : (derivative (C c * (xs.map (fun a : ℝ => C a - X)).prod)).eval L < 0 := by
      rw [derivative_C_mul, eval_mul, eval_C]
      exact mul_neg_of_pos_of_neg hc (hRstrict hne0)
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    nlinarith [hE, hQ, hQ', hL, hrR]
  · -- `L = x₁`: `Q(x₁) = 0` and `Q'(x₁) < 0`
    subst heq
    have hQ0 : (C c * (xs.map (fun a : ℝ => C a - X)).prod).eval L = 0 := by
      rw [eval_mul, eval_multiset_prod, Multiset.map_map]
      refine mul_eq_zero_of_right _ (Multiset.prod_eq_zero ?_)
      exact Multiset.mem_map.2 ⟨L, hmem, by simp⟩
    have hQ' := eval_derivative_neg_at_smallest_root (c := c) hc hmem hgap
    nlinarith [hE, hQ0, hQ', hL]

/-! ### Strict minimum modulus

`eq:endpoint-fixed-gap` needs strictness, and the minimum-modulus statement
imported from `Forgacs2017RationalDenominator` is quantified over the open
parameter interval, so in the limit it gives only `|t_j| ≥ t_a`.  The paper
supplies the strict comparison directly, and it is elementary. -/

theorem multiset_prod_le_prod (f g : ℝ → ℝ) : ∀ xs : Multiset ℝ,
    (∀ x ∈ xs, 0 ≤ f x) → (∀ x ∈ xs, f x ≤ g x) → (xs.map f).prod ≤ (xs.map g).prod := by
  intro xs
  refine Multiset.induction_on xs (by simp) ?_
  intro a s ih hf hle
  simp only [Multiset.map_cons, Multiset.prod_cons]
  have hfa : 0 ≤ f a := hf a (Multiset.mem_cons_self a s)
  have hprodf : 0 ≤ (s.map f).prod := by
    refine Multiset.prod_nonneg fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
    exact hf x (Multiset.mem_cons_of_mem hx)
  exact mul_le_mul (hle a (Multiset.mem_cons_self a s))
    (ih (fun x hx => hf x (Multiset.mem_cons_of_mem hx))
      (fun x hx => hle x (Multiset.mem_cons_of_mem hx)))
    hprodf (le_trans hfa (hle a (Multiset.mem_cons_self a s)))

theorem multiset_prod_lt_prod (f g : ℝ → ℝ) : ∀ xs : Multiset ℝ, xs ≠ 0 →
    (∀ x ∈ xs, 0 ≤ f x) → (∀ x ∈ xs, f x < g x) → (xs.map f).prod < (xs.map g).prod := by
  intro xs
  refine Multiset.induction_on xs (by simp) ?_
  intro a s _ _ hf hlt
  simp only [Multiset.map_cons, Multiset.prod_cons]
  have hfa : 0 ≤ f a := hf a (Multiset.mem_cons_self a s)
  have hlta : f a < g a := hlt a (Multiset.mem_cons_self a s)
  have hprodg : 0 < (s.map g).prod := by
    refine Multiset.prod_pos fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
    exact lt_of_le_of_lt (hf x (Multiset.mem_cons_of_mem hx)) (hlt x (Multiset.mem_cons_of_mem hx))
  have hle := multiset_prod_le_prod f g s (fun x hx => hf x (Multiset.mem_cons_of_mem hx))
    (fun x hx => (hlt x (Multiset.mem_cons_of_mem hx)).le)
  calc f a * (s.map f).prod ≤ f a * (s.map g).prod := mul_le_mul_of_nonneg_left hle hfa
    _ < g a * (s.map g).prod := mul_lt_mul_of_pos_right hlta hprodg

/-- `eq:Q-hypotheses` in factored form: `Q(t) = c ∏_j (t - x_j)`, the `x_j`
running over a multiset of positive reals. -/
noncomputable def posRootPoly (c : ℂ) (xs : Multiset ℝ) : Polynomial ℂ :=
  C c * (xs.map (fun x : ℝ => X - C ((x : ℝ) : ℂ))).prod

private theorem norm_multiset_prod_sub (xs : Multiset ℝ) (t : ℂ) :
    ‖(xs.map (fun x : ℝ => t - ((x : ℝ) : ℂ))).prod‖
      = (xs.map (fun x : ℝ => ‖t - ((x : ℝ) : ℂ)‖)).prod := by
  refine Multiset.induction_on xs ?_ ?_ <;> intros <;> simp_all

theorem norm_eval_posRootPoly (c : ℂ) (xs : Multiset ℝ) (t : ℂ) :
    ‖(posRootPoly c xs).eval t‖ = ‖c‖ * (xs.map (fun x : ℝ => ‖t - ((x : ℝ) : ℂ)‖)).prod := by
  rw [posRootPoly, eval_mul, eval_C, norm_mul, Polynomial.eval_multiset_prod,
    show ((xs.map (fun x : ℝ => (X : Polynomial ℂ) - C ((x : ℝ) : ℂ))).map (Polynomial.eval t))
      = xs.map (fun x : ℝ => t - ((x : ℝ) : ℂ)) by simp [Multiset.map_map],
    norm_multiset_prod_sub]

/-- The circle comparison: at equal modulus, the squared distance to a positive
zero `x` of `Q` moves by `2x(t_e - Re t)`, whose sign is that of `t_e`. -/
theorem norm_sub_sq_sub (x te : ℝ) {t : ℂ} (hnorm : ‖t‖ = |te|) :
    ‖t - ((x : ℝ) : ℂ)‖ ^ 2 - ‖((te : ℝ) : ℂ) - ((x : ℝ) : ℂ)‖ ^ 2 = 2 * x * (te - t.re) := by
  have hre : t.re ^ 2 + t.im ^ 2 = te ^ 2 := by
    have h1 : ‖t‖ ^ 2 = t.re ^ 2 + t.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← h1, hnorm, sq_abs]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination hre

/-- **`thm:FT-geometry`, strict minimum modulus.**  Let `t_e ≠ 0` be real with
`Q(t_e) + z_e t_e^r = 0`, `z_e` real.  Then no *other* point of the circle
`|t| = |t_e|` is a zero of `Q(·) + z_e(·)^r`: at equal modulus every distance to
a positive zero of `Q` moves strictly one way, so `|Q(t)| ≠ |Q(t_e)| = |z_e t^r|`.
Applied at `t_e = t_a` this makes the limiting bound `|t_j| ≥ t_a` strict, which
is what `eq:endpoint-fixed-gap` needs and what the imported minimum-modulus
statement, quantified over the open parameter interval, does not give. -/
theorem eval_ftDen_ne_zero_of_norm_eq {c : ℂ} (hc : c ≠ 0) {xs : Multiset ℝ} (hxs : xs ≠ 0)
    (hx : ∀ x ∈ xs, 0 < x) {r : ℕ} {te ze : ℝ} (hte : te ≠ 0)
    (hroot : (ftDen (posRootPoly c xs) r ((ze : ℝ) : ℂ)).eval ((te : ℝ) : ℂ) = 0)
    {t : ℂ} (hnorm : ‖t‖ = ‖((te : ℝ) : ℂ)‖) (hne : t ≠ ((te : ℝ) : ℂ)) :
    (ftDen (posRootPoly c xs) r ((ze : ℝ) : ℂ)).eval t ≠ 0 := by
  have hnormte : ‖t‖ = |te| := by rwa [Complex.norm_real, Real.norm_eq_abs] at hnorm
  have hre : t.re ^ 2 + t.im ^ 2 = te ^ 2 := by
    have h1 : ‖t‖ ^ 2 = t.re ^ 2 + t.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← h1, hnormte, sq_abs]
  have hres : t.re ≠ te := by
    intro h
    refine hne (Complex.ext (by simpa using h) ?_)
    have him : t.im ^ 2 = 0 := by rw [h] at hre; linarith
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 him
  have habsre : |t.re| ≤ |te| := by rw [← hnormte]; exact Complex.abs_re_le_norm t
  -- the moduli of `Q` at `t` and at `t_e` differ
  have hQne : ‖(posRootPoly c xs).eval t‖ ≠ ‖(posRootPoly c xs).eval ((te : ℝ) : ℂ)‖ := by
    have hcnorm : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    rw [norm_eval_posRootPoly, norm_eval_posRootPoly]
    rcases lt_or_gt_of_ne hte with hneg | hpos
    · -- `t_e < 0`: `t_e < Re t`, so every distance shrinks
      have hltre : te < t.re := by
        have hge : te ≤ t.re := by
          have := neg_le_of_abs_le (habsre.trans_eq (abs_of_neg hneg))
          linarith
        exact lt_of_le_of_ne hge (Ne.symm hres)
      have hstep : ∀ x ∈ xs, ‖t - ((x : ℝ) : ℂ)‖ < ‖((te : ℝ) : ℂ) - ((x : ℝ) : ℂ)‖ := by
        intro x hx'
        have h := norm_sub_sq_sub x te hnormte
        have hxpos := hx x hx'
        refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
        nlinarith
      have := multiset_prod_lt_prod (fun x : ℝ => ‖t - ((x : ℝ) : ℂ)‖)
        (fun x : ℝ => ‖((te : ℝ) : ℂ) - ((x : ℝ) : ℂ)‖) xs hxs (fun x _ => norm_nonneg _) hstep
      exact ne_of_lt (by exact mul_lt_mul_of_pos_left this hcnorm)
    · -- `t_e > 0`: `Re t < t_e`, so every distance grows
      have hltre : t.re < te := by
        have hle : t.re ≤ te := (le_abs_self t.re).trans (habsre.trans_eq (abs_of_pos hpos))
        exact lt_of_le_of_ne hle hres
      have hstep : ∀ x ∈ xs, ‖((te : ℝ) : ℂ) - ((x : ℝ) : ℂ)‖ < ‖t - ((x : ℝ) : ℂ)‖ := by
        intro x hx'
        have h := norm_sub_sq_sub x te hnormte
        have hxpos := hx x hx'
        refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
        nlinarith
      have := multiset_prod_lt_prod (fun x : ℝ => ‖((te : ℝ) : ℂ) - ((x : ℝ) : ℂ)‖)
        (fun x : ℝ => ‖t - ((x : ℝ) : ℂ)‖) xs hxs (fun x _ => norm_nonneg _) hstep
      exact ne_of_gt (by exact mul_lt_mul_of_pos_left this hcnorm)
  intro hcon
  rw [ftDen_eval] at hcon hroot
  have h1 : ‖(posRootPoly c xs).eval t‖ = |ze| * ‖t‖ ^ r := by
    have hEq : (posRootPoly c xs).eval t = -(((ze : ℝ) : ℂ) * t ^ r) := by linear_combination hcon
    rw [hEq, norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(posRootPoly c xs).eval ((te : ℝ) : ℂ)‖ = |ze| * ‖((te : ℝ) : ℂ)‖ ^ r := by
    have hEq : (posRootPoly c xs).eval ((te : ℝ) : ℂ)
        = -(((ze : ℝ) : ℂ) * ((te : ℝ) : ℂ) ^ r) := by linear_combination hroot
    rw [hEq, norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact hQne (by rw [h1, h2, hnorm])

end ForgacsTran
