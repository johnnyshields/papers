/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Shields.Analysis.Calculus.TaylorCoeff
import Shields.Analysis.Complex.Rouche
import ForgacsTran.AttractorBranch
import ForgacsTran.AttractorExpansion

/-!
# The isolated dominant cancellation

`isolated_dominant_cancellation` is the proposition itself, in the generality it
is stated in: an arbitrary `Q` with `Q(0) ≠ 0`, an arbitrary nonzero `B`, and a
zero `t_0 ≠ 0` of `B` that is a simple, uniquely minimal-modulus zero of
`D(·,z_0) = Q + z_0t^r`.  No positive-rootedness is assumed.

The route runs through four modules.  `AttractorBranch` supplies the root branch
`t(z)` and `eq:dominant-root-derivative`; `AttractorExpansion` the coefficient
calculus at a simple pole.  What is added here is the rest:

## Main statements

* `taylorCoeff_div_ftDen` — `F_M(z) = [t^M]B/D(·,z)` is a **polynomial** in
  the parameter, `ftCoeffPoly`, read off the convolution recurrence of
  `B = D(·,z)∑ F_Mt^M`.  This is what makes `F_M` an analytic function of
  `z`, which Rouché in the parameter needs.
* `div_ftDen_eq` — the pole subtraction, done by polynomial division rather than
  through a removable singularity: `D = (t-τ)S`, and `B - AS` vanishes at
  `τ`, so the remainder is a quotient of polynomials with `S` zero-free on the
  disk.
* `exists_unique_root_nearby` — Rouché in `t` against the perturbation
  `(z - z_0)t^r`: the dominant root stays alone in `|t| ≤ R` for every nearby
  parameter.
* `exists_uniform_expansion` — `eq:isolated-dominant-expansion` with one constant
  and one ratio `ρ < 1` for a whole parameter disk, the constant obtained by
  compactness from the joint continuity of the remainder.
* `exists_amplitude_factorization` — `eq:isolated-amplitude-order`,
  `𝒜(z) = (z-z_0)^ν𝒱(z)`, from the analytic order of `B` at
  `t_0` transported along a branch of nonvanishing derivative.
* `isolated_dominant_cancellation` — Rouché in the parameter, giving the exact
  count `ν` as a `FactoredOn` of `F_M`, together with
  `eq:isolated-cancellation-rate` in the form `|z - z_0|^ν ≤ Kρ^M`.
* `rootMultiplicity_monomial_mul` — `rem:cancellation-meaning`'s first half:
  the monomial `t^{λ_N}` of the canonical Laurent restriction does not
  change vanishing order at a nonzero point.

## Implementation notes

Sorry-free, and no axiom beyond `propext`, `Classical.choice`, `Quot.sound`.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `subsec:isolated-attractors`,
`prop:isolated-dominant-cancellation`, `eq:isolated-dominant-root`,
`eq:local-spectral-ratio`, `eq:isolated-amplitude-order`,
`eq:isolated-dominant-expansion`, `eq:isolated-cancellation-rate`,
`rem:cancellation-meaning`, `eq:cancellation-intersection-multiplicity`).

## Tags

dominant cancellation, residue amplitude, isolated pole, zero attractor
-/

namespace ForgacsTran

open Complex Metric Polynomial Shields

/-! ### Taylor coefficients of a polynomial -/

/-- The Taylor coefficients of a polynomial function are its coefficients. -/
theorem taylorCoeff_polynomial (p : ℂ[X]) (m : ℕ) :
    taylorCoeff (fun t => p.eval t) m = p.coeff m := by
  have hiter : ∀ (k : ℕ) (q : ℂ[X]),
      iteratedDeriv k (fun t => q.eval t) = fun t => (derivative^[k] q).eval t := by
    intro k
    induction k with
    | zero => intro q; simp
    | succ k ih =>
      intro q
      rw [iteratedDeriv_succ']
      have : deriv (fun t => q.eval t) = fun t => (derivative q).eval t := by
        funext t; exact q.deriv
      rw [this, ih (derivative q), Function.iterate_succ_apply]
  have hfac : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  rw [taylorCoeff, hiter m p]
  change ((Nat.factorial m : ℕ) : ℂ)⁻¹ * (derivative^[m] p).eval 0 = p.coeff m
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative (k := m) p 0]
  simp only [Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  field_simp

/-- A polynomial function is analytic everywhere. -/
theorem analyticAt_eval (p : ℂ[X]) (c : ℂ) : AnalyticAt ℂ (fun t => p.eval t) c :=
  AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) p c (Set.mem_univ c)

/-- A polynomial function is analytic on any set. -/
theorem analyticOnNhd_eval (p : ℂ[X]) (s : Set ℂ) :
    AnalyticOnNhd ℂ (fun t => p.eval t) s := fun c _ => analyticAt_eval p c

/-! ### The coefficient polynomials -/

/-- Paper `prop:isolated-dominant-cancellation` — the denominator
`D(·,z) = Q + z X^r`, as a polynomial in `t`. -/
noncomputable def ftDen (Q : ℂ[X]) (r : ℕ) (z : ℂ) : ℂ[X] := Q + C z * X ^ r

@[simp] theorem ftDen_eval (Q : ℂ[X]) (r : ℕ) (z t : ℂ) :
    (ftDen Q r z).eval t = Q.eval t + z * t ^ r := by simp [ftDen]

/-- The `j`-th coefficient of `D(·,z)`, as a polynomial in `z`: the pencil is
affine in `z`, so each coefficient is. -/
noncomputable def ftDenCoeff (Q : ℂ[X]) (r j : ℕ) : ℂ[X] :=
  C (Q.coeff j) + (if j = r then X else 0)

theorem ftDenCoeff_eval (Q : ℂ[X]) (r j : ℕ) (z : ℂ) :
    (ftDenCoeff Q r j).eval z = (ftDen Q r z).coeff j := by
  simp only [ftDenCoeff, ftDen, coeff_add, coeff_C_mul, coeff_X_pow, eval_add, eval_C]
  by_cases h : j = r <;> simp [h]

theorem ftDenCoeff_zero (Q : ℂ[X]) {r : ℕ} (hr : 1 ≤ r) :
    ftDenCoeff Q r 0 = C (Q.coeff 0) := by
  have h : ¬ (0 = r) := by omega
  simp [ftDenCoeff, h]

/-- Paper `prop:isolated-dominant-cancellation` — the coefficient polynomials
`F_M`, defined by the convolution recurrence read off `B = D(·,z)·∑ F_M t^M`.
Each is a polynomial in `z`, which is what makes `F_M` an analytic function of
the parameter. -/
noncomputable def ftCoeffPoly (Q B : ℂ[X]) (r : ℕ) : ℕ → ℂ[X]
  | M => C (Q.coeff 0)⁻¹ * (C (B.coeff M)
      - ∑ i : Fin M, ftDenCoeff Q r (M - (i : ℕ)) * ftCoeffPoly Q B r (i : ℕ))
  decreasing_by exact i.isLt

theorem ftCoeffPoly_eq (Q B : ℂ[X]) (r M : ℕ) :
    ftCoeffPoly Q B r M = C (Q.coeff 0)⁻¹ * (C (B.coeff M)
      - ∑ i ∈ Finset.range M, ftDenCoeff Q r (M - i) * ftCoeffPoly Q B r i) := by
  rw [ftCoeffPoly, Fin.sum_univ_eq_sum_range
    (fun i => ftDenCoeff Q r (M - i) * ftCoeffPoly Q B r i) M]

/-- **Paper `prop:isolated-dominant-cancellation` — `F_M` is a polynomial in the
parameter.**  The `M`-th Taylor coefficient of `B/D(·,z)` at `t = 0` is
`ftCoeffPoly Q B r M` evaluated at `z`.

**Differs from the paper's route.**  The paper reads `F_M` off the generating
function `B/D` as a coefficient and never needs it to be a polynomial in `z`.
Rouché in the parameter does need that, so here `F_M` is *defined* by the
convolution recurrence of `B = D(·,z)∑ F_M t^M` and the coefficient identity is
proved from the recurrence. -/
theorem taylorCoeff_div_ftDen (Q B : ℂ[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    (z : ℂ) (M : ℕ) :
    taylorCoeff (fun t => B.eval t / (ftDen Q r z).eval t) M = (ftCoeffPoly Q B r M).eval z := by
  have hD0 : (ftDen Q r z).eval 0 = Q.eval 0 := by
    simp [zero_pow (by omega : r ≠ 0)]
  have hDan : AnalyticAt ℂ (fun t => (ftDen Q r z).eval t) 0 := analyticAt_eval (ftDen Q r z) 0
  have hDne : (fun t => (ftDen Q r z).eval t) 0 ≠ 0 := by
    change (ftDen Q r z).eval 0 ≠ 0
    rw [hD0]; exact hQ0
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    set f : ℂ → ℂ := fun t => B.eval t / (ftDen Q r z).eval t with hf
    have hfan : AnalyticAt ℂ f 0 := (analyticAt_eval B 0).div hDan hDne
    have heq : (fun t => f t * (ftDen Q r z).eval t) =ᶠ[nhds 0] fun t => B.eval t := by
      have hev : ∀ᶠ t in nhds (0 : ℂ), (ftDen Q r z).eval t ≠ 0 :=
        hDan.continuousAt.eventually_ne hDne
      filter_upwards [hev] with t ht
      simp only [hf]
      field_simp
    have hmul := taylorCoeff_mul hfan hDan M
    rw [taylorCoeff_congr heq M, taylorCoeff_polynomial B M, Finset.sum_range_succ,
      Nat.sub_self] at hmul
    have hd0 : taylorCoeff (fun t => (ftDen Q r z).eval t) 0 = Q.coeff 0 := by
      rw [taylorCoeff_polynomial]
      simpa [ftDenCoeff_eval] using congrArg (Polynomial.eval z) (ftDenCoeff_zero Q hr)
    have hq0 : Q.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
    have hsum : ∀ i ∈ Finset.range M,
        taylorCoeff f i * taylorCoeff (fun t => (ftDen Q r z).eval t) (M - i)
          = (ftDenCoeff Q r (M - i) * ftCoeffPoly Q B r i).eval z := by
      intro i hi
      rw [ih i (Finset.mem_range.mp hi), taylorCoeff_polynomial, eval_mul, ftDenCoeff_eval,
        mul_comm]
    rw [Finset.sum_congr rfl hsum, hd0] at hmul
    rw [ftCoeffPoly_eq, eval_mul, eval_sub, eval_C, eval_C, eval_finsetSum]
    field_simp
    linear_combination -hmul

/-! ### Subtracting the dominant pole -/

/-- Paper `prop:isolated-dominant-cancellation` — the denominator with its
dominant root divided out, `D(t,z)/(t - τ)`.  At a simple root this is the
polynomial whose value at `τ` is `∂_t D(τ,z)`. -/
noncomputable def ftCofactor (Q : ℂ[X]) (r : ℕ) (z τ : ℂ) : ℂ[X] :=
  ftDen Q r z /ₘ (X - C τ)

theorem ftCofactor_mul {Q : ℂ[X]} {r : ℕ} {z τ : ℂ} (hroot : (ftDen Q r z).eval τ = 0) :
    (X - C τ) * ftCofactor Q r z τ = ftDen Q r z :=
  mul_divByMonic_eq_iff_isRoot.mpr hroot

/-- The cofactor at the root is `∂_t D(τ,z)`: differentiating
`D = (t - τ)S` and evaluating kills the `S'` term. -/
theorem eval_derivative_ftDen {Q : ℂ[X]} {r : ℕ} {z τ : ℂ}
    (hroot : (ftDen Q r z).eval τ = 0) :
    (derivative (ftDen Q r z)).eval τ = (ftCofactor Q r z τ).eval τ := by
  conv_lhs => rw [← ftCofactor_mul hroot]
  simp

/-- Paper `prop:isolated-dominant-cancellation` — the residue amplitude
`𝒜 = -B(τ)/∂_t D(τ,z)`. -/
noncomputable def ftAmp (Q B : ℂ[X]) (r : ℕ) (z τ : ℂ) : ℂ :=
  -(B.eval τ / (ftCofactor Q r z τ).eval τ)

/-- The numerator of the analytic remainder left after the pole at `τ` is
subtracted: `B + 𝒜 S` vanishes at `τ`, so it is divisible there. -/
noncomputable def ftRem (Q B : ℂ[X]) (r : ℕ) (z τ : ℂ) : ℂ[X] :=
  (B + C (ftAmp Q B r z τ) * ftCofactor Q r z τ) /ₘ (X - C τ)

/-- Paper `eq:isolated-dominant-expansion` — the analytic remainder
`B/D - A/(t - τ)`, as the quotient of two polynomials with no pole left. -/
noncomputable def ftErr (Q B : ℂ[X]) (r : ℕ) (z τ : ℂ) (t : ℂ) : ℂ :=
  (ftRem Q B r z τ).eval t / (ftCofactor Q r z τ).eval t

theorem ftRem_mul {Q B : ℂ[X]} {r : ℕ} {z τ : ℂ}
    (hS : (ftCofactor Q r z τ).eval τ ≠ 0) :
    (X - C τ) * ftRem Q B r z τ = B + C (ftAmp Q B r z τ) * ftCofactor Q r z τ := by
  refine mul_divByMonic_eq_iff_isRoot.mpr ?_
  simp only [IsRoot, eval_add, eval_mul, eval_C, ftAmp]
  field

/-- **Paper `prop:isolated-dominant-cancellation` — the pole subtraction.**
Off the root and where the cofactor does not vanish, `B/D` is a simple pole of
residue `-𝒜` at `τ` plus the analytic remainder.

**Differs from the paper's route.**  The paper reaches this through
`lem:contour-separation`, reading the residue off a contour integral and treating
the difference as a removable singularity.  Here it is polynomial algebra:
`D = (t-τ)S` by monic division, `B - AS` vanishes at `τ` so `(t-τ)`
divides it, and the quotient over `S` is the remainder.  Nothing analytic is
consumed, so the identity holds wherever `S` and `t-τ` are nonzero rather than
only inside a contour. -/
theorem div_ftDen_eq {Q B : ℂ[X]} {r : ℕ} {z τ t : ℂ} (hroot : (ftDen Q r z).eval τ = 0)
    (hSτ : (ftCofactor Q r z τ).eval τ ≠ 0) (ht : t ≠ τ)
    (hSt : (ftCofactor Q r z τ).eval t ≠ 0) :
    B.eval t / (ftDen Q r z).eval t
      = -ftAmp Q B r z τ * (t - τ)⁻¹ + ftErr Q B r z τ t := by
  have hD : (ftDen Q r z).eval t = (t - τ) * (ftCofactor Q r z τ).eval t := by
    conv_lhs => rw [← ftCofactor_mul hroot]
    simp
  have hW : (t - τ) * (ftRem Q B r z τ).eval t
      = B.eval t + ftAmp Q B r z τ * (ftCofactor Q r z τ).eval t := by
    have := congrArg (Polynomial.eval t) (ftRem_mul (B := B) hSτ)
    simpa using this
  have htτ : t - τ ≠ 0 := sub_ne_zero.mpr ht
  rw [hD, div_eq_iff (mul_ne_zero htτ hSt), ftErr]
  field_simp
  linear_combination -hW

/-- The analytic remainder is analytic wherever the cofactor does not vanish. -/
theorem analyticOnNhd_ftErr (Q B : ℂ[X]) (r : ℕ) (z τ : ℂ) {s : Set ℂ}
    (hS : ∀ t ∈ s, (ftCofactor Q r z τ).eval t ≠ 0) :
    AnalyticOnNhd ℂ (ftErr Q B r z τ) s :=
  AnalyticOnNhd.div (analyticOnNhd_eval _ s) (analyticOnNhd_eval _ s) hS

/-- **Paper `eq:isolated-dominant-expansion`.**  With `τ` the unique root of
`D(·,z)` in `|t| ≤ R`, the normalized coefficient `τ^{M+1}F_M(z)` equals
the residue amplitude `𝒜` up to `‖τ‖ C (‖τ‖/R)^M`.  With `τ`
the dominant root and `R` a separating radius this is the proposition's
`O(η^M)`. -/
theorem norm_ftCoeff_sub_amp_le {Q B : ℂ[X]} {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {z τ : ℂ} {R Cb : ℝ} (hR : 0 < R) (hτ0 : τ ≠ 0) (hτR : ‖τ‖ < R)
    (hroot : (ftDen Q r z).eval τ = 0)
    (hS : ∀ t ∈ closedBall (0 : ℂ) R, (ftCofactor Q r z τ).eval t ≠ 0)
    (hbd : ∀ t ∈ sphere (0 : ℂ) R, ‖ftErr Q B r z τ t‖ ≤ Cb) (M : ℕ) :
    ‖τ ^ (M + 1) * (ftCoeffPoly Q B r M).eval z - ftAmp Q B r z τ‖
      ≤ ‖τ‖ * Cb * (‖τ‖ / R) ^ M := by
  have hτmem : τ ∈ closedBall (0 : ℂ) R := by
    simp only [mem_closedBall, dist_zero_right]; exact hτR.le
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) R := by simp [hR.le]
  have hSτ := hS τ hτmem
  have hS0 := hS 0 h0mem
  set E : ℂ → ℂ := ftErr Q B r z τ with hEdef
  set F : ℂ → ℂ := fun t => -ftAmp Q B r z τ * (t - τ)⁻¹ + E t with hFdef
  have hEan : AnalyticOnNhd ℂ E (closedBall (0 : ℂ) R) := analyticOnNhd_ftErr Q B r z τ hS
  have hEdcc : DiffContOnCl ℂ E (ball (0 : ℂ) R) := by
    refine ⟨(hEan.mono ball_subset_closedBall).differentiableOn, ?_⟩
    rw [closure_ball (0 : ℂ) hR.ne']
    exact hEan.continuousOn
  obtain ⟨heq, hbound⟩ := coeff_of_simple_pole (A := -ftAmp Q B r z τ) (E := E) (F := F)
    hτ0 hR hEdcc hbd (hEan 0 h0mem) (fun t => rfl) M
  have hgerm : (fun t => B.eval t / (ftDen Q r z).eval t) =ᶠ[nhds 0] F := by
    have h1 : ∀ᶠ t in nhds (0 : ℂ), t ≠ τ :=
      (continuousAt_id (x := (0 : ℂ))).eventually_ne (Ne.symm hτ0)
    have h2 : ∀ᶠ t in nhds (0 : ℂ), (ftCofactor Q r z τ).eval t ≠ 0 :=
      (analyticAt_eval (ftCofactor Q r z τ) 0).continuousAt.eventually_ne hS0
    filter_upwards [h1, h2] with t ht hSt
    exact div_ftDen_eq hroot hSτ ht hSt
  rw [← taylorCoeff_congr hgerm M, taylorCoeff_div_ftDen Q B hr hQ0 z M] at heq
  rw [show τ ^ (M + 1) * (ftCoeffPoly Q B r M).eval z - ftAmp Q B r z τ
      = τ ^ (M + 1) * taylorCoeff E M by rw [heq]; ring]
  exact hbound

/-! ### The denominator pencil in the two parameters -/

/-- `∂_t D(t,z) = Q'(t) + z r t^{r-1}`, written out. -/
theorem eval_derivative_ftDen_eq (Q : ℂ[X]) (r : ℕ) (z τ : ℂ) :
    (derivative (ftDen Q r z)).eval τ = (derivative Q).eval τ + z * r * τ ^ (r - 1) := by
  simp only [ftDen, derivative_add, derivative_C_mul, derivative_X_pow, eval_add, eval_mul,
    eval_C, eval_pow, eval_X]
  ring

/-- Paper `prop:isolated-dominant-cancellation` — `z_0 = -Q(t_0)/t_0^r` is the
parameter at which `t_0` is a denominator root. -/
theorem ftDen_eval_fiber (Q : ℂ[X]) {r : ℕ} {t₀ z₀ : ℂ} (ht₀ : t₀ ≠ 0)
    (hz₀ : z₀ = -Q.eval t₀ / t₀ ^ r) : (ftDen Q r z₀).eval t₀ = 0 := by
  have htr : t₀ ^ r ≠ 0 := pow_ne_zero _ ht₀
  rw [ftDen_eval, hz₀]
  field

/-- The fiber map of `AttractorBranch` at a polynomial `Q` is `z_0 = -Q(t_0)/t_0^r`. -/
theorem ftBranch_eval (Q : ℂ[X]) (r : ℕ) (t : ℂ) :
    ftBranch (fun t => Q.eval t) r t = -Q.eval t / t ^ r := rfl

/-- The simplicity datum of `AttractorBranch` is `∂_t D(t_0,z_0)`. -/
theorem ftDenomFnDeriv_eq (Q : ℂ[X]) {r : ℕ} {t₀ z₀ : ℂ}
    (hz₀ : z₀ = -Q.eval t₀ / t₀ ^ r) :
    ftDenomFnDeriv (fun t => Q.eval t) r t₀ = (derivative (ftDen Q r z₀)).eval t₀ := by
  have hd : deriv (fun t => Q.eval t) t₀ = (derivative Q).eval t₀ := Q.deriv
  rw [ftDenomFnDeriv, hd, eval_derivative_ftDen_eq, ftBranch_eval, hz₀]

/-- The residue amplitude through the derivative of the denominator, which is the
form the paper writes: `𝒜 = -B(τ)/∂_t D(τ,z)`. -/
theorem ftAmp_eq_derivative {Q B : ℂ[X]} {r : ℕ} {z τ : ℂ}
    (hroot : (ftDen Q r z).eval τ = 0) :
    ftAmp Q B r z τ = -(B.eval τ / (derivative (ftDen Q r z)).eval τ) := by
  rw [ftAmp, eval_derivative_ftDen hroot]

/-- The analytic remainder, written as the pole subtraction itself. -/
theorem ftErr_eq {Q B : ℂ[X]} {r : ℕ} {z τ t : ℂ} (hroot : (ftDen Q r z).eval τ = 0)
    (hSτ : (ftCofactor Q r z τ).eval τ ≠ 0) (ht : t ≠ τ)
    (hSt : (ftCofactor Q r z τ).eval t ≠ 0) :
    ftErr Q B r z τ t
      = B.eval t / (ftDen Q r z).eval t + ftAmp Q B r z τ * (t - τ)⁻¹ := by
  have h := div_ftDen_eq (B := B) hroot hSτ ht hSt
  rw [h]; ring

/-! ### The dominant root stays alone under a small parameter move -/

/-- Paper `prop:isolated-dominant-cancellation` — the separating circle at `z_0`.
If `t_0` is the only zero of `D(·,z_0)` in `|t| ≤ R` and is simple, then
`D(·,z_0)` factors over that disk with exactly one root displayed. -/
theorem factoredOn_ftDen {Q : ℂ[X]} {r : ℕ} {z₀ t₀ : ℂ} {R : ℝ} (hR : ‖t₀‖ < R)
    (hroot : (ftDen Q r z₀).eval t₀ = 0)
    (hsimple : (derivative (ftDen Q r z₀)).eval t₀ ≠ 0)
    (hsep : ∀ t, ‖t‖ ≤ R → (ftDen Q r z₀).eval t = 0 → t = t₀) :
    FactoredOn (fun t => (ftDen Q r z₀).eval t) 0 R 1 (fun _ => t₀)
      (fun t => (ftCofactor Q r z₀ t₀).eval t) := by
  have hfac : ∀ t : ℂ, (ftDen Q r z₀).eval t = (t - t₀) * (ftCofactor Q r z₀ t₀).eval t := by
    intro t
    conv_lhs => rw [← ftCofactor_mul hroot]
    simp
  refine ⟨?_, analyticOnNhd_eval _ _, ?_, ?_⟩
  · intro j _
    simpa [mem_ball, dist_zero_right] using hR
  · intro t ht hS
    have h0 : (ftDen Q r z₀).eval t = 0 := by rw [hfac t, hS, mul_zero]
    have htR : ‖t‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using ht
    have : t = t₀ := hsep t htR h0
    subst this
    exact hsimple ((eval_derivative_ftDen hroot).trans hS)
  · intro t
    rw [Finset.prod_range_one, hfac t]

/-- Paper `prop:isolated-dominant-cancellation` — the dominant root is alone in
the disk for every nearby parameter.

**Differs from the paper's route.**  The paper shrinks the `z`-neighborhood so
that `t(z)` is the only denominator zero inside `Γ_0`, by continuity of the
roots.  Here the same conclusion is Rouché in `t`, comparing `D(·,z)` with
`D(·,z_0)` against the perturbation `(z - z_0)t^r` on `|t| = R`. -/
theorem exists_unique_root_nearby {Q : ℂ[X]} {r : ℕ} {z₀ t₀ : ℂ} {R : ℝ} (hR : ‖t₀‖ < R)
    (hroot : (ftDen Q r z₀).eval t₀ = 0)
    (hsimple : (derivative (ftDen Q r z₀)).eval t₀ ≠ 0)
    (hsep : ∀ t, ‖t‖ ≤ R → (ftDen Q r z₀).eval t = 0 → t = t₀) :
    ∃ δ > 0, ∀ z, ‖z - z₀‖ < δ → ∀ t t', ‖t‖ ≤ R → ‖t'‖ ≤ R →
      (ftDen Q r z).eval t = 0 → (ftDen Q r z).eval t' = 0 → t = t' := by
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  set f : ℂ → ℂ := fun t => (ftDen Q r z₀).eval t with hfdef
  have hfcont : ContinuousOn (fun t => ‖f t‖) (sphere (0 : ℂ) R) :=
    ((ftDen Q r z₀).continuous_aeval.norm).continuousOn
  have hpos : ∀ u ∈ sphere (0 : ℂ) R, (0 : ℝ) < ‖f u‖ := by
    intro u hu
    have huR : ‖u‖ = R := by simpa [mem_sphere, dist_zero_right] using hu
    refine norm_pos_iff.mpr fun h0 => ?_
    have := hsep u (le_of_eq huR) h0
    rw [this] at huR
    exact absurd huR (ne_of_lt hR)
  obtain ⟨m, hm, hmin⟩ :=
    IsCompact.exists_forall_le' (isCompact_sphere (0 : ℂ) R) hfcont hpos
  have hRr : (0 : ℝ) < R ^ r := pow_pos hR0 r
  refine ⟨m / R ^ r, div_pos hm hRr, ?_⟩
  intro z hz t t' ht ht' h0 h0'
  set g : ℂ → ℂ := fun t => (z - z₀) * t ^ r with hgdef
  have hsum : ∀ t : ℂ, f t + g t = (ftDen Q r z).eval t := by
    intro t; simp only [hfdef, hgdef, ftDen_eval]; ring
  have hlt : ∀ u ∈ sphere (0 : ℂ) R, ‖g u‖ < ‖f u‖ := by
    intro u hu
    have huR : ‖u‖ = R := by simpa [mem_sphere, dist_zero_right] using hu
    have : ‖g u‖ = ‖z - z₀‖ * R ^ r := by
      simp only [hgdef, norm_mul, norm_pow, huR]
    rw [this]
    calc ‖z - z₀‖ * R ^ r < (m / R ^ r) * R ^ r := by gcongr
      _ = m := by field_simp
      _ ≤ ‖f u‖ := hmin u hu
  have hfa : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) := analyticOnNhd_eval _ _
  have hga : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) R) := fun u _ =>
    analyticAt_const.mul (analyticAt_id.pow r)
  obtain ⟨n, a, a', G, G', h₁, h₂⟩ := rouche_of_analytic hR0 hfa hga hlt
  have hn : 1 = n := rouche hR0 hfa hga hlt (factoredOn_ftDen hR hroot hsimple hsep) h₂
  subst hn
  have h₃ : FactoredOn (fun u => (ftDen Q r z).eval u) 0 R 1 a' G' :=
    h₂.congr (fun u => (hsum u).symm)
  have hmt : t ∈ closedBall (0 : ℂ) R := by simpa [mem_closedBall, dist_zero_right] using ht
  have hmt' : t' ∈ closedBall (0 : ℂ) R := by simpa [mem_closedBall, dist_zero_right] using ht'
  obtain ⟨j, hj, hja⟩ := (h₃.eq_zero_iff hmt).mp h0
  obtain ⟨k, hk, hka⟩ := (h₃.eq_zero_iff hmt').mp h0'
  rw [Nat.lt_one_iff] at hj hk
  subst hj; subst hk
  rw [← hja, ← hka]

/-- The cofactor is zero-free on the disk exactly when the root it divides out is
the only one there and is simple. -/
theorem ftCofactor_ne_zero {Q : ℂ[X]} {r : ℕ} {z τ : ℂ} {R : ℝ}
    (hroot : (ftDen Q r z).eval τ = 0)
    (hsimple : (derivative (ftDen Q r z)).eval τ ≠ 0)
    (huniq : ∀ t, ‖t‖ ≤ R → (ftDen Q r z).eval t = 0 → t = τ) :
    ∀ t ∈ closedBall (0 : ℂ) R, (ftCofactor Q r z τ).eval t ≠ 0 := by
  intro t ht hS
  have htR : ‖t‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using ht
  have h0 : (ftDen Q r z).eval t = 0 := by
    conv_lhs => rw [← ftCofactor_mul hroot]
    simp [hS]
  have := huniq t htR h0
  subst this
  exact hsimple ((eval_derivative_ftDen hroot).trans hS)

/-! ### The expansion, uniformly on a parameter neighborhood -/

theorem continuous_eval (p : ℂ[X]) : Continuous (fun t : ℂ => p.eval t) := p.continuous_aeval

/-- **Paper `eq:isolated-dominant-expansion`, uniformly in the parameter.**  On a
small closed disk around `z_0` the normalized coefficient `t(z)^{M+1}F_M(z)`
agrees with the residue amplitude `𝒜(z)` to within `Cρ^M`, with one
`C` and one `ρ < 1` serving the whole disk.  `ρ` may be taken as close to
`‖t_0‖/R` as desired, `R` being any radius separating the dominant root from the
rest of the denominator's zeros. -/
theorem exists_uniform_expansion {Q B : ℂ[X]} {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {t₀ z₀ : ℂ} (ht₀ : t₀ ≠ 0)
    (hroot : (ftDen Q r z₀).eval t₀ = 0)
    (hsimple : (derivative (ftDen Q r z₀)).eval t₀ ≠ 0)
    {R : ℝ} (hR : ‖t₀‖ < R)
    (hsep : ∀ t, ‖t‖ ≤ R → (ftDen Q r z₀).eval t = 0 → t = t₀)
    {T : ℂ → ℂ} (hTan : AnalyticAt ℂ T z₀) (hTz : T z₀ = t₀)
    (hTroot : ∀ᶠ z in nhds z₀, (ftDen Q r z).eval (T z) = 0)
    {ρ : ℝ} (hρ : ‖t₀‖ / R < ρ) (hρ1 : ρ < 1) :
    ∃ ε > 0, ∃ C ≥ (0 : ℝ), ∀ z ∈ closedBall z₀ ε, ∀ M : ℕ,
      ‖T z ^ (M + 1) * (ftCoeffPoly Q B r M).eval z - ftAmp Q B r z (T z)‖ ≤ C * ρ ^ M := by
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hρ0 : 0 < ρ := lt_of_le_of_lt (by positivity) hρ
  have ht₀ρ : ‖t₀‖ < ρ * R := by
    rw [div_lt_iff₀ hR0] at hρ
    linarith
  obtain ⟨δ, hδ, huniq⟩ := exists_unique_root_nearby hR hroot hsimple hsep
  -- the parameter conditions that hold near `z₀`
  have hTcont : ContinuousAt T z₀ := hTan.continuousAt
  have hdenderiv : ContinuousAt
      (fun z => (derivative Q).eval (T z) + z * r * T z ^ (r - 1)) z₀ :=
    (((continuous_eval (derivative Q)).continuousAt).comp hTcont).add
      ((continuousAt_id.mul continuousAt_const).mul (hTcont.pow (r - 1)))
  have hd0 : (derivative Q).eval (T z₀) + z₀ * r * T z₀ ^ (r - 1) ≠ 0 := by
    rw [hTz, ← eval_derivative_ftDen_eq]; exact hsimple
  have hev : ∀ᶠ z in nhds z₀, ‖z - z₀‖ < δ ∧ ‖T z‖ < ρ * R ∧ T z ≠ 0 ∧
      (derivative Q).eval (T z) + z * r * T z ^ (r - 1) ≠ 0 ∧
      (ftDen Q r z).eval (T z) = 0 ∧ ContinuousAt T z := by
    have e1 : ∀ᶠ z in nhds z₀, ‖z - z₀‖ < δ := by
      have : ContinuousAt (fun z => ‖z - z₀‖) z₀ := (continuousAt_id.sub continuousAt_const).norm
      exact this.eventually_lt_const (by simpa using hδ)
    have hTn : ‖T z₀‖ < ρ * R := by rw [hTz]; exact ht₀ρ
    have e2 : ∀ᶠ z in nhds z₀, ‖T z‖ < ρ * R := (hTcont.norm).eventually_lt_const hTn
    have e3 : ∀ᶠ z in nhds z₀, T z ≠ 0 := hTcont.eventually_ne (by rw [hTz]; exact ht₀)
    have e4 : ∀ᶠ z in nhds z₀, (derivative Q).eval (T z) + z * r * T z ^ (r - 1) ≠ 0 :=
      hdenderiv.eventually_ne hd0
    filter_upwards [e1, e2, e3, e4, hTroot, hTan.eventually_continuousAt]
      with z h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε₀ / 2, by linarith, ?_⟩
  set ε : ℝ := ε₀ / 2 with hεdef
  have hgood : ∀ z ∈ closedBall z₀ ε, ‖z - z₀‖ < δ ∧ ‖T z‖ < ρ * R ∧ T z ≠ 0 ∧
      (derivative Q).eval (T z) + z * r * T z ^ (r - 1) ≠ 0 ∧
      (ftDen Q r z).eval (T z) = 0 ∧ ContinuousAt T z := by
    intro z hz
    refine hball ?_
    have : dist z z₀ ≤ ε := by simpa [mem_closedBall] using hz
    have hlt : ε < ε₀ := by rw [hεdef]; linarith
    exact lt_of_le_of_lt this hlt
  -- the dominant root is alone in the disk for every parameter of the neighborhood
  have hτR : ∀ z ∈ closedBall z₀ ε, ‖T z‖ < R := by
    intro z hz
    have h := (hgood z hz).2.1
    calc ‖T z‖ < ρ * R := h
      _ < 1 * R := by gcongr
      _ = R := one_mul R
  have hsimple' : ∀ z ∈ closedBall z₀ ε, (derivative (ftDen Q r z)).eval (T z) ≠ 0 := by
    intro z hz
    rw [eval_derivative_ftDen_eq]
    exact (hgood z hz).2.2.2.1
  have huniq' : ∀ z ∈ closedBall z₀ ε, ∀ t, ‖t‖ ≤ R → (ftDen Q r z).eval t = 0 → t = T z := by
    intro z hz t ht h0
    exact huniq z (hgood z hz).1 t (T z) ht (hτR z hz).le h0 (hgood z hz).2.2.2.2.1
  have hcof : ∀ z ∈ closedBall z₀ ε, ∀ t ∈ closedBall (0 : ℂ) R,
      (ftCofactor Q r z (T z)).eval t ≠ 0 := fun z hz =>
    ftCofactor_ne_zero (hgood z hz).2.2.2.2.1 (hsimple' z hz) (huniq' z hz)
  -- a single bound on the analytic remainder over the whole parameter disk
  set K : Set ℂ := closedBall z₀ ε with hK
  set S : Set ℂ := sphere (0 : ℂ) R with hS
  have hKcpt : IsCompact (K ×ˢ S) := (isCompact_closedBall z₀ ε).prod (isCompact_sphere 0 R)
  have hmemS : ∀ t ∈ S, ‖t‖ = R := by
    intro t ht; simpa [hS, mem_sphere, dist_zero_right] using ht
  have hΨden : ∀ p ∈ K ×ˢ S, Q.eval p.2 + p.1 * p.2 ^ r ≠ 0 := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩ h0
    have h0' : (ftDen Q r z).eval t = 0 := by rw [ftDen_eval]; exact h0
    have heq : t = T z := huniq' z hz t (le_of_eq (hmemS t ht)) h0'
    have h1 : ‖T z‖ < R := hτR z hz
    rw [← heq, hmemS t ht] at h1
    exact absurd h1 (lt_irrefl R)
  have hΨsub : ∀ p ∈ K ×ˢ S, p.2 - T p.1 ≠ 0 := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩ h0
    have : t = T z := sub_eq_zero.mp h0
    have h1 := hτR z hz
    rw [← this, hmemS t ht] at h1
    exact absurd h1 (lt_irrefl R)
  have hΨdd : ∀ p ∈ K ×ˢ S,
      (derivative Q).eval (T p.1) + p.1 * r * T p.1 ^ (r - 1) ≠ 0 := by
    rintro ⟨z, t⟩ ⟨hz, _⟩
    exact (hgood z hz).2.2.2.1
  have hTonK : ContinuousOn T K := fun z hz => ((hgood z hz).2.2.2.2.2).continuousWithinAt
  have hT1 : ContinuousOn (fun p : ℂ × ℂ => T p.1) (K ×ˢ S) :=
    hTonK.comp continuousOn_fst (fun p hp => hp.1)
  have hΨcont : ContinuousOn (fun p : ℂ × ℂ =>
      B.eval p.2 / (Q.eval p.2 + p.1 * p.2 ^ r)
        + -(B.eval (T p.1) / ((derivative Q).eval (T p.1) + p.1 * r * T p.1 ^ (r - 1)))
          * (p.2 - T p.1)⁻¹) (K ×ˢ S) := by
    have c1 : ContinuousOn (fun p : ℂ × ℂ => B.eval p.2) (K ×ˢ S) :=
      ((continuous_eval B).comp continuous_snd).continuousOn
    have c2 : ContinuousOn (fun p : ℂ × ℂ => Q.eval p.2 + p.1 * p.2 ^ r) (K ×ˢ S) :=
      (((continuous_eval Q).comp continuous_snd).add
        (continuous_fst.mul (continuous_snd.pow r))).continuousOn
    have c3 : ContinuousOn (fun p : ℂ × ℂ => B.eval (T p.1)) (K ×ˢ S) :=
      (continuous_eval B).continuousOn.comp hT1 (fun _ _ => Set.mem_univ _)
    have c4 : ContinuousOn
        (fun p : ℂ × ℂ => (derivative Q).eval (T p.1) + p.1 * r * T p.1 ^ (r - 1)) (K ×ˢ S) :=
      (((continuous_eval (derivative Q)).continuousOn.comp hT1 (fun _ _ => Set.mem_univ _)).add
        ((continuousOn_fst.mul continuousOn_const).mul (hT1.pow (r - 1))))
    have c5 : ContinuousOn (fun p : ℂ × ℂ => p.2 - T p.1) (K ×ˢ S) :=
      continuousOn_snd.sub hT1
    exact (c1.div c2 hΨden).add
      (((c3.div c4 hΨdd).neg).mul (c5.inv₀ hΨsub))
  obtain ⟨Cb, hCb⟩ := hKcpt.exists_bound_of_continuousOn hΨcont
  refine ⟨R * max Cb 0, by positivity, ?_⟩
  intro z hz M
  have hzK : z ∈ K := hz
  have hbd : ∀ t ∈ sphere (0 : ℂ) R, ‖ftErr Q B r z (T z) t‖ ≤ max Cb 0 := by
    intro t ht
    have htS : t ∈ S := ht
    have hne : t ≠ T z := fun h => hΨsub (z, t) ⟨hzK, htS⟩ (by simp [h])
    have hSt := hcof z hzK t (by simpa [mem_closedBall, dist_zero_right] using (hmemS t htS).le)
    have hSτ := hcof z hzK (T z)
      (by simpa [mem_closedBall, dist_zero_right] using (hτR z hzK).le)
    have heq := ftErr_eq (B := B) (hgood z hzK).2.2.2.2.1 hSτ hne hSt
    rw [heq, ftAmp_eq_derivative (hgood z hzK).2.2.2.2.1, eval_derivative_ftDen_eq, ftDen_eval]
    exact le_trans (hCb (z, t) ⟨hzK, htS⟩) (le_max_left _ _)
  have hmain := norm_ftCoeff_sub_amp_le (B := B) hr hQ0 hR0 (hgood z hzK).2.2.1 (hτR z hzK)
    (hgood z hzK).2.2.2.2.1 (hcof z hzK) hbd M
  refine hmain.trans ?_
  have hq : ‖T z‖ / R ≤ ρ := by
    rw [div_le_iff₀ hR0]
    exact (hgood z hzK).2.1.le
  have hq0 : (0 : ℝ) ≤ ‖T z‖ / R := by positivity
  have hCb0 : (0 : ℝ) ≤ max Cb 0 := le_max_right _ _
  calc ‖T z‖ * max Cb 0 * (‖T z‖ / R) ^ M
      ≤ R * max Cb 0 * ρ ^ M := by
        gcongr
        · exact (hτR z hzK).le
  _ = R * max Cb 0 * ρ ^ M := rfl

/-! ### The order of the residue amplitude -/

/-- The analytic order of a polynomial at a point is its root multiplicity there. -/
theorem analyticOrderAt_eval {B : ℂ[X]} (hB : B ≠ 0) (t₀ : ℂ) :
    analyticOrderAt (fun t => B.eval t) t₀ = (B.rootMultiplicity t₀ : ℕ∞) := by
  set ν := B.rootMultiplicity t₀ with hν
  set B₁ := B /ₘ (X - C t₀) ^ ν with hB₁
  refine (analyticAt_eval B t₀).analyticOrderAt_eq_natCast.mpr
    ⟨fun t => B₁.eval t, analyticAt_eval _ _,
      Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero t₀ hB, ?_⟩
  filter_upwards with t
  have h := congrArg (Polynomial.eval t) (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq B t₀)
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at h
  rw [smul_eq_mul, ← h]

/-- **Paper `eq:isolated-amplitude-order`.**  The residue amplitude along the
dominant branch vanishes to exactly the order to which `B` vanishes at `t_0`:
`𝒜(z) = (z - z_0)^ν𝒱(z)` with `𝒱(z_0) ≠ 0`.  The
branch has nonvanishing derivative, so it neither creates nor destroys vanishing
order. -/
theorem exists_amplitude_factorization {Q B : ℂ[X]} {r : ℕ} {t₀ z₀ : ℂ} (hB : B ≠ 0) {ν : ℕ}
    (hmult : B.rootMultiplicity t₀ = ν)
    (hsimple : (derivative (ftDen Q r z₀)).eval t₀ ≠ 0)
    {T : ℂ → ℂ} (hTan : AnalyticAt ℂ T z₀) (hTz : T z₀ = t₀) (hTd : deriv T z₀ ≠ 0)
    (hTroot : ∀ᶠ z in nhds z₀, (ftDen Q r z).eval (T z) = 0) :
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V z₀ ∧ V z₀ ≠ 0 ∧
      ∀ᶠ z in nhds z₀, ftAmp Q B r z (T z) = (z - z₀) ^ ν * V z := by
  have hcompan : AnalyticAt ℂ (fun z => B.eval (T z)) z₀ := by
    have := (analyticAt_eval B (T z₀)).comp hTan
    simpa [Function.comp_def] using this
  have hord : analyticOrderAt (fun z => B.eval (T z)) z₀ = (ν : ℕ∞) := by
    have h := analyticOrderAt_comp_of_deriv_ne_zero (f := fun t => B.eval t) hTan hTd
    rw [show (fun z => B.eval (T z)) = (fun t => B.eval t) ∘ T from rfl, h, hTz,
      analyticOrderAt_eval hB, hmult]
  obtain ⟨g, hg, hg0, hgeq⟩ := hcompan.analyticOrderAt_eq_natCast.mp hord
  -- the denominator derivative along the branch
  set Dd : ℂ → ℂ := fun z => (derivative Q).eval (T z) + z * r * T z ^ (r - 1) with hDd
  have hDdan : AnalyticAt ℂ Dd z₀ := by
    have h1 : AnalyticAt ℂ (fun z => (derivative Q).eval (T z)) z₀ := by
      have := (analyticAt_eval (derivative Q) (T z₀)).comp hTan
      simpa [Function.comp_def] using this
    exact h1.add ((analyticAt_id.mul analyticAt_const).mul (hTan.pow (r - 1)))
  have hDd0 : Dd z₀ ≠ 0 := by
    simp only [hDd]
    rw [hTz, ← eval_derivative_ftDen_eq]
    exact hsimple
  refine ⟨fun z => -(g z / Dd z), (hg.div hDdan hDd0).neg, ?_, ?_⟩
  · simp only [neg_ne_zero]
    exact div_ne_zero hg0 hDd0
  · have hDdev : ∀ᶠ z in nhds z₀, Dd z ≠ 0 := hDdan.continuousAt.eventually_ne hDd0
    filter_upwards [hgeq, hTroot, hDdev] with z hz hzroot hzD
    rw [ftAmp_eq_derivative hzroot, eval_derivative_ftDen_eq]
    simp only [hDd] at hzD ⊢
    rw [smul_eq_mul] at hz
    rw [hz]
    field_simp

/-! ### The proposition -/

/-- **Paper `prop:isolated-dominant-cancellation`.**  Let `t_0 ≠ 0` be a zero of
`B` of multiplicity `ν ≥ 1` which is a simple zero of `D(·,z_0)` and its
unique zero of minimal modulus, `z_0 = -Q(t_0)/t_0^r`.  Then there is a
neighborhood `U` of `z_0` on which, for every sufficiently large `M`, the
coefficient function `F_M` has exactly `ν` zeros counted with multiplicity —
`FactoredOn` displays them — and each of them satisfies
`eq:isolated-cancellation-rate`, `|z - z_0|^ν ≤ Kρ^M`, i.e.
`|z - z_0| = O(ρ^{M/ν})`.

`R` is any radius separating `t_0` from the other zeros of `D(·,z_0)`, and
`ρ` any number above `‖t_0‖/R`; letting `R` run over the separating radii
makes `‖t_0‖/R` approach the local spectral ratio `eq:local-spectral-ratio`, so
`ρ` may be taken anywhere in `(χ_0, 1)`.

The paper's `ν ≥ 1` is not assumed: the argument does not use it, and at
`ν = 0` the conclusion is the true statement that `F_M` has no zero near
`z_0`.

**Differs from the paper's route.**  The paper obtains
`eq:isolated-cancellation-rate` by a second Rouché argument on a shrinking disk
`|z - z_0| = C_*η^{M/ν}`.  Here the rate is pointwise: at a zero of `F_M` the two
sides of `eq:isolated-dominant-expansion` cancel, so `‖𝒜(z)‖ ≤ Cρ^M`, and
`eq:isolated-amplitude-order` turns that into `‖z - z_0‖^ν ≤ Kρ^M`.  One Rouché
argument is used, the one that fixes the count. -/
theorem isolated_dominant_cancellation {Q B : ℂ[X]} {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    (hB : B ≠ 0) {t₀ z₀ : ℂ} (ht₀ : t₀ ≠ 0) (hz₀ : z₀ = -Q.eval t₀ / t₀ ^ r)
    {ν : ℕ} (hmult : B.rootMultiplicity t₀ = ν)
    (hsimple : (derivative (ftDen Q r z₀)).eval t₀ ≠ 0)
    {R : ℝ} (hR : ‖t₀‖ < R)
    (hsep : ∀ t, ‖t‖ ≤ R → (ftDen Q r z₀).eval t = 0 → t = t₀)
    {ρ : ℝ} (hρ : ‖t₀‖ / R < ρ) (hρ1 : ρ < 1) :
    ∃ ε > 0, ∃ K ≥ (0 : ℝ), ∃ M₀ : ℕ, ∀ M ≥ M₀, ∃ (a : ℕ → ℂ) (G : ℂ → ℂ),
      FactoredOn (fun z => (ftCoeffPoly Q B r M).eval z) z₀ ε ν a G ∧
      ∀ j < ν, ‖a j - z₀‖ ^ ν ≤ K * ρ ^ M := by
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hρ0 : 0 < ρ := lt_of_le_of_lt (by positivity) hρ
  have hroot : (ftDen Q r z₀).eval t₀ = 0 := ftDen_eval_fiber Q ht₀ hz₀
  -- the dominant root branch
  have hbr : ftBranch (fun t => Q.eval t) r t₀ = z₀ := by rw [ftBranch_eval, hz₀]
  have hsimple' : ftDenomFnDeriv (fun t => Q.eval t) r t₀ ≠ 0 := by
    rw [ftDenomFnDeriv_eq Q hz₀]; exact hsimple
  obtain ⟨T, hTan, hTz, hTroot', hTderiv⟩ :=
    exists_root_branch (Q := fun t => Q.eval t) (r := r) (analyticAt_eval Q t₀) ht₀ hsimple'
  rw [hbr] at hTan hTz hTroot' hTderiv
  have hTroot : ∀ᶠ z in nhds z₀, (ftDen Q r z).eval (T z) = 0 := by
    filter_upwards [hTroot'] with z hz
    rw [ftDen_eval]; exact hz
  have hTd : deriv T z₀ ≠ 0 := by
    rw [hTderiv.deriv]
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ ht₀)) hsimple'
  -- the two analytic inputs
  obtain ⟨ε₁, hε₁, C, hC0, hexp⟩ :=
    exists_uniform_expansion (B := B) hr hQ0 ht₀ hroot hsimple hR hsep hTan hTz hTroot hρ hρ1
  obtain ⟨V, hVan, hV0, hVeq⟩ :=
    exists_amplitude_factorization (Q := Q) (r := r) hB hmult hsimple hTan hTz hTd hTroot
  -- a disk on which the amplitude is bounded below and the branch is regular
  set c : ℝ := ‖V z₀‖ / 2 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hev : ∀ᶠ z in nhds z₀, c < ‖V z‖ ∧ AnalyticAt ℂ V z ∧ T z ≠ 0 ∧ AnalyticAt ℂ T z ∧
      ftAmp Q B r z (T z) = (z - z₀) ^ ν * V z := by
    have e1 : ∀ᶠ z in nhds z₀, c < ‖V z‖ := by
      refine (hVan.continuousAt.norm).eventually_const_lt ?_
      rw [hc]
      have : 0 < ‖V z₀‖ := norm_pos_iff.mpr hV0
      linarith
    have e3 : ∀ᶠ z in nhds z₀, T z ≠ 0 :=
      hTan.continuousAt.eventually_ne (by rw [hTz]; exact ht₀)
    filter_upwards [e1, hVan.eventually_analyticAt, e3, hTan.eventually_analyticAt, hVeq]
      with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set ε : ℝ := min (ε₁ / 2) (ε₂ / 2) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεsub : ∀ z ∈ closedBall z₀ ε, c < ‖V z‖ ∧ AnalyticAt ℂ V z ∧ T z ≠ 0 ∧
      AnalyticAt ℂ T z ∧ ftAmp Q B r z (T z) = (z - z₀) ^ ν * V z := by
    intro z hz
    refine hball (lt_of_le_of_lt (by simpa [mem_closedBall] using hz) ?_)
    calc ε ≤ ε₂ / 2 := min_le_right _ _
      _ < ε₂ := by linarith
  have hεexp : ∀ z ∈ closedBall z₀ ε, ∀ M : ℕ,
      ‖T z ^ (M + 1) * (ftCoeffPoly Q B r M).eval z - ftAmp Q B r z (T z)‖ ≤ C * ρ ^ M := by
    intro z hz
    refine hexp z ?_
    have : dist z z₀ ≤ ε := by simpa [mem_closedBall] using hz
    simp only [mem_closedBall]
    calc dist z z₀ ≤ ε := this
      _ ≤ ε₁ / 2 := min_le_left _ _
      _ ≤ ε₁ := by linarith
  -- the threshold on `M`
  set C' : ℝ := max C 1 with hC'
  have hC'0 : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨M₀, hM₀⟩ : ∃ n : ℕ, ρ ^ n < c * ε ^ ν / C' :=
    exists_pow_lt_of_lt_one (by positivity) hρ1
  refine ⟨ε, hε, C / c, by positivity, M₀, ?_⟩
  intro M hM
  have hsmall : C * ρ ^ M < c * ε ^ ν := by
    have h1 : ρ ^ M ≤ ρ ^ M₀ := pow_le_pow_of_le_one hρ0.le hρ1.le hM
    have h2 : ρ ^ M < c * ε ^ ν / C' := lt_of_le_of_lt h1 hM₀
    have h3 : C' * ρ ^ M < c * ε ^ ν := by
      rw [lt_div_iff₀ hC'0] at h2
      linarith [h2]
    have h4 : C * ρ ^ M ≤ C' * ρ ^ M := by
      have : (0 : ℝ) ≤ ρ ^ M := by positivity
      nlinarith [le_max_left C 1]
    linarith
  -- Rouché in the parameter
  set f : ℂ → ℂ := fun z => (z - z₀) ^ ν * (V z * ((T z)⁻¹) ^ (M + 1)) with hfdef
  set g : ℂ → ℂ := fun z => (ftCoeffPoly Q B r M).eval z - f z with hgdef
  have hfV : ∀ z, f z = (z - z₀) ^ ν * (V z * ((T z)⁻¹) ^ (M + 1)) := fun z => rfl
  have hfA : ∀ z ∈ closedBall z₀ ε,
      f z = ftAmp Q B r z (T z) * ((T z)⁻¹) ^ (M + 1) := by
    intro z hz
    rw [hfV z, (hεsub z hz).2.2.2.2]
    ring
  have hGan : AnalyticOnNhd ℂ (fun z => V z * ((T z)⁻¹) ^ (M + 1)) (closedBall z₀ ε) := by
    intro z hz
    exact (hεsub z hz).2.1.mul (((hεsub z hz).2.2.2.1.inv (hεsub z hz).2.2.1).pow _)
  have hGne : ∀ z ∈ closedBall z₀ ε, V z * ((T z)⁻¹) ^ (M + 1) ≠ 0 := by
    intro z hz
    refine mul_ne_zero ?_ (pow_ne_zero _ (inv_ne_zero (hεsub z hz).2.2.1))
    have := (hεsub z hz).1
    exact norm_pos_iff.mp (lt_trans hc0 this)
  have hfac : FactoredOn f z₀ ε ν (fun _ => z₀) (fun z => V z * ((T z)⁻¹) ^ (M + 1)) :=
    ⟨fun j _ => by simpa using hε, hGan, hGne, fun z => by
      simp [hfV z, Finset.prod_const]⟩
  have hfan : AnalyticOnNhd ℂ f (closedBall z₀ ε) := fun z hz =>
    ((analyticAt_id.sub analyticAt_const).pow ν).mul (hGan z hz)
  have hgan : AnalyticOnNhd ℂ g (closedBall z₀ ε) := fun z hz =>
    (analyticAt_eval _ z).sub (hfan z hz)
  have hkey : ∀ z ∈ closedBall z₀ ε, ‖g z‖ ≤ ‖((T z)⁻¹) ^ (M + 1)‖ * (C * ρ ^ M) ∧
      ‖f z‖ = ‖((T z)⁻¹) ^ (M + 1)‖ * (‖z - z₀‖ ^ ν * ‖V z‖) := by
    intro z hz
    have hTne := (hεsub z hz).2.2.1
    constructor
    · have hgz : g z = ((T z)⁻¹) ^ (M + 1) *
          (T z ^ (M + 1) * (ftCoeffPoly Q B r M).eval z - ftAmp Q B r z (T z)) := by
        have hp : ((T z)⁻¹) ^ (M + 1) * T z ^ (M + 1) = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hTne, one_pow]
        simp only [hgdef]
        rw [hfA z hz]
        linear_combination (-((ftCoeffPoly Q B r M).eval z)) * hp
      rw [hgz, norm_mul]
      exact mul_le_mul_of_nonneg_left (hεexp z hz M) (norm_nonneg _)
    · rw [hfV z, norm_mul, norm_mul, norm_pow]
      ring
  have hlt : ∀ z ∈ sphere z₀ ε, ‖g z‖ < ‖f z‖ := by
    intro z hz
    have hzc : z ∈ closedBall z₀ ε := sphere_subset_closedBall hz
    have hnz : ‖z - z₀‖ = ε := by simpa [mem_sphere, dist_eq_norm] using hz
    obtain ⟨h1, h2⟩ := hkey z hzc
    have hu : 0 < ‖((T z)⁻¹) ^ (M + 1)‖ := by
      refine norm_pos_iff.mpr (pow_ne_zero _ (inv_ne_zero (hεsub z hzc).2.2.1))
    have hVz : c < ‖V z‖ := (hεsub z hzc).1
    have hlow : c * ε ^ ν ≤ ‖z - z₀‖ ^ ν * ‖V z‖ := by
      rw [hnz]
      have : (0 : ℝ) < ε ^ ν := by positivity
      nlinarith
    calc ‖g z‖ ≤ ‖((T z)⁻¹) ^ (M + 1)‖ * (C * ρ ^ M) := h1
      _ < ‖((T z)⁻¹) ^ (M + 1)‖ * (‖z - z₀‖ ^ ν * ‖V z‖) := by
          exact mul_lt_mul_of_pos_left (lt_of_lt_of_le hsmall hlow) hu
      _ = ‖f z‖ := h2.symm
  obtain ⟨n, a, a', G, G', h₁, h₂⟩ := rouche_of_analytic hε hfan hgan hlt
  have hn : ν = n := rouche hε hfan hgan hlt hfac h₂
  subst hn
  have h₃ : FactoredOn (fun z => (ftCoeffPoly Q B r M).eval z) z₀ ε ν a' G' := by
    refine h₂.congr fun z => ?_
    rw [hgdef]
    ring
  refine ⟨a', G', h₃, ?_⟩
  intro j hj
  have hmem : a' j ∈ ball z₀ ε := h₃.mem_ball j hj
  have hmemc : a' j ∈ closedBall z₀ ε := ball_subset_closedBall hmem
  have hzero : (ftCoeffPoly Q B r M).eval (a' j) = 0 := by
    rw [h₃.eq (a' j), Finset.prod_eq_zero_iff.mpr ⟨j, Finset.mem_range.mpr hj, sub_self _⟩,
      zero_mul]
  obtain ⟨h1, h2⟩ := hkey (a' j) hmemc
  have hu : 0 < ‖((T (a' j))⁻¹) ^ (M + 1)‖ :=
    norm_pos_iff.mpr (pow_ne_zero _ (inv_ne_zero (hεsub (a' j) hmemc).2.2.1))
  have hgz : g (a' j) = -f (a' j) := by simp only [hgdef]; rw [hzero]; ring
  have hfg : ‖f (a' j)‖ = ‖g (a' j)‖ := by rw [hgz, norm_neg]
  have hVz : c < ‖V (a' j)‖ := (hεsub (a' j) hmemc).1
  have hchain : ‖a' j - z₀‖ ^ ν * ‖V (a' j)‖ ≤ C * ρ ^ M := by
    have hle : ‖((T (a' j))⁻¹) ^ (M + 1)‖ * (‖a' j - z₀‖ ^ ν * ‖V (a' j)‖)
        ≤ ‖((T (a' j))⁻¹) ^ (M + 1)‖ * (C * ρ ^ M) := by
      rw [← h2, hfg]; exact h1
    exact le_of_mul_le_mul_left hle hu
  have hpos : (0 : ℝ) ≤ ‖a' j - z₀‖ ^ ν := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  nlinarith [hchain, hVz, hpos]

/-- **Paper `rem:cancellation-meaning`, `eq:cancellation-intersection-multiplicity`.**
The canonical Laurent restriction writes `N(t,g(t)) = t^{λ_N}B_N(t)`, and
at a nonzero point the monomial factor does not change vanishing order:
`\operatorname{ord}_{t_0}(t^kB) = \operatorname{ord}_{t_0}B`.  Together with
`AttractorBranch.deriv_ftBranch`, which gives `g'(t_0) ≠ 0` exactly when `t_0`
is a simple denominator root, this identifies the packet multiplicity `ν` of
`isolated_dominant_cancellation` with the local intersection multiplicity of the
numerator and denominator curves. -/
theorem rootMultiplicity_monomial_mul (B : ℂ[X]) {t₀ : ℂ} (ht₀ : t₀ ≠ 0) (k : ℕ) :
    ((X : ℂ[X]) ^ k * B).rootMultiplicity t₀ = B.rootMultiplicity t₀ := by
  rcases eq_or_ne B 0 with rfl | hB
  · simp
  · have hX : ((X : ℂ[X]) ^ k).rootMultiplicity t₀ = 0 := by
      refine Polynomial.rootMultiplicity_eq_zero ?_
      simp [Polynomial.IsRoot, ht₀]
    rw [Polynomial.rootMultiplicity_mul (by simpa using hB), hX, zero_add]

end ForgacsTran
