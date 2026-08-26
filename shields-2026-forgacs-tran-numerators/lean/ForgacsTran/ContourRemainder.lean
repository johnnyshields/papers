/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Amplitude

/-!
# The contour remainder and its decay

`ClusterContour` carries the *invariance* half of `lem:contour-separation` — that
the integral does not depend on which enclosing circle is used.  This module
carries the *decay* half.

## Main statements

* `exists_contour_const` — `C_Γ = sup_Γ |B/D|` is finite, by compactness of the
  circle; it is produced from the integrand rather than posited.
* `norm_contourRemainder_le` — `eq:contour-remainder-bound`.  For the circle
  `|t| = R` the paper's `L_Γ C_Γ/(2π) · R_Γ^{-M-1}` is `C_Γ R^{-M}`, and the
  `M`-dependence is derived from the `t^{-M-1}` in the integrand, not assumed.
* `norm_smul_contourRemainder_le` — the normalized form: scaling by `ρ^{M+1}`
  with `ρ < R` turns the bound into `ρ C_Γ σ^M`, `σ = ρ/R < 1`.

## Implementation notes

Circles rather than a general rectifiable Jordan curve: the paper states
`lem:contour-separation` for an arbitrary such curve, but every use of it fixes
circles (`prop:local-strong-clock` covers a compact parameter interval by pieces
"carrying fixed circles"), and `L_Γ = 2πR` is then read off the contour.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Contour-separated
residues» (`sec:geometry`, `subsec:contour-residues`, `lem:contour-separation`,
`eq:contour-remainder-bound`), and the principal decomposition it feeds
(`subsec:principal-amplitude`, `eq:principal-decomposition`).

## Tags

contour integral, remainder decay, pole expansion
-/

namespace ForgacsTran

open Polynomial Metric Real Shields

/-- **`eq:contour-separated-expansion`.**  The contour remainder
`E_M = (1/2πi)∮_{|t|=R} B(t)/(t^{M+1}D(t)) dt`. -/
noncomputable def contourRemainder (B : Polynomial ℂ) (D : ℂ → ℂ) (R : ℝ) (M : ℕ) : ℂ :=
  (1 / (2 * (π : ℂ) * Complex.I)) * ∮ t in C(0, R), B.eval t / (t ^ (M + 1) * D t)

/-- **`C_Γ` exists.**  On a circle where `D` is continuous and nonvanishing, the
integrand's `M`-free factor `B/D` is bounded — by compactness, not by fiat.  This
is what makes `eq:contour-remainder-bound` a statement rather than a definition
of its own constant. -/
theorem exists_contour_const (B : Polynomial ℂ) {D : ℂ → ℂ} {R : ℝ}
    (hD : ContinuousOn D (sphere (0 : ℂ) R)) (hne : ∀ t ∈ sphere (0 : ℂ) R, D t ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t / D t‖ ≤ C := by
  have hcont : ContinuousOn (fun t => ‖B.eval t / D t‖) (sphere (0 : ℂ) R) :=
    ((((Polynomial.continuous B).continuousOn).div hD hne)).norm
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  exact le_trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC t ht)
    (le_max_left _ _)

/-- **`eq:contour-remainder-bound`.**  With `C_Γ` bounding `B/D` on the circle
`|t| = R`, the remainder decays geometrically in `M`:
`|E_M| ≤ L_Γ C_Γ/(2π) · R^{-M-1} = C_Γ R^{-M}`.

The `M`-dependence comes out of the `t^{-M-1}` in the integrand — on the circle
`‖t‖ = R`, so that factor contributes exactly `R^{-M-1}` — and the length
`L_Γ = 2πR` comes out of the contour.  Neither is assumed.
**Differs from the paper's route.**  `lem:contour-separation` states this for an arbitrary
rectifiable
Jordan contour, with `L_Γ` its length.  Mathlib's circle integral is over
`sphere 0 R`, so the estimate is taken there and `L_Γ = 2πR` is read off the
contour; the paper's `L_Γ C_Γ/(2π) · R^{-M-1}` is then `C_Γ R^{-M}`.
-/
theorem norm_contourRemainder_le {B : Polynomial ℂ} {D : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hC : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t / D t‖ ≤ C) (M : ℕ) :
    ‖contourRemainder B D R M‖ ≤ C / R ^ M := by
  have hRM : (0 : ℝ) < R ^ (M + 1) := pow_pos hR (M + 1)
  -- the integrand on the circle
  have hbd : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t / (t ^ (M + 1) * D t)‖ ≤ C / R ^ (M + 1) := by
    intro t ht
    have hnt : ‖t‖ = R := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 ht
    have hsplit : B.eval t / (t ^ (M + 1) * D t) = B.eval t / D t / t ^ (M + 1) := by
      rw [div_div, mul_comm]
    rw [hsplit, norm_div, norm_pow, hnt]
    exact div_le_div_of_nonneg_right (hC t ht) hRM.le
  have hint := circleIntegral.norm_integral_le_of_norm_le_const hR.le hbd
  -- the `1/(2πi)` prefactor
  have hpre : ‖(1 / (2 * (π : ℂ) * Complex.I))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos pi_pos]
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [contourRemainder, norm_mul, hpre]
  calc 1 / (2 * π) * ‖∮ t in C(0, R), B.eval t / (t ^ (M + 1) * D t)‖
      ≤ 1 / (2 * π) * (2 * π * R * (C / R ^ (M + 1))) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = C / R ^ M := by
        rw [pow_succ]
        field_simp

/-- **The normalized form.**  Scaling by any `ρ^{M+1}` with `0 ≤ ρ < R` turns
`eq:contour-remainder-bound` into a bound of order `σ^M` with `σ = ρ/R < 1`,
which is how the paper uses it after normalizing by `τ^{M+1}`. -/
theorem norm_smul_contourRemainder_le {B : Polynomial ℂ} {D : ℂ → ℂ} {R C ρ : ℝ}
    (hR : 0 < R) (hρ : 0 ≤ ρ)
    (hC : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t / D t‖ ≤ C) (M : ℕ) :
    ‖((ρ : ℂ)) ^ (M + 1) * contourRemainder B D R M‖ ≤ ρ * C * (ρ / R) ^ M := by
  have hRM : (0 : ℝ) < R ^ M := pow_pos hR M
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]
  calc ρ ^ (M + 1) * ‖contourRemainder B D R M‖
      ≤ ρ ^ (M + 1) * (C / R ^ M) :=
        mul_le_mul_of_nonneg_left (norm_contourRemainder_le hR hC M) (by positivity)
    _ = ρ * C * (ρ / R) ^ M := by rw [div_pow, pow_succ]; field_simp


/-! ### Two simple poles subtracted

`eq:principal-decomposition` groups the *pair* of principal residues, so the
single-pole subtraction of `AttractorPole.div_ftDen_eq` is not enough: two roots
sit inside the separating circle.  What follows is that subtraction carried out
for two distinct simple roots, at the level of polynomials. -/

/-- Two distinct roots divide out together. -/
private theorem exists_factor_two_roots {P : Polynomial ℂ} {a b : ℂ} (hab : a ≠ b)
    (ha : P.eval a = 0) (hb : P.eval b = 0) :
    ∃ S : Polynomial ℂ, P = (X - C a) * ((X - C b) * S) := by
  obtain ⟨S₁, hS₁⟩ := (dvd_iff_isRoot (a := a) (p := P)).2 ha
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hS₁b : S₁.eval b = 0 := by
    have h := congrArg (Polynomial.eval b) hS₁
    simp only [hb, eval_mul, eval_sub, eval_X, eval_C] at h
    rcases mul_eq_zero.1 h.symm with h' | h'
    · exact absurd h' hba
    · exact h'
  obtain ⟨S₂, hS₂⟩ := (dvd_iff_isRoot (a := b) (p := S₁)).2 hS₁b
  exact ⟨S₂, by rw [hS₁, hS₂]⟩

/-- **The two-pole subtraction.**  At two distinct nonzero simple roots `a ≠ b`
of `D`, the rational function `B/D` is the two simple poles of amplitudes
`B(a)/D'(a)` and `B(b)/D'(b)` plus `G/S`, where `D = (X-a)(X-b)S`.  This is
`eq:contour-separated-expansion` for a contour enclosing exactly the pair, with
the residues in the form `eq:simple-residue-amplitude` gives them. -/
theorem exists_two_pole_decomposition {B D : Polynomial ℂ} {a b : ℂ} (hab : a ≠ b)
    (ha : D.eval a = 0) (hb : D.eval b = 0)
    (hDa : (derivative D).eval a ≠ 0) (hDb : (derivative D).eval b ≠ 0) :
    ∃ (S G : Polynomial ℂ), D = (X - C a) * ((X - C b) * S) ∧
      S.eval a ≠ 0 ∧ S.eval b ≠ 0 ∧
      ∀ t : ℂ, S.eval t ≠ 0 → t ≠ a → t ≠ b →
        B.eval t / D.eval t
          = (B.eval a / (derivative D).eval a) * (t - a)⁻¹
            + (B.eval b / (derivative D).eval b) * (t - b)⁻¹
            + G.eval t / S.eval t := by
  obtain ⟨S, hS⟩ := exists_factor_two_roots hab ha hb
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hba' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- the derivative at each root, in terms of `S`
  have hD'a : (derivative D).eval a = (a - b) * S.eval a := by
    rw [hS]; simp [derivative_mul]
  have hD'b : (derivative D).eval b = (b - a) * S.eval b := by
    rw [hS]; simp [derivative_mul]
  have hSa : S.eval a ≠ 0 := fun h => hDa (by rw [hD'a, h, mul_zero])
  have hSb : S.eval b ≠ 0 := fun h => hDb (by rw [hD'b, h, mul_zero])
  set Aa : ℂ := B.eval a / (derivative D).eval a with hAa
  set Ab : ℂ := B.eval b / (derivative D).eval b with hAb
  set N : Polynomial ℂ := B - C Aa * ((X - C b) * S) - C Ab * ((X - C a) * S) with hN
  have hNa : N.eval a = 0 := by
    simp only [hN, eval_sub, eval_mul, eval_C, eval_X, sub_self, zero_mul, mul_zero]
    rw [hAa, hD'a]
    field
  have hNb : N.eval b = 0 := by
    simp only [hN, eval_sub, eval_mul, eval_C, eval_X, sub_self, zero_mul, mul_zero]
    rw [hAb, hD'b]
    field
  obtain ⟨G, hG⟩ := exists_factor_two_roots hab hNa hNb
  refine ⟨S, G, hS, hSa, hSb, fun t hSt hta htb => ?_⟩
  have hta' : t - a ≠ 0 := sub_ne_zero.mpr hta
  have htb' : t - b ≠ 0 := sub_ne_zero.mpr htb
  have hDt : D.eval t = (t - a) * ((t - b) * S.eval t) := by rw [hS]; simp
  have hNt : B.eval t - Aa * ((t - b) * S.eval t) - Ab * ((t - a) * S.eval t)
      = (t - a) * ((t - b) * G.eval t) := by
    have h := congrArg (Polynomial.eval t) hG
    simpa [hN] using h
  have hNt' : B.eval t
      = Aa * ((t - b) * S.eval t) + Ab * ((t - a) * S.eval t)
        + G.eval t * ((t - a) * (t - b)) := by linear_combination hNt
  have key : Aa * (t - a)⁻¹ + Ab * (t - b)⁻¹ + G.eval t / S.eval t
      = (Aa * ((t - b) * S.eval t) + Ab * ((t - a) * S.eval t)
          + G.eval t * ((t - a) * (t - b))) / ((t - a) * ((t - b) * S.eval t)) := by
    field_simp
  rw [hDt, key, hNt']


/-! ### The coefficient of a two-pole function -/

private theorem taylorCoeff_fun_add {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (M : ℕ) : taylorCoeff (fun t => F t + G t) M = taylorCoeff F M + taylorCoeff G M := by
  rw [taylorCoeff, iteratedDeriv_fun_add hF.contDiffAt hG.contDiffAt, mul_add, ← taylorCoeff,
    ← taylorCoeff]

private theorem taylorCoeff_const_mul_inv_sub {A a : ℂ} (ha : a ≠ 0) (M : ℕ) :
    taylorCoeff (fun t : ℂ => A * (t - a)⁻¹) M = A * -(a ^ (M + 1))⁻¹ := by
  rw [taylorCoeff, iteratedDeriv_const_mul_field, ← mul_assoc,
    mul_comm ((((Nat.factorial M : ℕ)) : ℂ))⁻¹ A, mul_assoc, ← taylorCoeff,
    taylorCoeff_inv_sub ha]

/-- **`eq:contour-separated-expansion`, coefficient form for a pair.**  Two simple
poles at nonzero `a ≠ b` plus an analytic remainder contribute
`-A_a a^{-M-1} - A_b b^{-M-1}` to `[t^M]`. -/
theorem coeff_of_two_simple_poles {a b Aa Ab : ℂ} {E F : ℂ → ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hEan : AnalyticAt ℂ E 0)
    (hF : ∀ t, F t = Aa * (t - a)⁻¹ + Ab * (t - b)⁻¹ + E t) (M : ℕ) :
    taylorCoeff F M
      = -(Aa * (a ^ (M + 1))⁻¹) - (Ab * (b ^ (M + 1))⁻¹) + taylorCoeff E M := by
  have hsa : (0 : ℂ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hsb : (0 : ℂ) - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hpa : AnalyticAt ℂ (fun t : ℂ => Aa * (t - a)⁻¹) 0 :=
    analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv hsa)
  have hpb : AnalyticAt ℂ (fun t : ℂ => Ab * (t - b)⁻¹) 0 :=
    analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv hsb)
  have hFeq : F = fun t => Aa * (t - a)⁻¹ + (Ab * (t - b)⁻¹ + E t) := by
    funext t; rw [hF t]; ring
  have hpbE : AnalyticAt ℂ (fun t : ℂ => Ab * (t - b)⁻¹ + E t) 0 := hpb.add hEan
  rw [hFeq, taylorCoeff_fun_add hpa hpbE M, taylorCoeff_fun_add hpb hEan M,
    taylorCoeff_const_mul_inv_sub ha, taylorCoeff_const_mul_inv_sub hb]
  ring

/-! ### `eq:principal-decomposition`, with `R_M` produced -/

/-- **`eq:principal-decomposition`.**  For a parameter at which the principal
conjugate pair `t_± = τ e^{±iθ}` are distinct simple denominator zeros, the
normalized coefficient splits as
`τ^{M+1}F_M(z) = 2 Re(W e^{-i(M+1)θ}) + τ^{M+1}[t^M]E`,
with `E = G/S` the *explicit* analytic remainder left when the pair is divided
out — `D = (t-t_+)(t-t_-)S`.  Nothing here is assumed: the pole structure comes
from `exists_two_pole_decomposition`, the coefficient extraction from
`coeff_of_two_simple_poles`, and the grouping from
`Amplitude.principal_pair_contribution`.

Combined with `norm_contourRemainder_le` (or with `AttractorExpansion.norm_taylorCoeff_le`
applied to `E` on a separating circle), `R_M = τ^{M+1}[t^M]E` is `O(σ^M)`.
**Differs from the paper's route.**  The paper reaches `eq:principal-decomposition` through the
residue
expansion `eq:contour-separated-expansion` of `lem:contour-separation`.  Here the
pair is divided out algebraically instead — `exists_two_pole_decomposition`
writes `B/D` as its two simple poles plus `G/S`, with `D = (t-t_+)(t-t_-)S` — so
no contour and no residue theorem enters, and `R_M` is the Taylor coefficient of
an explicit rational remainder.
-/
theorem principal_decomposition_of_pair {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {τ θ z : ℝ} (hτ : 0 < τ) (M : ℕ)
    (hne : (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
         ≠ (τ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))
    (hroot : (ftDen Q r (z : ℂ)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0)
    (hsa : (derivative (ftDen Q r (z : ℂ))).eval
              ((τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0)
    (hsb : (derivative (ftDen Q r (z : ℂ))).eval
              ((τ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)) ≠ 0) :
    ∃ S G : Polynomial ℂ,
      ftDen Q r (z : ℂ)
          = (X - C ((τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
            * ((X - C ((τ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))) * S) ∧
        S.eval 0 ≠ 0 ∧
        ((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (z : ℂ)
          = ((2 * (ftAmp Q B r (z : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                * Complex.exp (((-(((M : ℝ) + 1) * θ) : ℝ) : ℂ) * Complex.I)).re : ℝ) : ℂ)
            + ((τ : ℂ)) ^ (M + 1)
              * taylorCoeff (fun t => G.eval t / S.eval t) M := by
  set a : ℂ := (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hadef
  set b : ℂ := (τ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) with hbdef
  have hτ0 : ((τ : ℂ)) ≠ 0 := by exact_mod_cast hτ.ne'
  have ha0 : a ≠ 0 := mul_ne_zero hτ0 (Complex.exp_ne_zero _)
  have hb0 : b ≠ 0 := mul_ne_zero hτ0 (Complex.exp_ne_zero _)
  have hconj : (starRingEnd ℂ) a = b := conj_polar τ θ
  have hrootb : (ftDen Q r (z : ℂ)).eval b = 0 := by
    rw [← hconj]; exact ftDen_eval_conj_eq_zero hQ hroot
  obtain ⟨S, G, hS, hSa, hSb, hdec⟩ :=
    exists_two_pole_decomposition (B := B) (D := ftDen Q r (z : ℂ)) hne hroot hrootb hsa hsb
  have hS0 : S.eval 0 ≠ 0 := by
    intro h
    have hev : (ftDen Q r (z : ℂ)).eval 0 = 0 := by rw [hS]; simp [h]
    rw [ftDen_eval, zero_pow (by omega : r ≠ 0), mul_zero, add_zero] at hev
    exact hQ0 hev
  refine ⟨S, G, hS, hS0, ?_⟩
  -- the analytic remainder
  set E : ℂ → ℂ := fun t => G.eval t / S.eval t with hEdef
  have hEan : AnalyticAt ℂ E 0 :=
    (analyticAt_eval G 0).div (analyticAt_eval S 0) hS0
  -- the decomposition holds near the origin
  set F : ℂ → ℂ := fun t =>
    (B.eval a / (derivative (ftDen Q r (z : ℂ))).eval a) * (t - a)⁻¹
    + (B.eval b / (derivative (ftDen Q r (z : ℂ))).eval b) * (t - b)⁻¹ + E t with hFdef
  have hgerm : (fun t => B.eval t / (ftDen Q r (z : ℂ)).eval t) =ᶠ[nhds 0] F := by
    have h1 : ∀ᶠ t in nhds (0 : ℂ), S.eval t ≠ 0 :=
      (analyticAt_eval S 0).continuousAt.eventually_ne hS0
    have h2 : ∀ᶠ t in nhds (0 : ℂ), t ≠ a :=
      (continuousAt_id (x := (0 : ℂ))).eventually_ne (Ne.symm ha0)
    have h3 : ∀ᶠ t in nhds (0 : ℂ), t ≠ b :=
      (continuousAt_id (x := (0 : ℂ))).eventually_ne (Ne.symm hb0)
    filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
    exact hdec t ht1 ht2 ht3
  -- extract the coefficient
  have hcoeff := coeff_of_two_simple_poles (E := E) (F := F) ha0 hb0 hEan (fun t => rfl) M
  rw [← taylorCoeff_congr hgerm M, taylorCoeff_div_ftDen Q B hr hQ0 z M] at hcoeff
  -- rewrite the two amplitudes as `ftAmp`
  have hAa : -(B.eval a / (derivative (ftDen Q r (z : ℂ))).eval a) = ftAmp Q B r (z : ℂ) a := by
    rw [ftAmp_eq_neg_div_derivative hroot, neg_div]
  have hAb : -(B.eval b / (derivative (ftDen Q r (z : ℂ))).eval b) = ftAmp Q B r (z : ℂ) b := by
    rw [ftAmp_eq_neg_div_derivative hrootb, neg_div]
  have hexp : (ftCoeffPoly Q B r M).eval (z : ℂ)
      = ftAmp Q B r (z : ℂ) a / a ^ (M + 1) + ftAmp Q B r (z : ℂ) b / b ^ (M + 1)
        + taylorCoeff E M := by
    rw [hcoeff, ← hAa, ← hAb]
    field
  have := principal_decomposition (Q := Q) (B := B) hQ hB (r := r) (M := M) (τ := τ)
    (θ := θ) (z := z) hτ (FM := (ftCoeffPoly Q B r M).eval (z : ℂ)) (EM := taylorCoeff E M)
    hroot hexp
  exact this

end ForgacsTran
