/-
# Sharpness of the threshold `κ = 1`

Completes the "if and only if" of `shields-2026-turan-bessel.tex`,
§2 «Main results» `thm:coefficientwise` and the deformation half of
`prop:bessel-sharpness` (`D_ν^{(κ)}>0` for all `ν>-1,z>0` iff `κ≥1`); the
sharpness computation `eq:MD01-kappa` lives in §7 «Mixed determinants and
coefficientwise positivity» (`sec:determinant`).
For the one-parameter family, the degree-one coefficient
of the determinant is a positive multiple of `MD(N_0, N_1^{(κ)})`, and
```
MD(N_0, N_1^{(κ)}) = MD(N_0, N_1) + ψ₁(a)·(κ-1)/2      (eq:MD01-kappa)
                   = (aψ₁(a)-1)/(a²ψ₁(a)) + ψ₁(a)(κ-1)/2.
```
For `κ ≥ 1` this is `> 0` (`MDkappa_ge_pos`).  For `κ < 1`, taking `a = (1-κ)/2`
and using `ψ₁(a) ≥ a⁻²` (the first series term) makes it `< 0`
(`MDkappa_neg_exists`).  Hence uniform coefficientwise positivity holds iff `κ≥1`.

Sorry-free.
-/
import TuranBessel.Degree

namespace TuranBessel

variable {a : ℝ}

/-- The degree-one coefficient matrix `N_1^{(κ)}` of the `κ`-family: `c_1^{(κ)} =
(κ-1)/2`, so `a22 = g⁻¹ + (κ-1)/2`. -/
noncomputable def N1kappa (a κ : ℝ) : SymMat :=
  ⟨αcoef a 1, βcoef a 1, (trigamma a)⁻¹ + (κ - 1) / 2⟩

/-- `MD(N_0, N_1^{(κ)}) = (aψ₁(a)-1)/(a²ψ₁(a)) + ψ₁(a)(κ-1)/2` (eq:MD01-kappa). -/
theorem MDkappa_eq (ha : 0 < a) (κ : ℝ) :
    SymMat.MD (Nmat a 0) (N1kappa a κ)
      = (a * trigamma a - 1) / (a ^ 2 * trigamma a) + trigamma a * (κ - 1) / 2 := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have ht1 : trigamma (a + 1) = trigamma a - (a ^ 2)⁻¹ := trigamma_succ' ha
  simp only [SymMat.MD, N1kappa, Nmat_a11, Nmat_a12, Nmat_a22, αcoef, βcoef_zero, βcoef_one,
    ccoef_zero, Nat.cast_zero, Nat.cast_one, add_zero]
  rw [ht1]
  field_simp
  ring

/-- **Forward:** for `κ ≥ 1` the degree-one coefficient is strictly positive. -/
theorem MDkappa_ge_pos (ha : 0 < a) {κ : ℝ} (hκ : 1 ≤ κ) :
    0 < SymMat.MD (Nmat a 0) (N1kappa a κ) := by
  rw [MDkappa_eq ha]
  have hg := trigamma_pos ha
  have hfirst : 0 < (a * trigamma a - 1) / (a ^ 2 * trigamma a) :=
    div_pos (by linarith [a_trigamma_gt_one ha]) (mul_pos (pow_pos ha 2) hg)
  have hsecond : 0 ≤ trigamma a * (κ - 1) / 2 :=
    div_nonneg (mul_nonneg hg.le (by linarith)) (by norm_num)
  linarith

/-- **Converse:** for `κ < 1` there is `a > 0` with the degree-one coefficient
strictly negative — so uniform positivity fails. -/
theorem MDkappa_neg_exists {κ : ℝ} (hκ : κ < 1) :
    ∃ a : ℝ, 0 < a ∧ SymMat.MD (Nmat a 0) (N1kappa a κ) < 0 := by
  refine ⟨(1 - κ) / 2, by linarith, ?_⟩
  set a := (1 - κ) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hg := trigamma_pos ha
  have hge : (a ^ 2)⁻¹ ≤ trigamma a := by
    have hrec := trigamma_succ' ha
    have hnn : 0 ≤ trigamma (a + 1) := by
      rw [trigamma]; exact tsum_nonneg (fun n => by positivity)
    linarith
  have hs : (1 : ℝ) - κ ≠ 0 := by linarith
  rw [MDkappa_eq ha]
  have h1 : (a * trigamma a - 1) / (a ^ 2 * trigamma a) < 1 / a := by
    have hpos : 0 < 1 / (a ^ 2 * trigamma a) :=
      one_div_pos.mpr (mul_pos (pow_pos ha 2) hg)
    have heq : 1 / a - (a * trigamma a - 1) / (a ^ 2 * trigamma a) = 1 / (a ^ 2 * trigamma a) := by
      field_simp; ring
    linarith
  have h2 : trigamma a * (κ - 1) / 2 ≤ -((1 - κ) / (2 * a ^ 2)) := by
    have hle : trigamma a * (κ - 1) ≤ (a ^ 2)⁻¹ * (κ - 1) :=
      mul_le_mul_of_nonpos_right hge (by linarith)
    have hrw : -((1 - κ) / (2 * a ^ 2)) = (a ^ 2)⁻¹ * (κ - 1) / 2 := by
      field_simp; ring
    rw [hrw]; linarith
  have heq0 : 1 / a = (1 - κ) / (2 * a ^ 2) := by
    rw [ha_def]; field_simp
  linarith

end TuranBessel
