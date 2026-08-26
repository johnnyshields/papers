/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Degree

/-!
# Sharpness of the threshold `κ = 1`, uniformly in `a`

Formalizes `shields-2026-turan-bessel.tex`, «The exceptional degree and endpoint
sufficiency» (`subsec:endpoint-sufficiency`, `rem:uniform-degree-one`,
`eq:MD01-kappa`): degree one alone rules out every `κ < 1` that is to serve all
`a > 0` at once.  For the one-parameter family, the degree-one coefficient of the
determinant is a positive multiple of `MD(N_0, N_1^{(κ)})`, and
```
MD(N_0, N_1^{(κ)}) = MD(N_0, N_1) + ψ₁(a)·(κ-1)/2      (eq:MD01-kappa)
                   = (aψ₁(a)-1)/(a²ψ₁(a)) + ψ₁(a)(κ-1)/2.
```
For `κ ≥ 1` this is `> 0` at every `a > 0` (`MDkappa_ge_pos`).  For `κ < 1`,
taking `a = (1-κ)/2` and using `ψ₁(a) ≥ a⁻²` (the first series term) makes it
`< 0` (`MDkappa_neg_exists`).  So degree-one positivity *uniform in `a`* holds
exactly for `κ ≥ 1` (`MDkappa_uniform_iff`).

The **fixed-`a`** converse of `thm:coefficientwise` — for each `a > 0`,
positivity of every `Δ_n^{(κ)}(a)` forces `κ ≥ 1` — is not established here, and
degree one cannot deliver it: at fixed `a` the degree-one coefficient stays
positive for `κ` just below `1`.  The paper defers that converse to the necessity
part of `thm:two-parameter-coeff`, which routes through
`lem:large-argument-limit`; both are recorded as missing in `../README.md`.  The
same boundary applies to `prop:bessel-sharpness`, whose sharp quadrant is the
two-parameter `κ ≥ 1, τ ≥ 1` for `D_ν^{(κ,τ)}(z) > 0` at every `z > 0`; only its
`κ ≥ 1` deformation direction is what `MDkappa_ge_pos` speaks to.

Sorry-free.
-/

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
  field

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

/-- **Uniform sharpness** (`rem:uniform-degree-one`): the degree-one coefficient is
positive at *every* `a > 0` exactly when `κ ≥ 1`.  This is the uniform-in-`a`
statement; the fixed-`a` converse of `thm:coefficientwise` is a different, stronger
claim and is not proved here. -/
theorem MDkappa_uniform_iff (κ : ℝ) :
    (∀ a : ℝ, 0 < a → 0 < SymMat.MD (Nmat a 0) (N1kappa a κ)) ↔ 1 ≤ κ := by
  constructor
  · intro h
    by_contra hκ
    push Not at hκ
    obtain ⟨a, ha, hneg⟩ := MDkappa_neg_exists hκ
    exact absurd (h a ha) (not_lt.mpr hneg.le)
  · intro hκ a ha
    exact MDkappa_ge_pos ha hκ

end TuranBessel
