/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.ParameterCalculus
import TuranBessel.Phase

/-!
# The boundary chain of `lem:boundary-positivity`

`shields-2026-turan-bessel.tex`, `app:boundary-proof` (`lem:boundary-positivity`),
serving `sec:phase` (`thm:two-parameter-coeff`, `eq:coefficient-wall-factor`).

At the coefficientwise boundary `κ = 1`, `τ = τ_*` the degree-one coefficient
vanishes and every higher one is strictly positive.  The four facts about
`N̂_m = N_m^{(1,τ_*)}` the paper establishes are proved here in its order:

    N̂_m ≻ 0                (m ≥ 2)     `NmatHat_pd`
    MD(N̂_0, N̂_m) > 0       (m ≥ 2)     `MD_NmatHat_zero_pos`
    MD(N̂_1, N̂_m) > 0       (m ≥ 2)     `MD_NmatHat_one_pos`
    Δ̂_2 > 0                            `DcoeffKT_boundary_two_pos`

and assembled in `boundary_positivity`.

Two of the four come out shorter than they read.  `Λ_m` is a single hyperbola,

    Λ_m = s_* + (3-4a)/4 + (1-2a)/(4(2a+2m-3)),

so `eq:Lm-derivative`, the `m → ∞` limit and the `m = 2` minimum are three
readings of one identity, and the sign of `1-2a` alone decides which end of
`m ≥ 2` is extremal — no derivative and no limit.  And the telescoping estimate
of step 2 is one induction on the *inequality*
`ψ₁(a+1) - ψ₁(a+m) ≤ (a+1/2)⁻¹ - (a+m-1/2)⁻¹`, rather than an identity followed
by a bound, because the bound telescopes in exactly the shape the identity does.

Sorry-free.
-/

namespace TuranBessel

variable {a : ℝ} {m n : ℕ}

/-- The certificate polynomial of step 2, in the paper's shifted variables
`ã = a - 1/2`, `m̃ = m - 2`.  Every one of its sixteen coefficients is positive,
which is the whole content of the step. -/
def Pcert (A M : ℝ) : ℝ :=
  2 * A ^ 4 * M + 8 * A ^ 4 + 4 * A ^ 3 * M ^ 2 + 23 * A ^ 3 * M + 26 * A ^ 3
    + 2 * A ^ 2 * M ^ 3 + 19 * A ^ 2 * M ^ 2 + 48 * A ^ 2 * M + 35 * A ^ 2
    + 4 * A * M ^ 3 + 22 * A * M ^ 2 + 40 * A * M + 25 * A
    + 2 * M ^ 3 + 9 * M ^ 2 + 14 * M + 8

theorem Pcert_pos {A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) : 0 < Pcert A M := by
  have h1 : (0 : ℝ) ≤ A ^ 4 * M := by positivity
  have h2 : (0 : ℝ) ≤ A ^ 4 := by positivity
  have h3 : (0 : ℝ) ≤ A ^ 3 * M ^ 2 := by positivity
  have h4 : (0 : ℝ) ≤ A ^ 3 * M := mul_nonneg (by positivity) hM
  have h5 : (0 : ℝ) ≤ A ^ 3 := by positivity
  have h6 : (0 : ℝ) ≤ A ^ 2 * M ^ 3 := mul_nonneg (by positivity) (by positivity)
  have h7 : (0 : ℝ) ≤ A ^ 2 * M ^ 2 := by positivity
  have h8 : (0 : ℝ) ≤ A ^ 2 * M := mul_nonneg (by positivity) hM
  have h9 : (0 : ℝ) ≤ A ^ 2 := by positivity
  have h10 : (0 : ℝ) ≤ A * M ^ 3 := mul_nonneg hA (by positivity)
  have h11 : (0 : ℝ) ≤ A * M ^ 2 := mul_nonneg hA (by positivity)
  have h12 : (0 : ℝ) ≤ A * M := mul_nonneg hA hM
  have h13 : (0 : ℝ) ≤ M ^ 3 := by positivity
  have h14 : (0 : ℝ) ≤ M ^ 2 := by positivity
  rw [Pcert]
  linarith

/-! ### Rational identities over abstract denominators

Each denominator below is an abstract variable with its defining equation as a
hypothesis, because `field_simp` at this Mathlib revision normalizes a compound
denominator (`2a+2m-3 ↦ 2(a+m)-3`) out of reach of a hypothesis stated in the
paper's shape, and then clears nothing.  With the denominators as variables it
clears them, and the defining equations go back in before `ring`. -/

private theorem alg_lam (S a M u : ℝ) (hu : u ≠ 0) (hdef : u = 2 * a + 2 * M - 3) :
    S + M * (M - 1) / (2 * u) - (a + M / 2 - 1) ^ 2 / (u / 2)
      = S + (3 - 4 * a) / 4 + (1 - 2 * a) / (4 * u) := by
  field_simp
  subst hdef
  ring

private theorem alg_laminf (a g D : ℝ) (hD : D ≠ 0) (hdef : D = 2 * a ^ 2 * g - 1) :
    a * (2 * a - 1) / D + (3 - 4 * a) / 4
      = -(8 * a ^ 3 * g - 6 * a ^ 2 * g - 8 * a ^ 2 + 3) / (4 * D) := by
  field_simp
  subst hdef
  ring

private theorem alg_lam2 (a g D E : ℝ) (hD : D ≠ 0) (hE : E ≠ 0)
    (hDd : D = 2 * a ^ 2 * g - 1) (hEd : E = 2 * a + 1) :
    a * (2 * a - 1) / D + 2 / (2 * E) - a ^ 2 / (E / 2)
      = -(4 * a ^ 4 * g - 2 * a ^ 2 * g - 4 * a ^ 3 - 2 * a ^ 2 + a + 1) / (E * D) := by
  field_simp
  subst hDd
  subst hEd
  ring

private theorem alg_inv_sub (x y c : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (h : y = x + c) :
    x⁻¹ - y⁻¹ = c / (x * y) := by
  field_simp
  subst h
  ring

private theorem alg_key (a g D : ℝ) (hane : a ≠ 0) (hD : D ≠ 0)
    (hdef : D = 2 * a ^ 2 * g - 1) :
    g * (a * (2 * a - 1) / D) + a * (2 * a - 1) / D * (g - (a ^ 2)⁻¹) = (2 * a - 1) / a := by
  field_simp
  subst hdef
  ring

private theorem alg_beta (a M X : ℝ) (hane : a ≠ 0) (hX : X ≠ 0) (hdef : X = a + M - 1) :
    (2 * a - 1) / a - 2 * ((2 * a + M - 2) / (2 * X)) = (a - 1) * (M - 1) / (a * X) := by
  field_simp
  subst hdef
  ring

private theorem alg_Fm (S g a M u V W : ℝ) (hu : u ≠ 0) (hV : V ≠ 0) (hW : W ≠ 0) :
    g * (M * (M - 1) / (2 * u)) - S * ((M - 1) / V) + (a - 1) * (M - 1) / W
      = (M - 1) * (g * M / (2 * u) - S / V + (a - 1) / W) := by
  field_simp

private theorem alg_Dm (a M u X : ℝ) (hane : a ≠ 0) (hu : u ≠ 0) (hX : X ≠ 0) :
    M * (M - 1) / (2 * u) / a ^ 2 + (a - 1) * (M - 1) / (a * X)
      = (M - 1) * (M * X - 2 * a * (1 - a) * u) / (2 * a ^ 2 * u * X) := by
  field

private theorem alg_cm (a M u E : ℝ) (hu : u ≠ 0) (hE : E ≠ 0)
    (hud : u = 2 * a + 2 * M - 3) (hEd : E = 2 * a + 1) :
    M * (M - 1) / (2 * u) - 2 / (2 * E) = (M - 2) * (E * M + 2 * a - 3) / (2 * u * E) := by
  field_simp
  subst hud
  subst hEd
  ring

private theorem alg_bm (a M X Y : ℝ) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hXd : X = a + M - 1) (hYd : Y = a + 1) :
    (2 * a + M - 2) / (2 * X) - a / Y = (M - 2) * (1 - a) / (2 * X * Y) := by
  field_simp
  subst hXd
  subst hYd
  ring

private theorem alg_s1 (a D al bm : ℝ) (hane : a ≠ 0) (hD : D ≠ 0) :
    a * (2 * a - 1) / D * al - 2 * ((2 * a - 1) / (2 * a)) * bm
      = (2 * a - 1) * (a ^ 2 * al - D * bm) / (a * D) := by
  field_simp

private theorem alg_key2 (a t Y : ℝ) (hY : Y ≠ 0) (hYd : Y = a + 1) :
    (2 * a ^ 2 * t + 1) * (a / Y) - a ^ 2 * (t - (Y ^ 2)⁻¹)
      = (a * (2 * a + 1) - a ^ 2 * (1 - a ^ 2) * t) / Y ^ 2 := by
  field_simp
  subst hYd
  ring

private theorem alg_mono (c u v : ℝ) (hu : 0 < u) (hv : 0 < v) (hc : c ≤ 0) (huv : u ≤ v) :
    c / u ≤ c / v := by
  have hu' : u ≠ 0 := hu.ne'
  have hv' : v ≠ 0 := hv.ne'
  have hkey : c / v - c / u = c * (u - v) / (u * v) := by
    field_simp
  have hnn : 0 ≤ c * (u - v) / (u * v) :=
    div_nonneg (by nlinarith) (mul_pos hu hv).le
  linarith

private theorem alg_cert (a M u V W X Y Z : ℝ)
    (hane : a ≠ 0) (hu : u ≠ 0) (hV : V ≠ 0) (hW : W ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hZ : Z ≠ 0)
    (hud : u = 2 * a + 2 * M - 3) (hVd : V = a + 1 / 2) (hWd : W = a + M - 1 / 2)
    (hXd : X = a + M - 1) (hYd : Y = a + M - 3 / 2) (hZd : Z = 2 * a + 2 * M - 2) :
    (a⁻¹ + (1 / 2) * (a ^ 2)⁻¹) * M / (2 * u) - (a - 1 / 2) / (V * W) + (a - 1) / (a * X)
      = Pcert (a - 1 / 2) (M - 2) / (V * (2 * a) ^ 2 * Y * W * Z) := by
  rw [Pcert]
  field_simp
  subst hud
  subst hVd
  subst hWd
  subst hXd
  subst hYd
  subst hZd
  ring


/-! ### The boundary matrices `N̂_m` -/

/-- `N̂_m = N_m^{(1,τ_*)}`, the coefficient matrix on the coefficientwise
boundary. -/
noncomputable def NmatHat (a : ℝ) (m : ℕ) : SymMat := NmatKT a 1 (tauCw a 1) m

@[simp] theorem NmatHat_a11 (a : ℝ) (m : ℕ) : (NmatHat a m).a11 = αcoef a m := rfl
@[simp] theorem NmatHat_a12 (a : ℝ) (m : ℕ) : (NmatHat a m).a12 = βcoef a m := rfl

/-- The `(2,2)` entry is `s_* + c_m`: the boundary value of `τ/g` is `s_*`
(`tauCw_div_trigamma`) and `κ = 1` puts `c_m^{(κ)}` back at `c_m`. -/
theorem NmatHat_a22 (ha : 0 < a) (m : ℕ) : (NmatHat a m).a22 = sStar a + ccoef a m := by
  have h1 : ckappa a 1 m = ccoef a m := by
    have := ckappa_sub_ccoef ha 1 m; linarith
  change tauCw a 1 / trigamma a + ckappa a 1 m = sStar a + ccoef a m
  rw [tauCw_div_trigamma ha, h1]

/-! ### `s_*` and the closed forms of `c_m`, `β_m` -/

theorem sStar_den_pos (ha : 0 < a) : 0 < 2 * a ^ 2 * trigamma a - 1 := by
  have := sq_mul_trigamma_gt_one ha; linarith

theorem sStar_nonneg (ha : 1 / 2 ≤ a) : 0 ≤ sStar a := by
  have ha0 : 0 < a := by linarith
  exact div_nonneg (by nlinarith) (sStar_den_pos ha0).le

theorem sStar_neg (ha : 0 < a) (ha2 : a < 1 / 2) : sStar a < 0 :=
  div_neg_of_neg_of_pos (by nlinarith) (sStar_den_pos ha)

/-- `2a²ψ₁(a) > 2a + 1`, the sharp lower bound cleared of denominators.  This is
the one trigamma input step 2 of `app:boundary-proof` runs on. -/
theorem two_sq_mul_trigamma_gt (ha : 0 < a) : 2 * a + 1 < 2 * a ^ 2 * trigamma a := by
  have hlow := trigamma_gt_inv_sharp ha
  have h : 2 * a ^ 2 * (a⁻¹ + (1 / 2) * (a ^ 2)⁻¹) = 2 * a + 1 := by field_simp
  nlinarith [pow_pos ha 2]

/-- `s_* ≤ a - 1/2` for `a ≥ 1/2`.  Not an extra estimate: `2a²ψ₁(a) - 1 = 2a`
exactly at the sharp lower bound, so this *is* the substitution `ψ₁(a) → g₀`. -/
theorem sStar_le (ha : 1 / 2 ≤ a) : sStar a ≤ a - 1 / 2 := by
  have ha0 : 0 < a := by linarith
  rw [sStar, div_le_iff₀ (sStar_den_pos ha0)]
  nlinarith [two_sq_mul_trigamma_gt ha0]

theorem ccoef_of_two (a : ℝ) (hm : 2 ≤ m) :
    ccoef a m = (m : ℝ) * ((m : ℝ) - 1) / (2 * (2 * a + 2 * (m : ℝ) - 3)) := by
  rw [ccoef, if_neg (by omega : ¬(m ≤ 1))]

theorem βcoef_of_one (a : ℝ) (hm : 1 ≤ m) :
    βcoef a m = (2 * a + (m : ℝ) - 2) / (2 * (a + (m : ℝ) - 1)) := by
  rw [βcoef, if_neg (by omega : ¬(m = 0))]

theorem two_le_cast (hm : 2 ≤ m) : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm

theorem ccoef_pos_of_two (ha : 0 < a) (hm : 2 ≤ m) : 0 < ccoef a m := by
  have hmr := two_le_cast hm
  rw [ccoef_of_two a hm]
  apply div_pos <;> nlinarith

/-! ### Step 1: `N̂_m ≻ 0` for `m ≥ 2` -/

/-- `Λ_m` of `app:boundary-proof`: the Gram slack `ρ̂_m` with `eq:trig-upper-half`
substituted for `ψ₁(a+m-1)`. -/
noncomputable def LamBound (a : ℝ) (m : ℕ) : ℝ :=
  sStar a + ccoef a m - (gramP a m) ^ 2 / (a + (m : ℝ) - 3 / 2)

/-- **`Λ_m` in closed form.**  A single hyperbola in `m`: `eq:Lm-derivative`, the
`m → ∞` limit and the `m = 2` minimum are three readings of this identity. -/
theorem LamBound_eq (ha : 0 < a) (hm : 2 ≤ m) :
    LamBound a m
      = sStar a + (3 - 4 * a) / 4 + (1 - 2 * a) / (4 * (2 * a + 2 * (m : ℝ) - 3)) := by
  have hmr := two_le_cast hm
  have hu : (0 : ℝ) < 2 * a + 2 * (m : ℝ) - 3 := by linarith
  rw [LamBound, ccoef_of_two a hm, gramP,
    show a + (m : ℝ) - 3 / 2 = (2 * a + 2 * (m : ℝ) - 3) / 2 from by ring]
  exact alg_lam (sStar a) a (m : ℝ) (2 * a + 2 * (m : ℝ) - 3) hu.ne' rfl

/-- `Λ_∞ = s_* + (3-4a)/4 > 0` for `0 < a ≤ 1/2`: at `a²ψ₁(a) > a + 1/2` the
numerator `8a³g - 6a²g - 8a² + 3` drops below `-2a`. -/
theorem LamInf_pos (ha : 0 < a) (ha2 : a ≤ 1 / 2) : 0 < sStar a + (3 - 4 * a) / 4 := by
  have hd := sStar_den_pos ha
  have hdne : (2 * a ^ 2 * trigamma a - 1) ≠ 0 := hd.ne'
  have hane : a ≠ 0 := ha.ne'
  have hG : a + 1 / 2 < a ^ 2 * trigamma a := by
    have h := two_sq_mul_trigamma_gt ha; linarith
  have hneg : 8 * a - 6 < 0 := by linarith
  have hprod : (a ^ 2 * trigamma a) * (8 * a - 6) < (a + 1 / 2) * (8 * a - 6) :=
    mul_lt_mul_of_neg_right hG hneg
  rw [sStar, alg_laminf a (trigamma a) _ hd.ne' rfl]
  exact div_pos (by nlinarith [hprod]) (by linarith)

/-- `Λ_2 > 0` for `a ≥ 1/2`, the minimum over `m ≥ 2` on that side.  The
coefficient of `ψ₁(a)` in the numerator is `2a²(2a²-1)`, so the sharp lower bound
settles `2a² ≤ 1` (margin `-a`) and `eq:trig-upper-cubic` settles `2a² ≥ 1`
(margin `-(a²+1)/(3a)`). -/
theorem LamBound_two_pos (ha : 1 / 2 ≤ a) : 0 < LamBound a 2 := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hd := sStar_den_pos ha0
  have h2a1 : (2 * a + 1 : ℝ) ≠ 0 := by positivity
  have hg2 : gramP a 2 = a := by rw [gramP]; norm_num
  have hden2 : a + ((2 : ℕ) : ℝ) - 3 / 2 = (2 * a + 1) / 2 := by push_cast; ring
  have heq : LamBound a 2
      = -(4 * a ^ 4 * trigamma a - 2 * a ^ 2 * trigamma a - 4 * a ^ 3 - 2 * a ^ 2 + a + 1)
        / ((2 * a + 1) * (2 * a ^ 2 * trigamma a - 1)) := by
    rw [LamBound, hg2, hden2, ccoef_two, sStar]
    exact alg_lam2 a (trigamma a) _ (2 * a + 1) hd.ne' h2a1 rfl rfl
  rw [heq]
  refine div_pos ?_ (mul_pos (by linarith) hd)
  by_cases hc : 2 * a ^ 2 ≤ 1
  · -- `2a² ≤ 1`: the sharp lower bound, margin exactly `-a`
    have hle : (2 * a ^ 2 * trigamma a) * (2 * a ^ 2 - 1) ≤ (2 * a + 1) * (2 * a ^ 2 - 1) :=
      mul_le_mul_of_nonpos_right (two_sq_mul_trigamma_gt ha0).le (by linarith)
    nlinarith [hle]
  · -- `2a² ≥ 1`: the cubic upper bound, margin `-(a²+1)/(3a)`
    have hc : (1 : ℝ) < 2 * a ^ 2 := not_le.mp hc
    have hU := trigamma_lt_cubic ha0
    have hU3 : 6 * a ^ 3 * trigamma a < 6 * a ^ 2 + 3 * a + 1 := by
      have h : 6 * a ^ 3 * (1 / a + 1 / (2 * a ^ 2) + 1 / (6 * a ^ 3))
          = 6 * a ^ 2 + 3 * a + 1 := by field_simp; ring
      nlinarith [pow_pos ha0 3]
    have hlt : (6 * a ^ 3 * trigamma a) * (2 * a ^ 2 - 1)
        < (6 * a ^ 2 + 3 * a + 1) * (2 * a ^ 2 - 1) :=
      mul_lt_mul_of_pos_right hU3 (by linarith)
    nlinarith [hlt]

theorem LamBound_pos (ha : 0 < a) (hm : 2 ≤ m) : 0 < LamBound a m := by
  have hmr := two_le_cast hm
  rw [LamBound_eq ha hm]
  by_cases hc : a ≤ 1 / 2
  · have h1 : 0 ≤ (1 - 2 * a) / (4 * (2 * a + 2 * (m : ℝ) - 3)) :=
      div_nonneg (by linarith) (by linarith)
    linarith [LamInf_pos ha hc]
  · have hc : (1 : ℝ) / 2 < a := not_le.mp hc
    have h2 := LamBound_two_pos hc.le
    have he2 : LamBound a 2
        = sStar a + (3 - 4 * a) / 4 + (1 - 2 * a) / (4 * (2 * a + 1)) := by
      rw [LamBound_eq ha (le_refl 2),
        show 2 * a + 2 * ((2 : ℕ) : ℝ) - 3 = 2 * a + 1 from by push_cast; ring]
    rw [he2] at h2
    have hmono := alg_mono (1 - 2 * a) (4 * (2 * a + 1)) (4 * (2 * a + 2 * (m : ℝ) - 3))
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith

/-- **Step 1 of `lem:boundary-positivity`**: `N̂_m ≻ 0` for `m ≥ 2`.  `thm:gram`'s
Cauchy--Schwarz half is independent of the `(2,2)` entry, so it applies at `s_*`
just as at `g⁻¹`; `Λ_m > 0` is what makes `s_* + c_m` clear the slack. -/
theorem NmatHat_pd (ha : 0 < a) (hm : 2 ≤ m) : SymMat.PD (NmatHat a m) := by
  have hmr := two_le_cast hm
  refine ⟨αcoef_pos ha m, ?_⟩
  rw [NmatHat_a11, NmatHat_a12, NmatHat_a22 ha]
  have hcs := βcoef_sq_le_gram ha (show 1 ≤ m by omega)
  have hα := αcoef_pos ha m
  have hgp : 0 < gramP a m := by rw [gramP]; linarith
  have hp : 0 < (gramP a m) ^ 2 := by positivity
  have hub : trigamma (a + (m : ℝ) - 1) < (a + (m : ℝ) - 3 / 2)⁻¹ := by
    have h := trigamma_lt_upper (y := a + (m : ℝ) - 1) (by linarith)
    rwa [show a + (m : ℝ) - 1 - 1 / 2 = a + (m : ℝ) - 3 / 2 from by ring] at h
  have hstep : (gramP a m) ^ 2 * trigamma (a + (m : ℝ) - 1)
      < (gramP a m) ^ 2 / (a + (m : ℝ) - 3 / 2) := by
    rw [div_eq_mul_inv]
    exact mul_lt_mul_of_pos_left hub hp
  have hlam := LamBound_pos ha hm
  rw [LamBound] at hlam
  nlinarith [hcs, mul_lt_mul_of_pos_left hstep hα, mul_pos hα hlam]

/-! ### Step 2: `MD(N̂_0, N̂_m) > 0` for `m ≥ 2` -/

theorem MD_NmatHat_zero_eq (ha : 0 < a) (m : ℕ) :
    SymMat.MD (NmatHat a 0) (NmatHat a m)
      = trigamma a * (sStar a + ccoef a m) + sStar a * αcoef a m - 2 * βcoef a m := by
  simp only [SymMat.MD, NmatHat_a11, NmatHat_a12, NmatHat_a22 ha, αcoef, βcoef_zero,
    ccoef_zero, Nat.cast_zero, add_zero]
  ring

/-- **`eq:Fm-boundary`.**  `F_m = F_m - F_1`, and `F_1 = 0` is the defining relation
for `s_*`, which is why the `ψ₁(a)s_*` and `s_*ψ₁(a+1)` terms cancel and only the
trigamma *difference* survives. -/
theorem MD_NmatHat_zero_diff (ha : 0 < a) (hm : 1 ≤ m) :
    SymMat.MD (NmatHat a 0) (NmatHat a m)
      = trigamma a * ccoef a m
        - sStar a * (trigamma (a + 1) - trigamma (a + (m : ℝ)))
        + (a - 1) * ((m : ℝ) - 1) / (a * (a + (m : ℝ) - 1)) := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hd := sStar_den_pos ha
  have hlin : sStar a * (2 * a ^ 2 * trigamma a - 1) = a * (2 * a - 1) := by
    rw [sStar]; exact div_mul_cancel₀ _ hd.ne'
  have hkey : trigamma a * sStar a + sStar a * trigamma (a + 1) = (2 * a - 1) / a := by
    rw [trigamma_succ' ha, sStar]
    exact alg_key a (trigamma a) _ ha.ne' hd.ne' rfl
  have h1 : (0 : ℝ) < a + (m : ℝ) - 1 := by linarith
  have hβ : (2 * a - 1) / a - 2 * ((2 * a + (m : ℝ) - 2) / (2 * (a + (m : ℝ) - 1)))
      = (a - 1) * ((m : ℝ) - 1) / (a * (a + (m : ℝ) - 1)) :=
    alg_beta a (m : ℝ) (a + (m : ℝ) - 1) ha.ne' h1.ne' rfl
  rw [MD_NmatHat_zero_eq ha m, βcoef_of_one a hm, αcoef]
  linear_combination hkey + hβ

/-- The telescoping estimate of step 2, as a single induction on the inequality:
termwise `x⁻² ≤ (x-1/2)⁻¹ - (x+1/2)⁻¹`, and the right side telescopes. -/
theorem trigamma_diff_le (ha : 0 < a) (k : ℕ) :
    trigamma (a + 1) - trigamma (a + (k : ℝ) + 1)
      ≤ (a + 1 / 2)⁻¹ - (a + (k : ℝ) + 1 / 2)⁻¹ := by
  induction k with
  | zero => norm_num
  | succ j ih =>
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hrec : trigamma (a + (j : ℝ) + 1)
          = ((a + (j : ℝ) + 1)⁻¹) ^ 2 + trigamma (a + (j : ℝ) + 2) := by
        have h := trigamma_succ (y := a + (j : ℝ) + 1) (by linarith)
        rwa [show a + (j : ℝ) + 1 + 1 = a + (j : ℝ) + 2 from by ring] at h
      have hstep : ((a + (j : ℝ) + 1)⁻¹) ^ 2
          ≤ (a + (j : ℝ) + 1 / 2)⁻¹ - (a + (j : ℝ) + 3 / 2)⁻¹ := by
        have h1 : (a + (j : ℝ) + 1 / 2)⁻¹ - (a + (j : ℝ) + 3 / 2)⁻¹
            = 1 / ((a + (j : ℝ) + 1 / 2) * (a + (j : ℝ) + 3 / 2)) :=
          alg_inv_sub _ _ 1 (by linarith : (0:ℝ) < a + (j:ℝ) + 1/2).ne'
            (by linarith : (0:ℝ) < a + (j:ℝ) + 3/2).ne' (by ring)
        have h2 : ((a + (j : ℝ) + 1)⁻¹) ^ 2 = 1 / (a + (j : ℝ) + 1) ^ 2 := by
          rw [inv_pow, one_div]
        rw [h1, h2]
        apply one_div_le_one_div_of_le (by nlinarith)
        nlinarith
      push_cast
      rw [show a + ((j : ℝ) + 1) + 1 = a + (j : ℝ) + 2 from by ring,
        show a + ((j : ℝ) + 1) + 1 / 2 = a + (j : ℝ) + 3 / 2 from by ring]
      linarith [ih, hrec, hstep]

theorem trigamma_diff_le' (ha : 0 < a) (hm : 1 ≤ m) :
    trigamma (a + 1) - trigamma (a + (m : ℝ))
      ≤ (a + 1 / 2)⁻¹ - (a + (m : ℝ) - 1 / 2)⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := trigamma_diff_le ha k
  push_cast
  rwa [show a + ((k : ℝ) + 1) = a + (k : ℝ) + 1 from by ring,
    show a + (k : ℝ) + 1 - 1 / 2 = a + (k : ℝ) + 1 / 2 from by ring]

/-- `B_{a,m}(g)` of `eq:Bm-boundary`. -/
noncomputable def Bbound (a : ℝ) (m : ℕ) : ℝ :=
  trigamma a * (m : ℝ) / (2 * (2 * a + 2 * (m : ℝ) - 3))
    - sStar a / ((a + 1 / 2) * (a + (m : ℝ) - 1 / 2))
    + (a - 1) / (a * (a + (m : ℝ) - 1))

/-- `B` with both substitutions made is `P/den` identically, with every factor of
`den` positive for `a ≥ 1/2`, `m ≥ 2`. -/
private theorem Blow_pos (ha : 1 / 2 ≤ a) (hmr : (2 : ℝ) ≤ (m : ℝ)) :
    0 < (a⁻¹ + (1 / 2) * (a ^ 2)⁻¹) * (m : ℝ) / (2 * (2 * a + 2 * (m : ℝ) - 3))
        - (a - 1 / 2) / ((a + 1 / 2) * (a + (m : ℝ) - 1 / 2))
        + (a - 1) / (a * (a + (m : ℝ) - 1)) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have d1 : (0 : ℝ) < a + 1 / 2 := by linarith
  have d2 : (0 : ℝ) < (2 * a) ^ 2 := by positivity
  have d3 : (0 : ℝ) < a + (m : ℝ) - 3 / 2 := by linarith
  have d4 : (0 : ℝ) < a + (m : ℝ) - 1 / 2 := by linarith
  have d5 : (0 : ℝ) < 2 * a + 2 * (m : ℝ) - 2 := by linarith
  have heq : (a⁻¹ + (1 / 2) * (a ^ 2)⁻¹) * (m : ℝ) / (2 * (2 * a + 2 * (m : ℝ) - 3))
        - (a - 1 / 2) / ((a + 1 / 2) * (a + (m : ℝ) - 1 / 2))
        + (a - 1) / (a * (a + (m : ℝ) - 1))
      = Pcert (a - 1 / 2) ((m : ℝ) - 2)
        / ((a + 1 / 2) * (2 * a) ^ 2 * (a + (m : ℝ) - 3 / 2) * (a + (m : ℝ) - 1 / 2)
            * (2 * a + 2 * (m : ℝ) - 2)) := by
    have e1 : (0 : ℝ) < 2 * a + 2 * (m : ℝ) - 3 := by linarith
    have e2 : (0 : ℝ) < a + (m : ℝ) - 1 := by linarith
    exact alg_cert a (m : ℝ) (2 * a + 2 * (m : ℝ) - 3) (a + 1 / 2) (a + (m : ℝ) - 1 / 2)
      (a + (m : ℝ) - 1) (a + (m : ℝ) - 3 / 2) (2 * a + 2 * (m : ℝ) - 2)
      ha0.ne' e1.ne' d1.ne' d4.ne' e2.ne' d3.ne' d5.ne' rfl rfl rfl rfl rfl rfl
  rw [heq]
  exact div_pos (Pcert_pos (by linarith) (by linarith))
    (mul_pos (mul_pos (mul_pos (mul_pos d1 d2) d3) d4) d5)

theorem Bbound_pos (ha : 1 / 2 ≤ a) (hm : 2 ≤ m) : 0 < Bbound a m := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hmr := two_le_cast hm
  have hD : (0 : ℝ) < 2 * (2 * a + 2 * (m : ℝ) - 3) := by linarith
  have hE : (0 : ℝ) < (a + 1 / 2) * (a + (m : ℝ) - 1 / 2) := by
    apply mul_pos <;> linarith
  have hlow := trigamma_gt_inv_sharp ha0
  have h1 : (a⁻¹ + (1 / 2) * (a ^ 2)⁻¹) * (m : ℝ) / (2 * (2 * a + 2 * (m : ℝ) - 3))
      ≤ trigamma a * (m : ℝ) / (2 * (2 * a + 2 * (m : ℝ) - 3)) := by
    have hnum : (a⁻¹ + (1 / 2) * (a ^ 2)⁻¹) * (m : ℝ) ≤ trigamma a * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hlow.le (by linarith)
    have hq : 0 ≤ (trigamma a * (m : ℝ) - (a⁻¹ + (1 / 2) * (a ^ 2)⁻¹) * (m : ℝ))
        / (2 * (2 * a + 2 * (m : ℝ) - 3)) := div_nonneg (by linarith) hD.le
    rw [sub_div] at hq
    linarith
  have h2 : sStar a / ((a + 1 / 2) * (a + (m : ℝ) - 1 / 2))
      ≤ (a - 1 / 2) / ((a + 1 / 2) * (a + (m : ℝ) - 1 / 2)) := by
    have hq : 0 ≤ ((a - 1 / 2) - sStar a) / ((a + 1 / 2) * (a + (m : ℝ) - 1 / 2)) :=
      div_nonneg (by linarith [sStar_le ha]) hE.le
    rw [sub_div] at hq
    linarith
  rw [Bbound]
  linarith [Blow_pos ha hmr]

/-- **Step 2 of `lem:boundary-positivity`**: `MD(N̂_0, N̂_m) > 0` for `m ≥ 2`.
For `a ≥ 1/2` the telescoping bound reduces it to `(m-1)B_{a,m}(g) > 0`; for
`a < 1/2` the `s_*` term is positive outright and `ψ₁(a) > a⁻²` suffices. -/
theorem MD_NmatHat_zero_pos (ha : 0 < a) (hm : 2 ≤ m) :
    0 < SymMat.MD (NmatHat a 0) (NmatHat a m) := by
  have hmr := two_le_cast hm
  have he2 : (0 : ℝ) < a + (m : ℝ) - 1 := by linarith
  have he3 : (0 : ℝ) < 2 * a + 2 * (m : ℝ) - 3 := by linarith
  rw [MD_NmatHat_zero_diff ha (by omega)]
  by_cases hc : (1 : ℝ) / 2 ≤ a
  · -- `a ≥ 1/2`
    have hs := sStar_nonneg hc
    have hT := trigamma_diff_le' ha (show 1 ≤ m by omega)
    have p1 : (0 : ℝ) < a + 1 / 2 := by linarith
    have p2 : (0 : ℝ) < a + (m : ℝ) - 1 / 2 := by linarith
    have hTeq : (a + 1 / 2)⁻¹ - (a + (m : ℝ) - 1 / 2)⁻¹
        = ((m : ℝ) - 1) / ((a + 1 / 2) * (a + (m : ℝ) - 1 / 2)) :=
      alg_inv_sub _ _ _ p1.ne' p2.ne' (by ring)
    have hid : trigamma a * ccoef a m
          - sStar a * (((m : ℝ) - 1) / ((a + 1 / 2) * (a + (m : ℝ) - 1 / 2)))
          + (a - 1) * ((m : ℝ) - 1) / (a * (a + (m : ℝ) - 1))
        = ((m : ℝ) - 1) * Bbound a m := by
      rw [ccoef_of_two a hm, Bbound]
      exact alg_Fm (sStar a) (trigamma a) a (m : ℝ) (2 * a + 2 * (m : ℝ) - 3)
        ((a + 1 / 2) * (a + (m : ℝ) - 1 / 2)) (a * (a + (m : ℝ) - 1))
        he3.ne' (mul_pos p1 p2).ne' (mul_pos ha he2).ne'
    have hmul : sStar a * (trigamma (a + 1) - trigamma (a + (m : ℝ)))
        ≤ sStar a * ((a + 1 / 2)⁻¹ - (a + (m : ℝ) - 1 / 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hT hs
    rw [hTeq] at hmul
    have hB : 0 < ((m : ℝ) - 1) * Bbound a m :=
      mul_pos (by linarith) (Bbound_pos hc hm)
    linarith [hid, hmul, hB]
  · -- `0 < a < 1/2`
    have hc : a < 1 / 2 := not_le.mp hc
    have hs := sStar_neg ha hc
    have hTpos : 0 < trigamma (a + 1) - trigamma (a + (m : ℝ)) := by
      have h1 : trigamma (a + 1) = ((a + 1)⁻¹) ^ 2 + trigamma (a + 1 + 1) :=
        trigamma_succ (by linarith)
      have h2 : trigamma (a + (m : ℝ)) ≤ trigamma (a + 1 + 1) :=
        trigamma_anti (by linarith) (by linarith)
      have h3 : (0 : ℝ) < ((a + 1)⁻¹) ^ 2 := by positivity
      linarith
    have hgt : 1 < a ^ 2 * trigamma a := sq_mul_trigamma_gt_one ha
    have hc2 := ccoef_pos_of_two ha hm
    have hgc : ccoef a m / a ^ 2 < trigamma a * ccoef a m := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hc2, hgt]
    have hDpos : 0 < (m : ℝ) * (a + (m : ℝ) - 1) - 2 * a * (1 - a) * (2 * a + 2 * (m : ℝ) - 3) := by
      have hfac : ((m : ℝ) * (a + (m : ℝ) - 1) - 2 * a * (1 - a) * (2 * a + 2 * (m : ℝ) - 3))
          - 2 * (2 * a ^ 3 - a ^ 2 + 1)
          = ((m : ℝ) - 2) * ((m : ℝ) + 1 + 4 * a ^ 2 - 3 * a) := by ring
      have h1 : 0 < 2 * (2 * a ^ 3 - a ^ 2 + 1) := by nlinarith
      have h2 : 0 ≤ ((m : ℝ) - 2) * ((m : ℝ) + 1 + 4 * a ^ 2 - 3 * a) :=
        mul_nonneg (by linarith) (by nlinarith [sq_nonneg (2 * a - 1)])
      linarith
    have hid2 : ccoef a m / a ^ 2 + (a - 1) * ((m : ℝ) - 1) / (a * (a + (m : ℝ) - 1))
        = ((m : ℝ) - 1) * ((m : ℝ) * (a + (m : ℝ) - 1)
              - 2 * a * (1 - a) * (2 * a + 2 * (m : ℝ) - 3))
          / (2 * a ^ 2 * (2 * a + 2 * (m : ℝ) - 3) * (a + (m : ℝ) - 1)) := by
      rw [ccoef_of_two a hm]
      exact alg_Dm a (m : ℝ) (2 * a + 2 * (m : ℝ) - 3) (a + (m : ℝ) - 1)
        ha.ne' he3.ne' he2.ne'
    have hpos2 : 0 < ((m : ℝ) - 1) * ((m : ℝ) * (a + (m : ℝ) - 1)
            - 2 * a * (1 - a) * (2 * a + 2 * (m : ℝ) - 3))
        / (2 * a ^ 2 * (2 * a + 2 * (m : ℝ) - 3) * (a + (m : ℝ) - 1)) :=
      div_pos (mul_pos (by linarith) hDpos) (by positivity)
    have hneg : 0 < -(sStar a * (trigamma (a + 1) - trigamma (a + (m : ℝ)))) := by
      have := mul_neg_of_neg_of_pos hs hTpos
      linarith
    linarith [hid2, hpos2, hgc, hneg]

/-! ### Step 3: `MD(N̂_1, N̂_m) > 0` for `m ≥ 2` -/

theorem ccoef_two_le (ha : 0 < a) (hm : 2 ≤ m) : ccoef a 2 ≤ ccoef a m := by
  have hmr := two_le_cast hm
  rcases eq_or_lt_of_le hm with h | h
  · rw [← h]
  · have hmr3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    have hu : (0 : ℝ) < 2 * a + 2 * (m : ℝ) - 3 := by linarith
    have hid : ccoef a m - ccoef a 2
        = ((m : ℝ) - 2) * ((2 * a + 1) * (m : ℝ) + 2 * a - 3)
          / (2 * (2 * a + 2 * (m : ℝ) - 3) * (2 * a + 1)) := by
      rw [ccoef_of_two a hm, ccoef_two]
      exact alg_cm a (m : ℝ) (2 * a + 2 * (m : ℝ) - 3) (2 * a + 1) hu.ne'
        (by positivity) rfl rfl
    have hnum : 0 ≤ ((m : ℝ) - 2) * ((2 * a + 1) * (m : ℝ) + 2 * a - 3) :=
      mul_nonneg (by linarith) (by nlinarith)
    have : 0 ≤ ccoef a m - ccoef a 2 := by
      rw [hid]; exact div_nonneg hnum (by positivity)
    linarith

theorem sStar_add_ccoef_pos (ha : 0 < a) (hm : 2 ≤ m) : 0 < sStar a + ccoef a m := by
  linarith [sStar_add_c_two_pos ha, ccoef_two_le ha hm]

theorem βcoef_two_le (ha : 0 < a) (ha1 : a ≤ 1) (hm : 2 ≤ m) : βcoef a 2 ≤ βcoef a m := by
  have hmr := two_le_cast hm
  have he : (0 : ℝ) < a + (m : ℝ) - 1 := by linarith
  have hid : βcoef a m - βcoef a 2
      = ((m : ℝ) - 2) * (1 - a) / (2 * (a + (m : ℝ) - 1) * (a + 1)) := by
    rw [βcoef_of_one a (by omega), βcoef_two]
    exact alg_bm a (m : ℝ) (a + (m : ℝ) - 1) (a + 1) he.ne'
      (by linarith : (0:ℝ) < a + 1).ne' rfl rfl
  have : 0 ≤ βcoef a m - βcoef a 2 := by
    rw [hid]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

theorem NmatHat_one_psd (ha : 1 / 2 ≤ a) : SymMat.PSD (NmatHat a 1) := by
  have ha0 : (0 : ℝ) < a := by linarith
  refine ⟨(αcoef_pos ha0 1).le, ?_, ?_⟩
  · rw [NmatHat_a22 ha0, ccoef_one]
    linarith [sStar_nonneg ha]
  · have h := det_N1_boundary_nonneg ha
    change (NmatKT a 1 (tauCw a 1) 1).a12 ^ 2
        ≤ (NmatKT a 1 (tauCw a 1) 1).a11 * (NmatKT a 1 (tauCw a 1) 1).a22
    linarith [h]

theorem NmatHat_ne_zero (ha : 0 < a) (m : ℕ) : NmatHat a m ≠ 0 := by
  intro h
  have hp := αcoef_pos ha m
  rw [show αcoef a m = (NmatHat a m).a11 from rfl, h] at hp
  simp at hp

/-- **Step 3 of `lem:boundary-positivity`**: `MD(N̂_1, N̂_m) > 0` for `m ≥ 2`.
For `a ≥ 1/2` this is `lem:MD-positive` over `det N̂_1 ≥ 0` and step 1; for
`a < 1/2` the sign pattern `s_* < 0 < s_* + c_m`, `β_1 < 0 < β_m` puts everything
on the inequality `β_m(2a²g-1) > a²α_m`, which reduces to `m = 2`. -/
theorem MD_NmatHat_one_pos (ha : 0 < a) (hm : 2 ≤ m) :
    0 < SymMat.MD (NmatHat a 1) (NmatHat a m) := by
  by_cases hc : (1 : ℝ) / 2 ≤ a
  · exact SymMat.MD_pos_of_psd_pd (NmatHat_one_psd hc) (NmatHat_ne_zero ha 1)
      (NmatHat_pd ha hm)
  · have hc : a < 1 / 2 := not_le.mp hc
    have hmr := two_le_cast hm
    have hd := sStar_den_pos ha
    have hMD : SymMat.MD (NmatHat a 1) (NmatHat a m)
        = αcoef a 1 * (sStar a + ccoef a m)
          + (sStar a * αcoef a m - 2 * βcoef a 1 * βcoef a m) := by
      simp only [SymMat.MD, NmatHat_a11, NmatHat_a12, NmatHat_a22 ha, ccoef_one, add_zero]
      ring
    -- the `m = 2` reduction of `β_m(2a²g-1) > a²α_m`
    have h2a : (0 : ℝ) < 2 * a + 1 := by linarith
    have ht : trigamma (a + 1) * (2 * a + 1) < 2 := by
      have h := trigamma_lt_upper (y := a + 1) (by linarith)
      rw [show a + 1 - 1 / 2 = (2 * a + 1) / 2 from by ring, inv_div] at h
      calc trigamma (a + 1) * (2 * a + 1) < 2 / (2 * a + 1) * (2 * a + 1) :=
            mul_lt_mul_of_pos_right h h2a
        _ = 2 := div_mul_cancel₀ _ h2a.ne'
    have hα2 : αcoef a 2 = trigamma (a + 1) - ((a + 1) ^ 2)⁻¹ := by
      have h := trigamma_succ' (a := a + 1) (by linarith)
      rw [αcoef]
      push_cast
      rwa [show a + 2 = a + 1 + 1 from by ring]
    have hDT : 2 * a ^ 2 * trigamma a - 1 = 2 * a ^ 2 * trigamma (a + 1) + 1 := by
      have h := trigamma_succ' ha
      have h2 : trigamma a = trigamma (a + 1) + (a ^ 2)⁻¹ := by linarith
      have hane : a ≠ 0 := ha.ne'
      rw [h2]
      field
    have hkey2 : a ^ 2 * αcoef a 2 < (2 * a ^ 2 * trigamma a - 1) * βcoef a 2 := by
      rw [hα2, hDT, βcoef_two]
      have hid : (2 * a ^ 2 * trigamma (a + 1) + 1) * (a / (a + 1))
            - a ^ 2 * (trigamma (a + 1) - ((a + 1) ^ 2)⁻¹)
          = (a * (2 * a + 1) - a ^ 2 * (1 - a ^ 2) * trigamma (a + 1)) / (a + 1) ^ 2 :=
        alg_key2 a (trigamma (a + 1)) (a + 1) (by linarith : (0:ℝ) < a + 1).ne' rfl
      have hfac : 0 < a ^ 2 * (1 - a ^ 2) := by
        have h1 : (0 : ℝ) < a ^ 2 := pow_pos ha 2
        have h2 : a ^ 2 < 1 := by nlinarith
        nlinarith
      have hstep : 0 < (a * (2 * a + 1) - a ^ 2 * (1 - a ^ 2) * trigamma (a + 1))
          * (2 * a + 1) := by
        have h1 : a ^ 2 * (1 - a ^ 2) * (trigamma (a + 1) * (2 * a + 1))
            < a ^ 2 * (1 - a ^ 2) * 2 := mul_lt_mul_of_pos_left ht hfac
        nlinarith [h1]
      have hnum : 0 < a * (2 * a + 1) - a ^ 2 * (1 - a ^ 2) * trigamma (a + 1) := by
        rcases mul_pos_iff.mp hstep with ⟨h, _⟩ | ⟨_, h⟩
        · exact h
        · linarith
      have hpos : 0 < (a * (2 * a + 1) - a ^ 2 * (1 - a ^ 2) * trigamma (a + 1)) / ((a + 1) ^ 2) :=
        div_pos hnum (by positivity)
      linarith [hid, hpos]
    have hβm := βcoef_two_le ha (by linarith) hm
    have hαm : αcoef a m ≤ αcoef a 2 := by
      rw [αcoef, αcoef]
      exact trigamma_anti (by push_cast; linarith) (by push_cast; linarith)
    have hkey : a ^ 2 * αcoef a m < (2 * a ^ 2 * trigamma a - 1) * βcoef a m := by
      have h1 : a ^ 2 * αcoef a m ≤ a ^ 2 * αcoef a 2 :=
        mul_le_mul_of_nonneg_left hαm (by positivity)
      have h2 : (2 * a ^ 2 * trigamma a - 1) * βcoef a 2
          ≤ (2 * a ^ 2 * trigamma a - 1) * βcoef a m := mul_le_mul_of_nonneg_left hβm hd.le
      linarith
    have hid : sStar a * αcoef a m - 2 * βcoef a 1 * βcoef a m
        = (2 * a - 1) * (a ^ 2 * αcoef a m - (2 * a ^ 2 * trigamma a - 1) * βcoef a m)
          / (a * (2 * a ^ 2 * trigamma a - 1)) := by
      rw [sStar, βcoef_one]
      exact alg_s1 a (2 * a ^ 2 * trigamma a - 1) (αcoef a m) (βcoef a m) ha.ne' hd.ne'
    have h2pos : 0 < sStar a * αcoef a m - 2 * βcoef a 1 * βcoef a m := by
      rw [hid]
      exact div_pos (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by positivity)
    have h1pos : 0 < αcoef a 1 * (sStar a + ccoef a m) :=
      mul_pos (αcoef_pos ha 1) (sStar_add_ccoef_pos ha hm)
    rw [hMD]
    linarith

/-! ### Step 4: the degree-two coefficient -/

/-- **`eq:boundary-delta2`** in the reduced normalization: `Δ̂_2` is a positive
multiple of `P_2(a,ψ₁(a+1))`.  The `Γ(a)⁴` of the printed form is absorbed by
`Dcoeff`'s normalization, and `g = ψ₁(a+1) + a⁻²` cancels the `(a²t+1)` factor. -/
theorem DcoeffKT_boundary_two_eq (ha : 0 < a) :
    DcoeffKT a 1 (tauCw a 1) 2
      = 2 * P2boundary a (trigamma (a + 1))
        / (a ^ 3 * (a + 1) ^ 3 * (2 * a ^ 2 * trigamma (a + 1) + 1)) := by
  have hd := sStar_den_pos ha
  have hp : (0 : ℝ) < a + 1 := by linarith
  have hDT : 2 * a ^ 2 * trigamma a - 1 = 2 * a ^ 2 * trigamma (a + 1) + 1 := by
    have h : trigamma a = trigamma (a + 1) + (a ^ 2)⁻¹ := by
      linarith [trigamma_succ' ha]
    have hane : a ≠ 0 := ha.ne'
    rw [h]; field_simp; ring
  have hga : trigamma a = trigamma (a + 1) + (a ^ 2)⁻¹ := by linarith [trigamma_succ' ha]
  have hα2 : αcoef a 2 = trigamma (a + 1) - ((a + 1) ^ 2)⁻¹ := by
    have h := trigamma_succ' (a := a + 1) (by linarith)
    rw [αcoef]; push_cast; rwa [show a + 2 = a + 1 + 1 from by ring]
  have hα1 : αcoef a 1 = trigamma (a + 1) := by rw [αcoef]; push_cast; ring_nf
  have hα0 : αcoef a 0 = trigamma a := by rw [αcoef]; push_cast; ring_nf
  have hsS : sStar a = a * (2 * a - 1) / (2 * a ^ 2 * trigamma (a + 1) + 1) := by
    rw [sStar, hDT]
  have hden : (0 : ℝ) < 2 * a ^ 2 * trigamma (a + 1) + 1 := by
    have := trigamma_pos (show (0:ℝ) < a + 1 by linarith); positivity
  simp only [DcoeffKT, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    SymMat.MD, NmatKT_a11, NmatKT_a12]
  rw [show (NmatKT a 1 (tauCw a 1) 0).a22 = sStar a + ccoef a 0 from NmatHat_a22 ha 0,
    show (NmatKT a 1 (tauCw a 1) 1).a22 = sStar a + ccoef a 1 from NmatHat_a22 ha 1,
    show (NmatKT a 1 (tauCw a 1) 2).a22 = sStar a + ccoef a 2 from NmatHat_a22 ha 2]
  rw [ccoef_zero, ccoef_one, ccoef_two, βcoef_zero, βcoef_one, βcoef_two,
    hα0, hα1, hα2, hga, hsS, sred_zero, sred_one, sred_two, P2boundary]
  norm_num
  field

theorem DcoeffKT_boundary_two_pos (ha : 0 < a) : 0 < DcoeffKT a 1 (tauCw a 1) 2 := by
  have hden : (0 : ℝ) < 2 * a ^ 2 * trigamma (a + 1) + 1 := by
    have := trigamma_pos (show (0:ℝ) < a + 1 by linarith); positivity
  rw [DcoeffKT_boundary_two_eq ha]
  exact div_pos (by linarith [P2boundary_pos ha])
    (by have : (0:ℝ) < a + 1 := by linarith
        positivity)

/-! ### `lem:boundary-positivity` -/

/-- Every mixed pair contributing to a coefficient of degree `≥ 3` is positive:
`min(k,l) = 0` is step 2, `min(k,l) = 1` is step 3, and `min(k,l) ≥ 2` is step 1
through `lem:MD-positive`. -/
theorem MD_NmatHat_pos (ha : 0 < a) {k l : ℕ} (hkl : 3 ≤ k + l) :
    0 < SymMat.MD (NmatHat a k) (NmatHat a l) := by
  match k, l with
  | 0, l => exact MD_NmatHat_zero_pos ha (by omega)
  | 1, l => exact MD_NmatHat_one_pos ha (by omega)
  | (j + 2), 0 =>
      rw [SymMat.MD_comm]; exact MD_NmatHat_zero_pos ha (by omega)
  | (j + 2), 1 =>
      rw [SymMat.MD_comm]; exact MD_NmatHat_one_pos ha (by omega)
  | (j + 2), (i + 2) =>
      exact SymMat.MD_pos_of_psd_pd (NmatHat_pd ha (by omega)).psd
        (NmatHat_ne_zero ha _) (NmatHat_pd ha (by omega))

/-- **`lem:boundary-positivity`, positive degrees.** -/
theorem DcoeffKT_boundary_pos (ha : 0 < a) (hn : 2 ≤ n) :
    0 < DcoeffKT a 1 (tauCw a 1) n := by
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h]; exact DcoeffKT_boundary_two_pos ha
  · rw [DcoeffKT]
    refine Finset.sum_pos (fun k hk => ?_) ⟨0, Finset.mem_range.mpr (by omega)⟩
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact mul_pos (mul_pos (sred_pos ha k) (sred_pos ha (n - k)))
      (MD_NmatHat_pos ha (show 3 ≤ k + (n - k) by omega))

/-- **`lem:boundary-positivity`.**  On the coefficientwise boundary the degree-one
coefficient vanishes and every higher coefficient is strictly positive. -/
theorem boundary_positivity (ha : 0 < a) :
    DcoeffKT a 1 (tauCw a 1) 1 = 0 ∧ ∀ n : ℕ, 2 ≤ n → 0 < DcoeffKT a 1 (tauCw a 1) n :=
  ⟨DcoeffKT_degree_one_boundary ha 1, fun _ hn => DcoeffKT_boundary_pos ha hn⟩

end TuranBessel
