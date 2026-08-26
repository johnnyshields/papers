/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.BesselDict
import TuranBessel.BetaGammaCoeff
import TuranBessel.TuranDet
import TuranBessel.Main

/-!
# The Bessel dictionary: `P_ν`, `H_ν`, and `eq:D-Delta`

`shields-2026-turan-bessel.tex`, «Classical scalar Bessel directions»
(`sec:scalar`, `eq:U-L`, `eq:G-L`, `eq:ABC-log`, `eq:D-Delta`) and `sec:main`
(`eq:Pnu`, `eq:Hnu-kappa`).

`BesselDict` handles the pure `ν`-side: the affine term of
`log I_ν(x) = ν log(x/2) + log Z(ν+1,(x/2)²)` dies under `∂_ν²`, so
`G_ν = -L_{aa}` needs only the `a`-calculus of `ParameterCalculus`.  The
remaining two functionals both differentiate in `x`, and `Θ_x = x∂_x` acting on a
function of `λ = (x/2)²` is `2Θ_λ`.  This file runs that side:

    Θ_x log I_ν  = ν + 2 Z_Θ/Z                                (`eq:U-L`, first)
    P_ν          = ∂_ν(Θ_x log I_ν) = 2B/Z² - 1               (`eq:Pnu`, `eq:U-L`)
    H_ν          = 4Z_Θ/Z - 4(ZZ_{ΘΘ} - Z_Θ²)/Z² = 4C/(gZ²) - 4/g
                                                              (`eq:Hnu-kappa`, `eq:G-L`)
    G_ν(H_ν + 4/g) - (1+P_ν)² = 4Δ/(gZ⁴)                      (`eq:D-Delta`)

and closes with `turanDet_pos`, the pointwise positivity of `Δ` on `λ > 0` read
off `TuranDet.hasSum_turanDet` and `Main.coefficientwise_positivity`.

Two derivative facts are carried here and nowhere else in the tree.
`hasDerivAt_Zfun_lam` and
`hasDerivAt_ZEulerSeries_lam` restate `BetaGammaCoeff.hasDerivAt_weightedZ` with
the Euler series in place of the raw termwise `tsum`, which is legitimate only
for `λ ≠ 0` — hence `x > 0` throughout.  `hasDerivAt_ZEulerSeries_param` is the
mixed input `∂_a Z_Θ = Z_{aΘ}`: the same differentiation under the summation sign
that `ParameterCalculus.hasDerivAt_Zfun_param` performs for the constant weight,
run for the weight `k`, where the extra index factor costs one more geometric
factor in the dominating series.

Every `_eq` below states its functional as a derivative of `log I_ν`, so the
definitions name the paper's objects rather than standing in for them.

Sorry-free.
-/

open Filter Topology Set

namespace TuranBessel

variable {a lam ν x : ℝ}

/-! ### The `λ`-derivative of `Z` and of `Z_Θ`, in Euler form -/

private theorem bnd_one (k : ℕ) : |(1 : ℝ)| ≤ 1 * ((k : ℝ) + 1) ^ 2 := by
  have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  simpa using this

private theorem bnd_idx (k : ℕ) : |(k : ℝ)| ≤ 1 * ((k : ℝ) + 1) ^ 1 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [abs_of_nonneg hk]; nlinarith

/-- `∂_λ Z = Z_Θ/λ` for `λ ≠ 0`: the Euler series divided by `λ` is the honest
`λ`-derivative of `Z`. -/
theorem hasDerivAt_Zfun_lam (ha : 0 < a) (hlam : lam ≠ 0) :
    HasDerivAt (fun y : ℝ => Zfun a y) (ZEulerSeries a lam / lam) lam := by
  have h := hasDerivAt_weightedZ (a := a) ha (c := fun _ => (1 : ℝ)) (C := 1) 2
    (fun k => bnd_one k) lam
  have hfun : (fun y : ℝ => ∑' k : ℕ, (1 : ℝ) * zterm a y k) = fun y : ℝ => Zfun a y := by
    funext y; exact (Zfun_eq_weighted a y).symm
  rw [hfun] at h
  refine h.congr_deriv ?_
  have hkey : lam * (∑' k : ℕ, (1 : ℝ) * ((k : ℝ) * lam ^ (k - 1)
      / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ))))) = ZEulerSeries a lam := by
    rw [lam_mul_tsum_deriv a (fun _ => (1 : ℝ)) lam, ZEulerSeries]
    exact tsum_congr fun k => by ring
  rw [eq_div_iff hlam, mul_comm]
  exact hkey

/-- `∂_λ Z_Θ = Z_{ΘΘ}/λ` for `λ ≠ 0`. -/
theorem hasDerivAt_ZEulerSeries_lam (ha : 0 < a) (hlam : lam ≠ 0) :
    HasDerivAt (fun y : ℝ => ZEulerSeries a y) (ZEuler2Series a lam / lam) lam := by
  have h := hasDerivAt_weightedZ (a := a) ha (c := fun k : ℕ => (k : ℝ)) (C := 1) 1
    (fun k => bnd_idx k) lam
  have hfun : (fun y : ℝ => ∑' k : ℕ, (k : ℝ) * zterm a y k)
      = fun y : ℝ => ZEulerSeries a y := rfl
  rw [hfun] at h
  refine h.congr_deriv ?_
  have hkey : lam * (∑' k : ℕ, (k : ℝ) * ((k : ℝ) * lam ^ (k - 1)
      / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ))))) = ZEuler2Series a lam := by
    rw [lam_mul_tsum_deriv a (fun k : ℕ => (k : ℝ)) lam, ZEuler2Series]
    exact tsum_congr fun k => by ring
  rw [eq_div_iff hlam, mul_comm]
  exact hkey

/-! ### The mixed derivative `∂_a Z_Θ = Z_{aΘ}` -/

/-- `1/Γ` is bounded on a compact subinterval of `(0,∞)`. -/
private theorem exists_inv_Gamma_bd {a₀ a₁ : ℝ} (h₀ : 0 < a₀) (h : a₀ ≤ a₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ y ∈ Icc a₀ a₁, (Real.Gamma y)⁻¹ ≤ K := by
  have hsub : Icc a₀ a₁ ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le h₀ hy.1
  have hcont : ContinuousOn (fun y : ℝ => (Real.Gamma y)⁻¹) (Icc a₀ a₁) :=
    (Real.differentiableOn_Gamma_Ioi.continuousOn.mono hsub).inv₀
      (fun y hy => (Real.Gamma_pos_of_pos (hsub hy)).ne')
  obtain ⟨y₀, hy₀, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a₀, left_mem_Icc.2 h⟩ hcont
  exact ⟨(Real.Gamma y₀)⁻¹, inv_pos.2 (Real.Gamma_pos_of_pos (hsub hy₀)),
    fun y hy => isMaxOn_iff.1 hmax y hy⟩

/-- A summable majorant for the termwise `a`-derivative of `Z_Θ`, uniform on
`(a/2, a+1)`.  The index weight costs one more factor `2^k` over the constant-weight
bound of `ParameterCalculus`, so the geometric ratio is `4|λ|` instead of `2|λ|`. -/
private theorem exists_idx_dzterm_bd (ha : 0 < a) (lam : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ (k : ℕ) (y : ℝ), y ∈ Ioo (a / 2) (a + 1) →
      ‖(k : ℝ) * (-realDigamma (y + (k : ℝ)) * zterm y lam k)‖ ≤ u k := by
  have h₀ : 0 < a / 2 := by linarith
  have hle : a / 2 ≤ a + 1 := by linarith
  obtain ⟨K, hK, hKle⟩ := exists_inv_Gamma_bd h₀ hle
  set C : ℝ := |realDigamma (a / 2)| + |realDigamma (a + 1)| with hC
  have hC0 : 0 ≤ C := by positivity
  have hmin0 : 0 < min (a / 2) 1 := lt_min h₀ one_pos
  set D : ℝ := K / min (a / 2) 1 with hD
  have hD0 : 0 < D := div_pos hK hmin0
  refine ⟨fun k => (C + 1 / (a / 2)) * D * ((4 * |lam|) ^ k / (Nat.factorial k : ℝ)),
    (Real.summable_pow_div_factorial (4 * |lam|)).mul_left _, fun k y hy => ?_⟩
  obtain ⟨hy0, hy1⟩ := hy
  have hypos : 0 < y := lt_trans h₀ hy0
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hyk : 0 < y + (k : ℝ) := by linarith
  have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hGk : 0 < Real.Gamma (y + (k : ℝ)) := Real.Gamma_pos_of_pos hyk
  have hpsi : |realDigamma (y + (k : ℝ))| ≤ C + (k : ℝ) / (a / 2) :=
    abs_realDigamma_add_nat_le h₀ ⟨hy0.le, hy1.le⟩ k
  have hlow : Real.Gamma y * min (a / 2) 1 ≤ Real.Gamma (y + (k : ℝ)) := by
    calc Real.Gamma y * min (a / 2) 1 ≤ Real.Gamma y * min y 1 :=
          mul_le_mul_of_nonneg_left (min_le_min hy0.le le_rfl)
            (Real.Gamma_pos_of_pos hypos).le
      _ ≤ Real.Gamma (y + (k : ℝ)) := Gamma_mul_min_le_Gamma_add hypos k
  have hinvG : (Real.Gamma (y + (k : ℝ)))⁻¹ ≤ D := by
    have h1 : (Real.Gamma (y + (k : ℝ)))⁻¹ ≤ (Real.Gamma y * min (a / 2) 1)⁻¹ :=
      inv_anti₀ (by positivity) hlow
    rw [mul_inv] at h1
    refine h1.trans ?_
    rw [hD, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hKle y ⟨hy0.le, hy1.le⟩) (by positivity)
  have hzabs : ‖zterm y lam k‖ ≤ D * (|lam| ^ k / (Nat.factorial k : ℝ)) := by
    have hzn : ‖zterm y lam k‖
        = (|lam| ^ k / (Nat.factorial k : ℝ)) * (Real.Gamma (y + (k : ℝ)))⁻¹ := by
      rw [zterm, Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (mul_pos hfk hGk)]
      field_simp
    rw [hzn, mul_comm]
    exact mul_le_mul_of_nonneg_right hinvG (by positivity)
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hk2 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have hfac : |realDigamma (y + (k : ℝ))| ≤ (C + 1 / (a / 2)) * 2 ^ k := by
    have hkk : (k : ℝ) / (a / 2) ≤ 1 / (a / 2) * 2 ^ k := by
      rw [div_eq_mul_inv, one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hk2 (by positivity)
    have hC2 : C ≤ C * 2 ^ k := le_mul_of_one_le_right hC0 h2k
    have hdist : (C + 1 / (a / 2)) * 2 ^ k = C * 2 ^ k + 1 / (a / 2) * 2 ^ k := by ring
    linarith
  have h4 : ((4 : ℝ) * |lam|) ^ k = 2 ^ k * (2 ^ k * |lam| ^ k) := by
    rw [show (4 : ℝ) * |lam| = 2 * (2 * |lam|) by ring, mul_pow, mul_pow]
  calc ‖(k : ℝ) * (-realDigamma (y + (k : ℝ)) * zterm y lam k)‖
      = (k : ℝ) * (|realDigamma (y + (k : ℝ))| * ‖zterm y lam k‖) := by
        rw [norm_mul, norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hk]
    _ ≤ 2 ^ k * ((C + 1 / (a / 2)) * 2 ^ k * (D * (|lam| ^ k / (Nat.factorial k : ℝ)))) := by
        refine mul_le_mul hk2 (mul_le_mul hfac hzabs (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = (C + 1 / (a / 2)) * D * ((4 * |lam|) ^ k / (Nat.factorial k : ℝ)) := by
        rw [h4]; ring

/-- **`Z_{aΘ} = ∂_a Z_Θ`.**  The `a`-derivative of the Euler series may be taken
under the summation sign, exactly as `ParameterCalculus.hasDerivAt_Zfun_param` does
for `Z` itself.  This is the mixed input `∂_aΘ_λ` that `eq:Bdef` and `eq:Pnu`
consume. -/
theorem hasDerivAt_ZEulerSeries_param (ha : 0 < a) (lam : ℝ) :
    HasDerivAt (fun y : ℝ => ZEulerSeries y lam) (ZParamEulerSeries a lam) a := by
  have h₀ : 0 < a / 2 := by linarith
  have hmem : a ∈ Ioo (a / 2) (a + 1) := ⟨by linarith, by linarith⟩
  obtain ⟨u, hu, hbound⟩ := exists_idx_dzterm_bd ha lam
  have hsummable : Summable (fun k : ℕ => (k : ℝ) * zterm a lam k) :=
    (summable_norm_idx_zterm ha lam).of_norm
  have h := hasDerivAt_tsum_of_isPreconnected (u := u)
    (g := fun k y => (k : ℝ) * zterm y lam k)
    (g' := fun k y => (k : ℝ) * (-realDigamma (y + (k : ℝ)) * zterm y lam k))
    (t := Ioo (a / 2) (a + 1)) (y₀ := a) (y := a) hu isOpen_Ioo
    (convex_Ioo _ _).isPreconnected
    (fun k y hy => (hasDerivAt_zterm (lt_trans h₀ hy.1) lam k).const_mul (k : ℝ))
    hbound hmem hsummable hmem
  have hfun : (fun y : ℝ => ZEulerSeries y lam)
      = fun y : ℝ => ∑' k : ℕ, (k : ℝ) * zterm y lam k := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  rw [ZParamEulerSeries]
  exact tsum_congr fun k => by ring

/-! ### The field algebra of `eq:U-L`, `eq:G-L` and `eq:D-Delta`

Stated over abstract reals, because the identities are pure algebra in the five
atoms `Z, Z_Θ, Z_{ΘΘ}, Z_a, Z_{aΘ}` and `g`, and `field_simp` needs the
nonvanishing hypotheses to be about atoms rather than about `Zfun (ν+1) ((x/2)²)`
in whatever normal form it has just rewritten the goal into. -/

private theorem algebra_P (Z E ZP ZPE : ℝ) (hZ : Z ≠ 0) :
    1 + 2 * ((ZPE * Z - E * ZP) / Z ^ 2)
      = 2 * (Z * Z + Z * ZPE - ZP * E) / Z ^ 2 - 1 := by
  field

private theorem algebra_theta2 (x Z E E2 : ℝ) (hx : x ≠ 0) (hZ : Z ≠ 0) :
    x * (2 * ((E2 / (x / 2) ^ 2 * Z - E * (E / (x / 2) ^ 2)) / Z ^ 2 * (x / 2)))
      = 4 * (Z * E2 - E ^ 2) / Z ^ 2 := by
  field

private theorem algebra_H (ν g Z E E2 : ℝ) (hg : g ≠ 0) (hZ : Z ≠ 0) :
    4 * (1 * (Z * Z) + g * (1 * (Z * E) - Z * E2 + E * E)) / (g * Z ^ 2) - 4 / g
      = 2 * (ν + 2 * (E / Z) - ν) - 4 * (Z * E2 - E ^ 2) / Z ^ 2 := by
  field

private theorem algebra_D (A B C Z g : ℝ) (hg : g ≠ 0) (hZ : Z ≠ 0) :
    A / Z ^ 2 * (4 * C / (g * Z ^ 2) - 4 / g + 4 / g) - (1 + (2 * B / Z ^ 2 - 1)) ^ 2
      = 4 * (A * C - g * B ^ 2) / (g * Z ^ 4) := by
  field

/-! ### `Θ_x log I_ν` (`eq:U-L`, first identity) -/

/-- `Θ_x log I_ν = ν + 2Z_Θ/Z` at `a = ν+1`, `λ = (x/2)²`.  The `ν` here is the
affine term of the split surviving `Θ_x`, and the `2` is `Θ_x = 2Θ_λ`. -/
noncomputable def besselUfun (ν x : ℝ) : ℝ :=
  ν + 2 * (ZEulerSeries (ν + 1) ((x / 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2))

private theorem hasDerivAt_half_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y / 2) ^ 2) (x / 2) x := by
  have hfun : (fun y : ℝ => (y / 2) ^ 2) = fun y : ℝ => y ^ 2 / 4 := by
    funext y; ring
  rw [hfun]
  refine ((hasDerivAt_pow 2 x).div_const 4).congr_deriv ?_
  norm_num
  ring

/-- `∂_x log I_ν(x) = (ν + 2Z_Θ/Z)/x`; multiplying by `x` is `eq:U-L`. -/
theorem hasDerivAt_log_besselIReal_arg (hν : -1 < ν) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (besselIReal ν y)) (besselUfun ν x / x) x := by
  have ha : 0 < ν + 1 := by linarith
  have hlam : 0 < (x / 2) ^ 2 := by positivity
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha hlam.le
  have hxne : x ≠ 0 := hx.ne'
  have hZne : Zfun (ν + 1) ((x / 2) ^ 2) ≠ 0 := hZ.ne'
  have hlogZ : HasDerivAt (fun y : ℝ => Real.log (Zfun (ν + 1) y))
      (ZEulerSeries (ν + 1) ((x / 2) ^ 2) / (x / 2) ^ 2
        / Zfun (ν + 1) ((x / 2) ^ 2)) ((x / 2) ^ 2) :=
    (hasDerivAt_Zfun_lam ha hlam.ne').log hZne
  have hcomp := hlogZ.comp x (hasDerivAt_half_sq x)
  have hlogh : HasDerivAt (fun y : ℝ => Real.log (y / 2)) (1 / x) x := by
    have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2 : ℝ) x := by
      simpa using (hasDerivAt_id x).div_const 2
    refine (h1.log (by positivity : (0 : ℝ) < x / 2).ne').congr_deriv ?_
    field_simp
  have hev : (fun y : ℝ => Real.log (besselIReal ν y))
      =ᶠ[nhds x] fun y : ℝ => ν * Real.log (y / 2)
        + Real.log (Zfun (ν + 1) ((y / 2) ^ 2)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact log_besselIReal hν hy
  refine (((hlogh.const_mul ν).add hcomp).congr_of_eventuallyEq hev).congr_deriv ?_
  rw [besselUfun]
  field_simp

/-- **`eq:U-L`, first identity.**  `besselUfun` *is* `Θ_x log I_ν = x∂_x log I_ν`. -/
theorem besselUfun_eq (hν : -1 < ν) (hx : 0 < x) :
    besselUfun ν x = x * deriv (fun y : ℝ => Real.log (besselIReal ν y)) x := by
  rw [(hasDerivAt_log_besselIReal_arg hν hx).deriv]
  field_simp

/-! ### `P_ν` -/

/-- `P_ν = 2B/Z² - 1` at `a = ν+1`, `λ = (x/2)²` (`eq:Pnu`, `eq:U-L`). -/
noncomputable def besselPfun (ν x : ℝ) : ℝ :=
  2 * Bseries (ν + 1) ((x / 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2 - 1

/-- `∂_ν(Θ_x log I_ν) = 2B/Z² - 1`: differentiating `eq:U-L` in the order.  The
affine term contributes `1`, and `∂_a(Z_Θ/Z) = (ZZ_{aΘ} - Z_aZ_Θ)/Z² = (B-Z²)/Z²`
by `eq:Bdef`. -/
theorem hasDerivAt_besselUfun_order (hν : -1 < ν) :
    HasDerivAt (fun t : ℝ => besselUfun t x) (besselPfun ν x) ν := by
  have ha : 0 < ν + 1 := by linarith
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  have hZne : Zfun (ν + 1) ((x / 2) ^ 2) ≠ 0 := hZ.ne'
  have hshift : HasDerivAt (fun t : ℝ => t + 1) 1 ν := (hasDerivAt_id ν).add_const 1
  have hE : HasDerivAt (fun t : ℝ => ZEulerSeries (t + 1) ((x / 2) ^ 2))
      (ZParamEulerSeries (ν + 1) ((x / 2) ^ 2)) ν := by
    simpa using (hasDerivAt_ZEulerSeries_param ha ((x / 2) ^ 2)).comp ν hshift
  have hZp : HasDerivAt (fun t : ℝ => Zfun (t + 1) ((x / 2) ^ 2))
      (ZParamSeries (ν + 1) ((x / 2) ^ 2)) ν := by
    have h : HasDerivAt (fun y : ℝ => Zfun y ((x / 2) ^ 2))
        (ZParamSeries (ν + 1) ((x / 2) ^ 2)) (ν + 1) :=
      hasDerivAt_Zfun_param ha ((x / 2) ^ 2)
    simpa using h.comp ν hshift
  have hq : HasDerivAt
      (fun t : ℝ => ZEulerSeries (t + 1) ((x / 2) ^ 2) / Zfun (t + 1) ((x / 2) ^ 2))
      ((ZParamEulerSeries (ν + 1) ((x / 2) ^ 2) * Zfun (ν + 1) ((x / 2) ^ 2)
          - ZEulerSeries (ν + 1) ((x / 2) ^ 2) * ZParamSeries (ν + 1) ((x / 2) ^ 2))
        / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2) ν := hE.div hZp hZne
  simp only [besselUfun]
  refine ((hasDerivAt_id ν).add (hq.const_mul 2)).congr_deriv ?_
  rw [besselPfun, Bseries]
  exact algebra_P _ _ _ _ hZne

/-- **`eq:Pnu` with `eq:U-L`.**  `besselPfun` *is* `∂_ν(Θ_x log I_ν)`. -/
theorem besselPfun_eq (hν : -1 < ν) (hx : 0 < x) :
    besselPfun ν x
      = deriv (fun t : ℝ => x * deriv (fun y : ℝ => Real.log (besselIReal t y)) x) ν := by
  refine ((hasDerivAt_besselUfun_order (x := x) hν).congr_of_eventuallyEq ?_).deriv.symm
  filter_upwards [eventually_gt_nhds hν] with t ht
  exact (besselUfun_eq ht hx).symm

/-! ### `H_ν` -/

/-- `H_ν = 4C/(gZ²) - 4/g` at `a = ν+1`, `λ = (x/2)²`, `g = ψ₁(a)`
(`eq:Hnu-kappa` at `κ = 1`, `eq:G-L`, `eq:ABC-log`). -/
noncomputable def besselHfun (ν x : ℝ) : ℝ :=
  4 * Cseries (ν + 1) (trigamma (ν + 1)) 1 1 ((x / 2) ^ 2)
      / (trigamma (ν + 1) * Zfun (ν + 1) ((x / 2) ^ 2) ^ 2)
    - 4 / trigamma (ν + 1)

/-- `∂_x(Θ_x log I_ν)`: the second Euler derivative in the argument. -/
theorem hasDerivAt_besselUfun_arg (hν : -1 < ν) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => besselUfun ν y)
      (2 * ((ZEuler2Series (ν + 1) ((x / 2) ^ 2) / (x / 2) ^ 2
              * Zfun (ν + 1) ((x / 2) ^ 2)
            - ZEulerSeries (ν + 1) ((x / 2) ^ 2)
              * (ZEulerSeries (ν + 1) ((x / 2) ^ 2) / (x / 2) ^ 2))
          / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2 * (x / 2))) x := by
  have ha : 0 < ν + 1 := by linarith
  have hlam : 0 < (x / 2) ^ 2 := by positivity
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha hlam.le
  have hq : HasDerivAt (fun y : ℝ => ZEulerSeries (ν + 1) y / Zfun (ν + 1) y)
      ((ZEuler2Series (ν + 1) ((x / 2) ^ 2) / (x / 2) ^ 2
          * Zfun (ν + 1) ((x / 2) ^ 2)
        - ZEulerSeries (ν + 1) ((x / 2) ^ 2)
          * (ZEulerSeries (ν + 1) ((x / 2) ^ 2) / (x / 2) ^ 2))
        / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2) ((x / 2) ^ 2) :=
    (hasDerivAt_ZEulerSeries_lam ha hlam.ne').div (hasDerivAt_Zfun_lam ha hlam.ne') hZ.ne'
  have hc := hq.comp x (hasDerivAt_half_sq x)
  simp only [besselUfun]
  exact (hc.const_mul 2).const_add ν

/-- **`Θ_x² log I_ν = 4(ZZ_{ΘΘ} - Z_Θ²)/Z²`.**  `Θ_x` applied to `eq:U-L`: the
affine term dies and `Θ_x = 2Θ_λ` doubles again, giving `4Θ_λ²L`. -/
theorem theta_sq_log_besselIReal (hν : -1 < ν) (hx : 0 < x) :
    x * deriv (fun y : ℝ => y * deriv (fun w : ℝ => Real.log (besselIReal ν w)) y) x
      = 4 * (Zfun (ν + 1) ((x / 2) ^ 2) * ZEuler2Series (ν + 1) ((x / 2) ^ 2)
              - ZEulerSeries (ν + 1) ((x / 2) ^ 2) ^ 2)
          / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2 := by
  have ha : 0 < ν + 1 := by linarith
  have hlam : 0 < (x / 2) ^ 2 := by positivity
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha hlam.le
  have hxne : x ≠ 0 := hx.ne'
  have hZne : Zfun (ν + 1) ((x / 2) ^ 2) ≠ 0 := hZ.ne'
  have hev : (fun y : ℝ => y * deriv (fun w : ℝ => Real.log (besselIReal ν w)) y)
      =ᶠ[nhds x] fun y : ℝ => besselUfun ν y := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact (besselUfun_eq hν hy).symm
  rw [hev.deriv_eq, (hasDerivAt_besselUfun_arg hν hx).deriv]
  exact algebra_theta2 _ _ _ _ hxne hZne

/-- **`eq:Hnu-kappa` at `κ = 1`.**  `besselHfun` *is*
`2(Θ_x log I_ν - ν) - Θ_x² log I_ν`, with `Θ_x = x∂_x` written out on both
occurrences. -/
theorem besselHfun_eq (hν : -1 < ν) (hx : 0 < x) :
    besselHfun ν x
      = 2 * (x * deriv (fun y : ℝ => Real.log (besselIReal ν y)) x - ν)
        - x * deriv (fun y : ℝ => y * deriv (fun w : ℝ => Real.log (besselIReal ν w)) y) x := by
  have ha : 0 < ν + 1 := by linarith
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  have hZne : Zfun (ν + 1) ((x / 2) ^ 2) ≠ 0 := hZ.ne'
  have hgne : trigamma (ν + 1) ≠ 0 := (trigamma_pos ha).ne'
  rw [← besselUfun_eq hν hx, theta_sq_log_besselIReal hν hx, besselHfun, besselUfun,
    Cseries]
  exact algebra_H _ _ _ _ _ hgne hZne

/-! ### `eq:D-Delta` -/

/-- **`eq:D-Delta`.**  `D_ν = G_ν(H_ν + 4/g) - (1+P_ν)² = 4Δ(a,λ)/(gZ⁴)`.  Pure
algebra in `A, B, C, Z, g` once `eq:Gnu`, `eq:Pnu` and `eq:Hnu-kappa` are in the
`A/Z²`, `2B/Z² - 1`, `4C/(gZ²) - 4/g` forms of `eq:ABC-log`. -/
theorem besselDet_eq_turanDet (hν : -1 < ν) (hx : 0 < x) :
    besselGfun ν x * (besselHfun ν x + 4 / trigamma (ν + 1)) - (1 + besselPfun ν x) ^ 2
      = 4 * turanDet (ν + 1) ((x / 2) ^ 2)
          / (trigamma (ν + 1) * Zfun (ν + 1) ((x / 2) ^ 2) ^ 4) := by
  have ha : 0 < ν + 1 := by linarith
  have hlam : 0 < (x / 2) ^ 2 := by positivity
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha hlam.le
  have hZne : Zfun (ν + 1) ((x / 2) ^ 2) ≠ 0 := hZ.ne'
  have hgne : trigamma (ν + 1) ≠ 0 := (trigamma_pos ha).ne'
  rw [besselGfun, besselHfun, besselPfun, turanDet]
  exact algebra_D _ _ _ _ _ hgne hZne

/-! ### `Δ(a,λ) > 0` -/

/-- `Dcoeff a 0 = 0`: the degree-zero sector is `s_0² MD(N_0,N_0) = 2s_0² det N_0`,
and `det N_0 = gg^{-1} - 1 = 0`. -/
theorem Dcoeff_zero (ha : 0 < a) : Dcoeff a 0 = 0 := by
  have hg : trigamma a ≠ 0 := (trigamma_pos ha).ne'
  have hMD : SymMat.MD (Nmat a 0) (Nmat a 0) = 0 := by
    simp only [SymMat.MD, Nmat_a11, Nmat_a12, Nmat_a22, αcoef, βcoef_zero, ccoef_zero,
      Nat.cast_zero, add_zero]
    field_simp
    norm_num
  simp [Dcoeff, hMD]

/-- **`Δ(a,λ) > 0` for `a > 0`, `λ > 0`.**  `hasSum_turanDet` expands `Δ` in its
Maclaurin series; the degree-zero term vanishes and every higher term is strictly
positive by `coefficientwise_positivity`. -/
theorem turanDet_pos (ha : 0 < a) (hlam : 0 < lam) : 0 < turanDet a lam := by
  have hfac : 0 < trigamma a / (2 * Real.Gamma a ^ 4) :=
    div_pos (trigamma_pos ha)
      (mul_pos (by norm_num) (pow_pos (Real.Gamma_pos_of_pos ha) 4))
  have hsum := hasSum_turanDet ha lam
  have hnn : ∀ n : ℕ, 0 ≤ trigamma a / (2 * Real.Gamma a ^ 4) * Dcoeff a n * lam ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [Dcoeff_zero ha]
    · exact (mul_pos (mul_pos hfac (coefficientwise_positivity ha h)) (pow_pos hlam n)).le
  rw [← hsum.tsum_eq]
  exact hsum.summable.tsum_pos hnn 1
    (mul_pos (mul_pos hfac (coefficientwise_positivity ha le_rfl)) (pow_pos hlam 1))

end TuranBessel
