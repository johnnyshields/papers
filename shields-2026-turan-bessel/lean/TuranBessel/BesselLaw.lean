/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.BesselDictPH

/-!
# The discrete Bessel law and the covariance-deficit reading

`shields-2026-turan-bessel.tex`, «Microcanonical Bessel fibers and canonical
averaging» (`subsec:microcanonical`, `eq:bessel-law`, `cor:bessel-law`,
`eq:bessel-law-meanvar`, `eq:bessel-law-param`, `eq:covariance-deficit-matrix`,
`eq:covariance-loewner`, `eq:H-dispersion`, `eq:covariance-ineq`).

The law `P(Y=k) = λ^k/(k!Γ(a+k)Z(a,λ))` is `Z`'s own series renormalized, so each
of its moments is one of the weighted `Z`-series already assembled for
`eq:ABC-log`, divided by `Z`:

    E Y  = Z_Θ/Z          E Y² = Z_{ΘΘ}/Z
    E Ψ  = -Z_a/Z         E(ΨY) = -Z_{aΘ}/Z          Ψ = ψ(a+Y)

with `E Ψ²` and `E ψ₁(a+Y)` the two halves of `Z_{aa} = Z(E Ψ² - E ψ₁(a+Y))`.
The three entries of the normalized Turánian are then covariance deficits,

    A/Z²          = E ψ₁(a+Y) - Var Ψ                      (`eq:bessel-law-param`)
    B/Z²          = 1 - Cov(Ψ,Y)                           (`eq:bessel-law-param`)
    C_{κ,τ}/(gZ²) = τ/g + κ E Y - Var Y                    (`eq:bessel-law-meanvar`)

`thm:bessel` becomes `eq:covariance-ineq` and `H_ν^{(κ)} > 0` becomes
underdispersion of the law.

Sorry-free.
-/

namespace TuranBessel

open Set

variable {a lam ν x g κ τ : ℝ}

/-! ### The law `eq:bessel-law` -/

/-- The discrete Bessel law of `eq:bessel-law`:
`P(Y = k) = λ^k/(k!Γ(a+k)Z(a,λ))`. -/
noncomputable def besselPMF (a lam : ℝ) (k : ℕ) : ℝ := zterm a lam k / Zfun a lam

/-- `E f(Y)` under `eq:bessel-law`. -/
noncomputable def besselExp (a lam : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, f k * besselPMF a lam k

/-- An expectation is the matching weighted `Z`-series over `Z`.  This is the only
bridge the rest of the file needs: every moment below is one of the series that
`ParameterCalculus` and `BetaGammaCoeff` already differentiate under the
summation sign. -/
theorem besselExp_eq (f : ℕ → ℝ) :
    besselExp a lam f = (∑' k : ℕ, f k * zterm a lam k) / Zfun a lam := by
  rw [besselExp, div_eq_mul_inv, ← tsum_mul_right]
  exact tsum_congr fun k => by rw [besselPMF, div_eq_mul_inv]; ring

theorem besselPMF_nonneg (ha : 0 < a) (hlam : 0 ≤ lam) (k : ℕ) : 0 ≤ besselPMF a lam k := by
  have hG : 0 < Real.Gamma (a + (k : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hf : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [besselPMF, zterm]
  exact div_nonneg (div_nonneg (pow_nonneg hlam k) (by positivity)) (Zfun_pos ha hlam).le

/-- **`eq:bessel-law` is a probability law.**  `Zseries` already supplies both
ingredients: the terms are summable and `Z > 0`. -/
theorem hasSum_besselPMF (ha : 0 < a) (hlam : 0 ≤ lam) : HasSum (besselPMF a lam) 1 := by
  have hZ := Zfun_pos ha hlam
  have h : HasSum (zterm a lam) (Zfun a lam) := by
    rw [Zfun]; exact (summable_zterm ha lam).hasSum
  have h2 := h.div_const (Zfun a lam)
  rw [div_self hZ.ne'] at h2
  exact h2

theorem besselExp_const_one (ha : 0 < a) (hlam : 0 ≤ lam) :
    besselExp a lam (fun _ => 1) = 1 := by
  have h : besselExp a lam (fun _ => 1) = (∑' k : ℕ, (1 : ℝ) * zterm a lam k) / Zfun a lam :=
    besselExp_eq _
  rw [h, ← Zfun_eq_weighted, div_self (Zfun_pos ha hlam).ne']

/-! ### The two weights `ψ(a+k)²` and `ψ₁(a+k)`

`BetaGammaCoeff` covers `1, k, k², -ψ(a+k), -kψ(a+k)`; `Z_{aa}` needs the other
two.  Both clear the `C(k+1)²` bar of `summable_norm_weighted_zterm` — the
digamma square by squaring the linear bound, the trigamma by `trigamma_anti`,
which makes it bounded outright. -/

theorem summable_norm_psisq_zterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k : ℕ => ‖realDigamma (a + (k : ℝ)) ^ 2 * zterm a lam k‖) :=
  summable_norm_weighted_zterm ha lam (C := (2 * |realDigamma a| + 1 / a) ^ 2) 2 (fun k => by
    have h := abs_realDigamma_add_nat_le_linear ha k
    have hC : (0 : ℝ) ≤ 2 * |realDigamma a| + 1 / a := by positivity
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hb : (0 : ℝ) ≤ (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1) :=
      mul_nonneg hC (by linarith)
    rw [abs_pow]
    calc |realDigamma (a + (k : ℝ))| ^ 2
        ≤ ((2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1)) ^ 2 := by
          rw [sq, sq]; exact mul_le_mul h h (abs_nonneg _) hb
      _ = (2 * |realDigamma a| + 1 / a) ^ 2 * ((k : ℝ) + 1) ^ 2 := by ring)

theorem summable_norm_trigamma_zterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k : ℕ => ‖trigamma (a + (k : ℝ)) * zterm a lam k‖) :=
  summable_norm_weighted_zterm ha lam (C := trigamma a) 2 (fun k => by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpos : 0 < trigamma (a + (k : ℝ)) := trigamma_pos (by linarith)
    have hle : trigamma (a + (k : ℝ)) ≤ trigamma a := trigamma_anti ha (by linarith)
    have hga : 0 < trigamma a := trigamma_pos ha
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    rw [abs_of_pos hpos]
    calc trigamma (a + (k : ℝ)) ≤ trigamma a := hle
      _ = trigamma a * 1 := by ring
      _ ≤ trigamma a * ((k : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_left h1 hga.le)

/-! ### Moments of the law -/

/-- `μ = E Y` (`cor:bessel-law`). -/
noncomputable def besselMean (a lam : ℝ) : ℝ := besselExp a lam (fun k => (k : ℝ))

/-- `σ² = Var Y` (`cor:bessel-law`). -/
noncomputable def besselVar (a lam : ℝ) : ℝ :=
  besselExp a lam (fun k => (k : ℝ) ^ 2) - besselMean a lam ^ 2

/-- `E Ψ` for `Ψ = ψ(a+Y)` (`cor:bessel-law`). -/
noncomputable def besselExpPsi (a lam : ℝ) : ℝ :=
  besselExp a lam (fun k => realDigamma (a + (k : ℝ)))

/-- `Var Ψ`. -/
noncomputable def besselVarPsi (a lam : ℝ) : ℝ :=
  besselExp a lam (fun k => realDigamma (a + (k : ℝ)) ^ 2) - besselExpPsi a lam ^ 2

/-- `Cov(Ψ, Y)`. -/
noncomputable def besselCovPsi (a lam : ℝ) : ℝ :=
  besselExp a lam (fun k => realDigamma (a + (k : ℝ)) * (k : ℝ))
    - besselExpPsi a lam * besselMean a lam

/-- `E ψ₁(a+Y)`. -/
noncomputable def besselExpTrigamma (a lam : ℝ) : ℝ :=
  besselExp a lam (fun k => trigamma (a + (k : ℝ)))

theorem besselMean_eq : besselMean a lam = ZEulerSeries a lam / Zfun a lam := besselExp_eq _

theorem besselExpSq_eq :
    besselExp a lam (fun k => (k : ℝ) ^ 2) = ZEuler2Series a lam / Zfun a lam :=
  besselExp_eq _

theorem besselExpPsi_eq : besselExpPsi a lam = -(ZParamSeries a lam / Zfun a lam) := by
  have h : ∑' k : ℕ, realDigamma (a + (k : ℝ)) * zterm a lam k = -ZParamSeries a lam := by
    rw [ZParamSeries, ← tsum_neg]
    exact tsum_congr fun k => by ring
  have h2 : besselExpPsi a lam
      = (∑' k : ℕ, realDigamma (a + (k : ℝ)) * zterm a lam k) / Zfun a lam := besselExp_eq _
  rw [h2, h, neg_div]

theorem besselExpPsiIdx_eq :
    besselExp a lam (fun k => realDigamma (a + (k : ℝ)) * (k : ℝ))
      = -(ZParamEulerSeries a lam / Zfun a lam) := by
  have h : ∑' k : ℕ, realDigamma (a + (k : ℝ)) * (k : ℝ) * zterm a lam k
      = -ZParamEulerSeries a lam := by
    rw [ZParamEulerSeries, ← tsum_neg]
    exact tsum_congr fun k => by ring
  have h2 : besselExp a lam (fun k => realDigamma (a + (k : ℝ)) * (k : ℝ))
      = (∑' k : ℕ, realDigamma (a + (k : ℝ)) * (k : ℝ) * zterm a lam k) / Zfun a lam :=
    besselExp_eq _
  rw [h2, h, neg_div]

/-! ### `Z_a` and `Z_{aa}` in the moment atoms -/

theorem Zparam1_eq_ZParamSeries (ha : 0 < a) (lam : ℝ) :
    Zparam1 a lam = ZParamSeries a lam := by
  rw [Zparam1]; exact (ZParamSeries_eq_deriv ha lam).symm

/-- `Z_{aa} = Z(E Ψ² - E ψ₁(a+Y))`, split into its two summable halves. -/
theorem Zparam2_eq_split (ha : 0 < a) (lam : ℝ) :
    Zparam2 a lam
      = (∑' k : ℕ, realDigamma (a + (k : ℝ)) ^ 2 * zterm a lam k)
        - ∑' k : ℕ, trigamma (a + (k : ℝ)) * zterm a lam k := by
  rw [Zparam2_eq ha,
    ← Summable.tsum_sub (summable_norm_psisq_zterm ha lam).of_norm
      (summable_norm_trigamma_zterm ha lam).of_norm]
  exact tsum_congr fun k => by ring

/-! ### `cor:bessel-law`: the three entries as covariance deficits

Stated over abstract reals first, because each is pure field algebra in the
atoms `Z, Z_Θ, Z_{ΘΘ}, Z_a, Z_{aΘ}, E Ψ², E ψ₁` and `g`. -/

private theorem algebra_A (Z Zp TP TG : ℝ) (hZ : Z ≠ 0) :
    (Zp ^ 2 - Z * (TP - TG)) / Z ^ 2 = TG / Z - (TP / Z - (-(Zp / Z)) ^ 2) := by
  field_simp; ring

private theorem algebra_B (Z E Zp Zpe : ℝ) (hZ : Z ≠ 0) :
    (Z * Z + Z * Zpe - Zp * E) / Z ^ 2
      = 1 - (-(Zpe / Z) - -(Zp / Z) * (E / Z)) := by
  field_simp; ring

private theorem algebra_C (Z E E2 g κ τ : ℝ) (hZ : Z ≠ 0) (hg : g ≠ 0) :
    (τ * (Z * Z) + g * (κ * (Z * E) - Z * E2 + E * E)) / (g * Z ^ 2)
      = τ / g + κ * (E / Z) - (E2 / Z - (E / Z) ^ 2) := by
  field_simp; ring

/-- **`eq:bessel-law-param`, second identity.**  `-L_{aa} = A/Z² = E ψ₁(a+Y) - Var Ψ`.
With `BesselDict.besselGfun_eq` this reads `G_ν = E ψ₁(a+Y) - Var Ψ`. -/
theorem Afun_div_sq_eq (ha : 0 < a) (hlam : 0 ≤ lam) :
    Afun a lam / Zfun a lam ^ 2 = besselExpTrigamma a lam - besselVarPsi a lam := by
  have hZ := (Zfun_pos ha hlam).ne'
  have hT : besselExpTrigamma a lam
      = (∑' k : ℕ, trigamma (a + (k : ℝ)) * zterm a lam k) / Zfun a lam := besselExp_eq _
  have hP : besselExp a lam (fun k => realDigamma (a + (k : ℝ)) ^ 2)
      = (∑' k : ℕ, realDigamma (a + (k : ℝ)) ^ 2 * zterm a lam k) / Zfun a lam :=
    besselExp_eq _
  rw [besselVarPsi, hT, hP, besselExpPsi_eq, Afun, Zparam1_eq_ZParamSeries ha,
    Zparam2_eq_split ha]
  exact algebra_A _ _ _ _ hZ

/-- **`eq:bessel-law-param`, first identity.**  `L_{aΘλ} = -Cov(Ψ,Y)`, in the form
`B/Z² = 1 - Cov(Ψ,Y)` that `rem:canonical-origin` puts it in.  With
`BesselDictPH.besselPfun_eq` this reads `1 + P_ν = 2(1 - Cov(Ψ,Y))`. -/
theorem Bseries_div_sq_eq (ha : 0 < a) (hlam : 0 ≤ lam) :
    Bseries a lam / Zfun a lam ^ 2 = 1 - besselCovPsi a lam := by
  have hZ := (Zfun_pos ha hlam).ne'
  rw [besselCovPsi, besselExpPsiIdx_eq, besselExpPsi_eq, besselMean_eq, Bseries]
  exact algebra_B _ _ _ _ hZ

/-- **`eq:bessel-law-meanvar`.**  `L_{Θλ} = μ` and `L_{ΘλΘλ} = σ²`, in the combined
form `C_{κ,τ}/(gZ²) = τ/g + κμ - σ²` that `rem:canonical-origin` puts them in. -/
theorem Cseries_div_eq (ha : 0 < a) (hlam : 0 ≤ lam) (hg : g ≠ 0) (κ τ : ℝ) :
    Cseries a g κ τ lam / (g * Zfun a lam ^ 2)
      = τ / g + κ * besselMean a lam - besselVar a lam := by
  have hZ := (Zfun_pos ha hlam).ne'
  rw [besselVar, besselExpSq_eq, besselMean_eq, Cseries]
  exact algebra_C _ _ _ _ _ _ hZ hg

/-! ### `eq:covariance-deficit-matrix` and `eq:covariance-loewner` -/

/-- The normalized Turánian `(1/Z²)diag(1,g^{-1/2})𝒯_{κ,τ}diag(1,g^{-1/2})` of
`eq:canonical-fiber-average`, at `g = ψ₁(a)`. -/
noncomputable def normalizedTuran (a κ τ lam : ℝ) : SymMat :=
  ⟨Afun a lam / Zfun a lam ^ 2, Bseries a lam / Zfun a lam ^ 2,
    Cseries a (trigamma a) κ τ lam / (trigamma a * Zfun a lam ^ 2)⟩

/-- The baseline matrix of `eq:covariance-loewner`. -/
noncomputable def besselBaselineMat (a κ τ lam : ℝ) : SymMat :=
  ⟨besselExpTrigamma a lam, 1, τ / trigamma a + κ * besselMean a lam⟩

/-- `Cov(Ψ,Y)` as a symmetric matrix (`eq:covariance-loewner`). -/
noncomputable def besselCovMat (a lam : ℝ) : SymMat :=
  ⟨besselVarPsi a lam, besselCovPsi a lam, besselVar a lam⟩

/-- **`eq:covariance-deficit-matrix`.**  The normalized Turánian is the
covariance-deficit matrix of the Bessel law. -/
theorem normalizedTuran_eq (ha : 0 < a) (hlam : 0 ≤ lam) (κ τ : ℝ) :
    normalizedTuran a κ τ lam
      = ⟨besselExpTrigamma a lam - besselVarPsi a lam, 1 - besselCovPsi a lam,
          τ / trigamma a + κ * besselMean a lam - besselVar a lam⟩ := by
  refine SymMat.ext (Afun_div_sq_eq ha hlam) (Bseries_div_sq_eq ha hlam) ?_
  exact Cseries_div_eq ha hlam (trigamma_pos ha).ne' κ τ

/-- **`eq:covariance-loewner`.**  The same matrix regrouped: baseline minus the
covariance matrix of `(Ψ,Y)`.  This is `eq:covariance-deficit-matrix` with the
entries collected, which is exactly what the paper's "equivalently" asserts. -/
theorem normalizedTuran_eq_baseline_sub_cov (ha : 0 < a) (hlam : 0 ≤ lam) (κ τ : ℝ) :
    normalizedTuran a κ τ lam
      = ⟨(besselBaselineMat a κ τ lam).a11 - (besselCovMat a lam).a11,
          (besselBaselineMat a κ τ lam).a12 - (besselCovMat a lam).a12,
          (besselBaselineMat a κ τ lam).a22 - (besselCovMat a lam).a22⟩ := by
  rw [normalizedTuran_eq ha hlam]
  exact SymMat.ext rfl rfl rfl

/-! ### `eq:H-dispersion`: `H_ν^{(κ)}` is four times the dispersion gap -/

/-- `H_ν^{(κ)} = 2κ(Θ_x log I_ν - ν) - Θ_x² log I_ν` (`eq:Hnu-kappa`), as
`4C_{κ,1}/(gZ²) - 4/g`.  `BesselDictPH.besselHfun` is the `κ = 1` case
(`besselHfun_eq_besselHkappa`). -/
noncomputable def besselHkappa (κ ν x : ℝ) : ℝ :=
  4 * Cseries (ν + 1) (trigamma (ν + 1)) κ 1 ((x / 2) ^ 2)
      / (trigamma (ν + 1) * Zfun (ν + 1) ((x / 2) ^ 2) ^ 2)
    - 4 / trigamma (ν + 1)

private theorem algebra_Hk (κ ν Z E E2 g : ℝ) (hg : g ≠ 0) (hZ : Z ≠ 0) :
    4 * (1 * (Z * Z) + g * (κ * (Z * E) - Z * E2 + E * E)) / (g * Z ^ 2) - 4 / g
      = 2 * κ * (ν + 2 * (E / Z) - ν) - 4 * (Z * E2 - E ^ 2) / Z ^ 2 := by
  field_simp; ring

/-- **`eq:Hnu-kappa` at general `κ`.**  `BesselDictPH.besselHfun_eq` is the `κ = 1`
case; the `κ`-deformation costs nothing beyond carrying the parameter through the
same field algebra. -/
theorem besselHkappa_eq (hν : -1 < ν) (hx : 0 < x) (κ : ℝ) :
    besselHkappa κ ν x
      = 2 * κ * (x * deriv (fun y : ℝ => Real.log (besselIReal ν y)) x - ν)
        - x * deriv (fun y : ℝ => y * deriv (fun w : ℝ => Real.log (besselIReal ν w)) y) x := by
  have ha : 0 < ν + 1 := by linarith
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  rw [← besselUfun_eq hν hx, theta_sq_log_besselIReal hν hx, besselHkappa, besselUfun, Cseries]
  exact algebra_Hk _ _ _ _ _ _ (trigamma_pos ha).ne' hZ.ne'

theorem besselHfun_eq_besselHkappa (ν x : ℝ) : besselHfun ν x = besselHkappa 1 ν x := rfl

/-- **`eq:H-dispersion`.**  `H_ν^{(κ)} = 4(κμ - σ²)`. -/
theorem besselHkappa_eq_dispersion (hν : -1 < ν) (κ : ℝ) :
    besselHkappa κ ν x
      = 4 * (κ * besselMean (ν + 1) ((x / 2) ^ 2) - besselVar (ν + 1) ((x / 2) ^ 2)) := by
  have ha : 0 < ν + 1 := by linarith
  have hg : trigamma (ν + 1) ≠ 0 := (trigamma_pos ha).ne'
  have hZ := (Zfun_pos ha (sq_nonneg (x / 2))).ne'
  have hC := Cseries_div_eq (a := ν + 1) (lam := (x / 2) ^ 2) (g := trigamma (ν + 1))
    ha (sq_nonneg _) hg κ 1
  rw [besselHkappa]
  rw [show 4 * Cseries (ν + 1) (trigamma (ν + 1)) κ 1 ((x / 2) ^ 2)
        / (trigamma (ν + 1) * Zfun (ν + 1) ((x / 2) ^ 2) ^ 2)
      = 4 * (Cseries (ν + 1) (trigamma (ν + 1)) κ 1 ((x / 2) ^ 2)
        / (trigamma (ν + 1) * Zfun (ν + 1) ((x / 2) ^ 2) ^ 2)) by ring, hC]
  field

/-- **`H_ν > 0` is underdispersion of the Bessel law** — the reading
`cor:bessel-law` closes on, at `κ = 1`. -/
theorem besselHfun_pos_iff_underdispersed (hν : -1 < ν) :
    0 < besselHfun ν x
      ↔ besselVar (ν + 1) ((x / 2) ^ 2) < besselMean (ν + 1) ((x / 2) ^ 2) := by
  rw [besselHfun_eq_besselHkappa, besselHkappa_eq_dispersion hν]
  constructor <;> intro h <;> nlinarith

/-! ### `eq:covariance-ineq`: `thm:bessel` as a covariance inequality -/

/-- **`eq:covariance-ineq`.**  For `a > 0`, `λ > 0`,
`(1 - Cov(Ψ,Y))² < (E ψ₁(a+Y) - Var Ψ)(1/g + E Y - Var Y)`.

This is `Δ > 0` (`BesselDictPH.turanDet_pos`) divided by `gZ⁴`, rewritten through
the three entry identities.  Every `λ > 0` occurs as `(z/2)²`, so with `a = ν+1`
this is `thm:bessel`; `besselDefect_eq_covariance` states that equivalence as an
identity. -/
theorem covariance_ineq (ha : 0 < a) (hlam : 0 < lam) :
    (1 - besselCovPsi a lam) ^ 2
      < (besselExpTrigamma a lam - besselVarPsi a lam)
        * (1 / trigamma a + besselMean a lam - besselVar a lam) := by
  have hZ : 0 < Zfun a lam := Zfun_pos ha hlam.le
  have hg : 0 < trigamma a := trigamma_pos ha
  have hden : 0 < trigamma a * Zfun a lam ^ 4 := by positivity
  have halg : (Afun a lam / Zfun a lam ^ 2)
        * (Cseries a (trigamma a) 1 1 lam / (trigamma a * Zfun a lam ^ 2))
      - (Bseries a lam / Zfun a lam ^ 2) ^ 2
      = turanDet a lam / (trigamma a * Zfun a lam ^ 4) := by
    rw [turanDet]
    field_simp
  have hpos : 0 < turanDet a lam / (trigamma a * Zfun a lam ^ 4) :=
    div_pos (turanDet_pos ha hlam) hden
  have hA := Afun_div_sq_eq ha hlam.le
  have hB := Bseries_div_sq_eq ha hlam.le
  have hC := Cseries_div_eq ha hlam.le hg.ne' 1 1
  rw [hA, hB, hC] at halg
  have hone : (1 : ℝ) / trigamma a + 1 * besselMean a lam - besselVar a lam
      = 1 / trigamma a + besselMean a lam - besselVar a lam := by ring
  rw [hone] at halg
  linarith [halg, hpos]

/-- **`eq:covariance-ineq` is `thm:bessel`.**  The Bessel--Schur defect of
`eq:Dnu-def` is four times the covariance slack, so the two strict inequalities
are the same statement. -/
theorem besselDefect_eq_covariance (hν : -1 < ν) (hx : 0 < x) :
    besselGfun ν x * (besselHfun ν x + 4 / trigamma (ν + 1)) - (1 + besselPfun ν x) ^ 2
      = 4 * ((besselExpTrigamma (ν + 1) ((x / 2) ^ 2) - besselVarPsi (ν + 1) ((x / 2) ^ 2))
              * (1 / trigamma (ν + 1) + besselMean (ν + 1) ((x / 2) ^ 2)
                  - besselVar (ν + 1) ((x / 2) ^ 2))
            - (1 - besselCovPsi (ν + 1) ((x / 2) ^ 2)) ^ 2) := by
  have ha : 0 < ν + 1 := by linarith
  have hlam : (0 : ℝ) < (x / 2) ^ 2 := by positivity
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha hlam.le
  have hg : 0 < trigamma (ν + 1) := trigamma_pos ha
  have hA := Afun_div_sq_eq ha hlam.le
  have hB := Bseries_div_sq_eq ha hlam.le
  have hC := Cseries_div_eq (a := ν + 1) (lam := (x / 2) ^ 2) ha hlam.le hg.ne' 1 1
  have hone : (1 : ℝ) / trigamma (ν + 1) + 1 * besselMean (ν + 1) ((x / 2) ^ 2)
        - besselVar (ν + 1) ((x / 2) ^ 2)
      = 1 / trigamma (ν + 1) + besselMean (ν + 1) ((x / 2) ^ 2)
        - besselVar (ν + 1) ((x / 2) ^ 2) := by ring
  rw [hone] at hC
  rw [← hA, ← hB, ← hC, besselGfun, besselHfun, besselPfun]
  field

end TuranBessel
