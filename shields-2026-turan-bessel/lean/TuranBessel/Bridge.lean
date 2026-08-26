/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Main
import TuranBessel.TuranDet
import TuranBessel.BesselDict
import TuranBessel.BesselDictPH

/-!
# Analytic bridge and Bessel consequences

The proven core (`coefficientwise_positivity`) concerns `Dcoeff a n`, the
combinatorial mixed-determinant sum built from the closed-form coefficient
matrices `N_m`.  Both analytic bridges of `shields-2026-turan-bessel.tex` are
discharged in the tree:

1. **The coefficient formulas** — «Reciprocal-gamma convolution and
   canonical--microcanonical structure» (`sec:coefficients`, `thm:coefficients`).
   `lem:convolution` is proved in `Convolution`, `[λ^m] Z² = S_m` in `Zseries`,
   and the parameter calculus in `ParameterCalculus`; `TuranDet.hasSum_turanDet`
   assembles them into `Δ(a,λ) = ∑_n Δ_n(a)λⁿ`.

2. **The Bessel dictionary** — «Classical scalar Bessel directions»
   (`sec:scalar`, `eq:I-Z`, `eq:U-L`, `eq:G-L`, `eq:ABC-log`, `eq:D-Delta`).
   `BesselI` proves `eq:I-Z` over the `besselIReal` defined there and splits
   `log I_ν` into a term affine in `ν` plus `log Z`; `BesselDict` runs the
   `ν`-side and `BesselDictPH` the `Θ_x`-side, so `G_ν`, `P_ν` and `H_ν` are all
   definitions whose `_eq` theorems identify them with the derivatives of
   `log I_ν` that `eq:Gnu`--`eq:Hnu-kappa` prescribe.

Everything below therefore *consumes* `coefficientwise_positivity` and the
dictionary: `eq:D-Delta` turns the Bessel--Schur determinant into
`4Δ/(gZ⁴)`, and `BesselDictPH.turanDet_pos` supplies `Δ > 0` for `λ > 0` from the
coefficientwise theorem.  `thm:bessel` and `cor:bessel-matrix` are unconditional.

The scalar algebra of `sec:scalar` itself — `prop:scalar-H`, the Amos-type root
and the Turánian form of `H_ν^{(κ)}` — is proved without Bessel functions in
`ScalarH`.
-/

namespace TuranBessel

/-! ### Bridge 1 — the true Turán-determinant coefficients -/

/-- The positive normalization `ψ₁(a) Γ(a)^{-4}/2 = Δ_n / Dcoeff`, via `Real.Gamma`. -/
noncomputable def turanCoeffFactor (a : ℝ) : ℝ := trigamma a / (2 * Real.Gamma a ^ 4)

theorem turanCoeffFactor_pos (a : ℝ) (ha : 0 < a) : 0 < turanCoeffFactor a :=
  div_pos (trigamma_pos ha)
    (mul_pos (by norm_num) (pow_pos (Real.Gamma_pos_of_pos ha) 4))

/-- `Δ_n(a) = [λⁿ] det 𝒯(a,λ)`.  The definition supplies the value;
`hasSum_turanDetCoeff` below is the theorem that this value really is the `n`-th
Maclaurin coefficient of the genuine determinant `TuranDet.turanDet` rather than a
stand-in for it. -/
noncomputable def turanDetCoeff (a : ℝ) (n : ℕ) : ℝ := turanCoeffFactor a * Dcoeff a n

/-- **`eq:Delta-n-MD`, discharged.**  `Δ(a,λ) = det 𝒯(a,λ)` is the sum of
`∑ₙ Δ_n(a) λⁿ` for every real `λ`, with `Δ_n = turanCoeffFactor(a)·Dcoeff(a,n)`.

The chain is `AlphaCoeff.hasSum_Afun` (`eq:alpha`), `BetaGammaCoeff.tsum_beta_eq_B` and
`tsum_gamma_eq_C` (`eq:beta` and the `γ` identity), and
`DetAssembly.cauchy_eq_factor_mul_Dcoeff` for the Cauchy product and
symmetrization; `TuranDet.hasSum_turanDet` assembles them.  Nothing here is
definitional bookkeeping: the definition above supplies the *value*, and this
theorem supplies the *fact that it is the coefficient*, which is where all the
analysis sits. -/
theorem hasSum_turanDetCoeff {a : ℝ} (ha : 0 < a) (lam : ℝ) :
    HasSum (fun n : ℕ => turanDetCoeff a n * lam ^ n) (turanDet a lam) :=
  hasSum_turanDet ha lam

/-- The definitional unfolding of `turanDetCoeff`, carried as a named equation so
that downstream code and the paper's `eq:Delta-n-MD` reference resolve to it.  Its
mathematical content lives in `hasSum_turanDetCoeff`, not here. -/
theorem turanDetCoeff_eq (a : ℝ) (n : ℕ) :
    turanDetCoeff a n = turanCoeffFactor a * Dcoeff a n := rfl

/-- **`thm:coefficientwise` for the true determinant.**  Every positive-degree
Maclaurin coefficient of `det 𝒯(a,·)` is strictly positive for `a > 0` — proven
from `coefficientwise_positivity` and the bridge. -/
theorem turanDetCoeff_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    0 < turanDetCoeff a n := by
  rw [turanDetCoeff_eq]
  exact mul_pos (turanCoeffFactor_pos a ha) (coefficientwise_positivity ha hn)

section BesselSchur

variable {ν z : ℝ}

/-! ### Bridge 2 — the Bessel–Schur determinant -/

/-! The curvature functionals `G_ν, P_ν, H_ν` of `eq:Gnu`, `eq:Pnu`,
`eq:Hnu-kappa` at `κ = 1`.  All three are definitions carrying an `_eq`
theorem that identifies them with the prescribed derivative of `log I_ν`, so none
of them is a name standing in for the paper's object.  The scalar identities
`prop:scalar-H` satisfies in the ratio variable are proved in `ScalarH`. -/

/-- `G_ν = -∂_ν² log I_ν` (`eq:Gnu`).  `BesselDict.besselGfun` defines it as
`A/Z²` and `besselGfun_eq` proves that value is the second `ν`-derivative. -/
noncomputable def besselG : ℝ → ℝ → ℝ := besselGfun

/-- **`eq:Gnu`, discharged.** -/
theorem besselG_eq (hν : -1 < ν) (hz : 0 < z) :
    besselG ν z = -deriv (deriv fun t : ℝ => Real.log (besselIReal t z)) ν :=
  besselGfun_eq hν hz

/-- `P_ν = ∂_ν(Θ_z log I_ν)` (`eq:Pnu`).  `BesselDictPH.besselPfun` defines it as
`2B/Z² - 1` and `besselPfun_eq` proves that value is the order derivative of the
Euler derivative. -/
noncomputable def besselP : ℝ → ℝ → ℝ := besselPfun

/-- **`eq:Pnu` with `eq:U-L`, discharged.** -/
theorem besselP_eq (hν : -1 < ν) (hz : 0 < z) :
    besselP ν z
      = deriv (fun t : ℝ => z * deriv (fun y : ℝ => Real.log (besselIReal t y)) z) ν :=
  besselPfun_eq hν hz

/-- `H_ν = H_ν^{(1)} = 2(Θ_z log I_ν - ν) - Θ_z² log I_ν` (`eq:Hnu-kappa` at
`κ = 1`).  `BesselDictPH.besselHfun` defines it as `4C/(gZ²) - 4/g` and
`besselHfun_eq` proves that value is that combination of Euler derivatives. -/
noncomputable def besselH : ℝ → ℝ → ℝ := besselHfun

/-- **`eq:Hnu-kappa` at `κ = 1`, discharged.** -/
theorem besselH_eq (hν : -1 < ν) (hz : 0 < z) :
    besselH ν z
      = 2 * (z * deriv (fun y : ℝ => Real.log (besselIReal ν y)) z - ν)
        - z * deriv (fun y : ℝ => y * deriv (fun w : ℝ => Real.log (besselIReal ν w)) y) z :=
  besselHfun_eq hν hz

/-- **`eq:Dnu-def` with `eq:D-Delta`.**  The Bessel--Schur defect is a positive
multiple of the Turán determinant: `D_ν = 4Δ(ν+1,(z/2)²)/(ψ₁(ν+1)Z⁴)`. -/
theorem besselDefect_eq (hν : -1 < ν) (hz : 0 < z) :
    besselG ν z * (besselH ν z + 4 / trigamma (ν + 1)) - (1 + besselP ν z) ^ 2
      = 4 * turanDet (ν + 1) ((z / 2) ^ 2)
          / (trigamma (ν + 1) * Zfun (ν + 1) ((z / 2) ^ 2) ^ 4) :=
  besselDet_eq_turanDet hν hz

/-! ### Pointwise Bessel inequality and interpretations -/

/-- **Sharp mixed Bessel--Schur inequality** (`thm:bessel`, `eq:bessel-main`): for
`ν > -1`, `z > 0`,
`G_ν(z)(H_ν(z) + 4/ψ₁(ν+1)) > (1 + P_ν(z))²`.

`eq:D-Delta` (`besselDefect_eq`) rewrites the defect as `4Δ/(gZ⁴)`, and
`turanDet_pos` gives `Δ > 0` for `λ > 0` from `coefficientwise_positivity`: the
degree-zero Maclaurin coefficient of `Δ` vanishes and every higher one is
strictly positive. -/
theorem bessel_schur_ineq (hν : -1 < ν) (hz : 0 < z) :
    (1 + besselP ν z) ^ 2 < besselG ν z * (besselH ν z + 4 / trigamma (ν + 1)) := by
  have ha : 0 < ν + 1 := by linarith
  have hlam : 0 < (z / 2) ^ 2 := by positivity
  have hZ : 0 < Zfun (ν + 1) ((z / 2) ^ 2) := Zfun_pos ha hlam.le
  have hpos : 0 < 4 * turanDet (ν + 1) ((z / 2) ^ 2)
      / (trigamma (ν + 1) * Zfun (ν + 1) ((z / 2) ^ 2) ^ 4) :=
    div_pos (by linarith [turanDet_pos ha hlam])
      (mul_pos (trigamma_pos ha) (pow_pos hZ 4))
  linarith [besselDefect_eq hν hz, hpos]

/-- `G_ν(z) = -∂²_ν log I_ν(z) > 0` for `ν>-1`, `z>0` (order log-convexity of
`I_ν`).  `G = A/Z²`, and both `Afun_pos` (`eq:alpha` termwise positive) and
`Zfun_pos` are proved. -/
theorem besselG_pos (hν : -1 < ν) (hz : 0 < z) : 0 < besselG ν z :=
  besselGfun_pos hν hz

/-- **Positive Bessel--Schur matrix** (`cor:bessel-matrix`): the `2×2` matrix is
positive definite for `ν>-1`, `z>0` — the leading entry from `besselG_pos`, the
determinant from `bessel_schur_ineq`. -/
theorem bessel_schur_matrix_pd (hν : -1 < ν) (hz : 0 < z) :
    SymMat.PD ⟨besselG ν z, 1 + besselP ν z, besselH ν z + 4 / trigamma (ν + 1)⟩ :=
  ⟨besselG_pos hν hz, bessel_schur_ineq hν hz⟩

end BesselSchur

end TuranBessel
