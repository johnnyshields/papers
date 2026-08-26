/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.AlphaCoeff
import TuranBessel.BesselI

/-!
# The Bessel dictionary: `G_ν` from the parameter calculus

`shields-2026-turan-bessel.tex`, «Reciprocal-gamma formulation and positivity phase diagram»
(`sec:main`, `eq:Gnu`) and «Classical scalar Bessel directions» (`sec:scalar`).

`BesselI.log_besselIReal` splits

    log I_ν(x) = ν·log(x/2) + log Z(ν+1, (x/2)²),

so the `ν`-dependence is a term affine in `ν` plus `log Z`.  The affine term dies
under `∂_ν²`, and the shift `ν ↦ ν+1` has derivative `1`, so the `ν`-derivatives of
`log I_ν` are the `a`-derivatives of `log Z` — which `ParameterCalculus` proves.
Hence `eq:Gnu`'s

    G_ν(x) = -∂_ν² log I_ν(x)

is `A/Z²`, with `A = Z_a² - Z Z_aa` the `AlphaCoeff.Afun` whose coefficients are
`eq:alpha`.  `besselG_eq` is that identification, and it is what makes `besselG`
below the paper's object rather than a name: the definition supplies the value, and
`besselG_eq` supplies the fact that the value is `-∂_ν² log I_ν`.

Positivity is then immediate — `Afun_pos` and `Zfun_pos` are both proved — so
`besselG_pos` holds outright.

Sorry-free.
-/

namespace TuranBessel

variable {a lam ν x : ℝ}

/-! ### `a`-derivatives of `log Z` -/

/-- `∂_a Z_a = Z_aa`, in the `Zparam` naming. -/
theorem hasDerivAt_Zparam1 (ha : 0 < a) (lam : ℝ) :
    HasDerivAt (fun y : ℝ => Zparam1 y lam) (Zparam2 a lam) a := by
  have h := hasDerivAt_deriv_Zfun ha lam
  rwa [← Zparam2_eq ha lam] at h

/-- `∂_a Z = Z_a`, in the `Zparam` naming. -/
theorem hasDerivAt_Zfun_param' (ha : 0 < a) (lam : ℝ) :
    HasDerivAt (fun y : ℝ => Zfun y lam) (Zparam1 a lam) a := by
  have h := hasDerivAt_Zfun_param ha lam
  rwa [← Zparam1_eq ha lam] at h

/-- `∂_a log Z = Z_a/Z`. -/
theorem hasDerivAt_log_Zfun (ha : 0 < a) (hlam : 0 ≤ lam) :
    HasDerivAt (fun y : ℝ => Real.log (Zfun y lam)) (Zparam1 a lam / Zfun a lam) a :=
  (hasDerivAt_Zfun_param' ha lam).log (Zfun_pos ha hlam).ne'

/-- `∂_a² log Z = -A/Z²`.  This is `eq:ABC-log`'s `A/Z² = -L_aa`. -/
theorem hasDerivAt_logDeriv_Zfun (ha : 0 < a) (hlam : 0 ≤ lam) :
    HasDerivAt (fun y : ℝ => Zparam1 y lam / Zfun y lam)
      (-(Afun a lam) / Zfun a lam ^ 2) a := by
  refine ((hasDerivAt_Zparam1 ha lam).div (hasDerivAt_Zfun_param' ha lam)
    (Zfun_pos ha hlam).ne').congr_deriv ?_
  rw [Afun]; ring

/-! ### `ν`-derivatives of `log I_ν` -/

/-- `∂_ν log I_ν(x) = log(x/2) + Z_a/Z` at `a = ν+1`, `λ = (x/2)²`. -/
theorem hasDerivAt_log_besselIReal (hν : -1 < ν) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log (besselIReal t x))
      (Real.log (x / 2) + Zparam1 (ν + 1) ((x / 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2)) ν := by
  have ha : 0 < ν + 1 := by linarith
  have hlam : (0:ℝ) ≤ (x / 2) ^ 2 := sq_nonneg _
  have hshift : HasDerivAt (fun t : ℝ => t + 1) 1 ν := (hasDerivAt_id ν).add_const 1
  have hcomp : HasDerivAt (fun t : ℝ => Real.log (Zfun (t + 1) ((x / 2) ^ 2)))
      (Zparam1 (ν + 1) ((x / 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2)) ν := by
    simpa using (hasDerivAt_log_Zfun ha hlam).comp ν hshift
  have haff : HasDerivAt (fun t : ℝ => t * Real.log (x / 2)) (Real.log (x / 2)) ν := by
    simpa using (hasDerivAt_id ν).mul_const (Real.log (x / 2))
  refine (haff.add hcomp).congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hν] with t ht
  exact log_besselIReal ht hx

/-- `∂_ν² log I_ν(x) = -A/Z²`: the affine term of the split has vanished. -/
theorem hasDerivAt_deriv_log_besselIReal (hν : -1 < ν) (hx : 0 < x) :
    HasDerivAt (deriv fun t : ℝ => Real.log (besselIReal t x))
      (-(Afun (ν + 1) ((x / 2) ^ 2)) / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2) ν := by
  have ha : 0 < ν + 1 := by linarith
  have hlam : (0:ℝ) ≤ (x / 2) ^ 2 := sq_nonneg _
  have hshift : HasDerivAt (fun t : ℝ => t + 1) 1 ν := (hasDerivAt_id ν).add_const 1
  have hg : HasDerivAt
      (fun t : ℝ => Zparam1 (t + 1) ((x / 2) ^ 2) / Zfun (t + 1) ((x / 2) ^ 2))
      (-(Afun (ν + 1) ((x / 2) ^ 2)) / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2) ν := by
    simpa using (hasDerivAt_logDeriv_Zfun ha hlam).comp ν hshift
  refine (hg.const_add (Real.log (x / 2))).congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hν] with t ht
  exact (hasDerivAt_log_besselIReal ht hx).deriv

/-! ### `G_ν` -/

/-- `G_ν(x) = A/Z²` at `a = ν+1`, `λ = (x/2)²` (`eq:Gnu`). -/
noncomputable def besselGfun (ν x : ℝ) : ℝ :=
  Afun (ν + 1) ((x / 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2

/-- **`eq:Gnu`.**  `besselGfun` *is* `-∂_ν² log I_ν`, so the definition above names
the paper's object rather than standing in for it. -/
theorem besselGfun_eq (hν : -1 < ν) (hx : 0 < x) :
    besselGfun ν x = -deriv (deriv fun t : ℝ => Real.log (besselIReal t x)) ν := by
  rw [(hasDerivAt_deriv_log_besselIReal hν hx).deriv, besselGfun]
  ring

/-- `G_ν(x) > 0` for `ν > -1`, `x > 0` — the order log-convexity of `I_ν`.  Both
factors are already proved: `Afun_pos` is `eq:alpha` termwise positive, and
`Zfun_pos` is the reciprocal-gamma series. -/
theorem besselGfun_pos (hν : -1 < ν) (hx : 0 < x) : 0 < besselGfun ν x := by
  have ha : 0 < ν + 1 := by linarith
  exact div_pos (Afun_pos ha (sq_nonneg _)) (pow_pos (Zfun_pos ha (sq_nonneg _)) 2)

end TuranBessel
