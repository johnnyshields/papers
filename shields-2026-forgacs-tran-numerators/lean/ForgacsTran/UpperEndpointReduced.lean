/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchEndpoint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The branch equation at the `r = 1` upper endpoint, with its degeneracy divided out

`FTBranchEndpoint`'s `ftPencilIm P r τ θ = Im(e^{irθ}P(τe^{-iθ}))` vanishes exactly where the
branch's spectral value is real, and at `θ = 0` it vanishes **identically in `τ`** — which is
why the lower endpoint is read through `ftPencilImDeriv` rather than through `ftPencilIm`.

At `r = 1` the same thing happens at the *other* end.  There `θ = π`, and
`e^{iπ}P(τe^{-iπ}) = -P(-τ)` is real for every `τ`, so `ftPencilIm P 1 τ π = 0` identically and
the branch equation carries no information at the endpoint at all.  Both partials vanish there,
so the implicit function theorem that settles the `2 ≤ r` upper endpoint
(`scripts/check_upper_endpoint_branch_slope.py`, where `∂G/∂τ = -\sin(π/r)\sum_k 1/a_k`) has
nothing to apply to: that constant is `0` at `r = 1`.

**What replaces it is an exact factorization.**  Writing `θ = π + φ` and expanding by
coefficients,

    ftPencilIm P 1 τ (π + φ) = ∑_j p_j(-1)^{j+1}τ^j \sin((1-j)φ),

and every term carries a factor `φ`.  `ftUpperReduced` is that sum with the factor divided out
through `Real.sinc`, so it is defined at `φ = 0` rather than extended to it, and

* `ftUpperReduced P τ 0 = E(-τ)`, `E = XP' - P`, so the endpoint equation is the vanishing of
  the critical polynomial at the collision — the same `E(-L) = 0` that
  `FTBranchEndpointUpper.exists_tendsto_ftTau_nhdsLT_pi` produces and
  `EndpointUpperOneBinders.sum_div_add_eq_of_eval_ftCriticalReal_neg` reads as
  `∑_k L/(a_k + L) = r`;
* the reduced equation is **not** degenerate in `τ` there, because `-L` is a *simple* zero of
  `E` (`EndpointUpperOneBinders.rootMultiplicity_ftCritical_endpoint_pi_eq_one`), which is what
  `\sin(π/r)` supplies at `2 ≤ r`;
* `ftUpperReduced` is **even in `φ`**, since `Real.sinc` is.  That is the reason `τ'(π⁻) = 0`
  rather than a computation about it: the branch and its conjugate meet at `-L`, so the radius
  is even about `π`, and the endpoint's whole content sits in `τ''`.

`scripts/check_r_one_upper_endpoint_regularity.py` measures all three at `a = (1,1,3)`,
`a = (1,1,1)` and `a = (1,2,4)`.

Sorry-free.

## Main statements

* `ftPencilIm_pi_add` — the factorization, exactly.
* `ftUpperReduced_zero` — the reduced equation at the endpoint is `E(-τ)`.
* `ftUpperReduced_neg` — evenness in `φ`.
* `continuous_ftUpperReduced` — joint continuity in `(τ, φ)`.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`, `sec:geometry`, `eq:ab-def`,
`lem:principal-endpoint-regularity`.

## Tags

upper endpoint, branch equation, sinc, even function, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

/-- `\sin x = x\,\operatorname{sinc} x`, at every `x` including `0`. -/
theorem sin_eq_mul_sinc (x : ℝ) : Real.sin x = x * Real.sinc x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.sinc_of_ne_zero hx]; field_simp

/-- **The branch equation at the `r = 1` upper endpoint, with the factor `φ` divided out.**
The `j`-th coefficient contributes `\sin((1-j)φ)`, which is `(1-j)φ` times a `sinc`; this is
that sum with the `φ` removed, so it is *defined* at `φ = 0`. -/
noncomputable def ftUpperReduced (P : Polynomial ℝ) (τ φ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * (-1) ^ (j + 1) * τ ^ j * ((1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * φ))

/-- The coefficient expansion of `ftPencilIm` at `r = 1`, in the chart `θ = π + φ`. -/
private theorem ftPencilIm_pi_add_sum (P : Polynomial ℝ) (τ φ : ℝ) :
    ftPencilIm P 1 τ (π + φ)
      = ∑ j ∈ Finset.range (P.natDegree + 1),
        P.coeff j * (-1) ^ (j + 1) * τ ^ j * Real.sin ((1 - (j : ℝ)) * φ) := by
  classical
  set Q : Polynomial ℂ := P.map (algebraMap ℝ ℂ) with hQ
  have hdeg : Q.natDegree = P.natDegree := by
    rw [hQ, natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
  have hco : ∀ j, Q.coeff j = ((P.coeff j : ℝ) : ℂ) := fun j => by
    rw [hQ, coeff_map]; rfl
  have hev : Q.eval (ftArcPoint τ (π + φ))
      = ∑ j ∈ Finset.range (P.natDegree + 1),
        ((P.coeff j : ℝ) : ℂ) * (ftArcPoint τ (π + φ)) ^ j := by
    rw [Polynomial.eval_eq_sum_range, hdeg]
    exact Finset.sum_congr rfl fun j _ => by rw [hco]
  rw [ftPencilIm, ← hQ, hev, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- each term is a real multiple of `exp(i(1-j)(π + φ))`
  have key : Complex.exp ((((1 : ℕ) : ℝ) * (π + φ) : ℝ) * Complex.I)
      * Complex.exp ((j : ℂ) * (-((π + φ : ℝ) : ℂ) * Complex.I))
      = Complex.exp ((((1 - (j : ℝ)) * (π + φ) : ℝ)) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hterm : Complex.exp ((((1 : ℕ) : ℝ) * (π + φ) : ℝ) * Complex.I)
        * (((P.coeff j : ℝ) : ℂ) * (ftArcPoint τ (π + φ)) ^ j)
      = ((P.coeff j * τ ^ j : ℝ) : ℂ)
        * Complex.exp ((((1 - (j : ℝ)) * (π + φ) : ℝ)) * Complex.I) := by
    rw [ftArcPoint, mul_pow, ← Complex.exp_nat_mul,
      show ((P.coeff j * τ ^ j : ℝ) : ℂ) = ((P.coeff j : ℝ) : ℂ) * ((τ : ℝ) : ℂ) ^ j from by
        push_cast; ring]
    linear_combination ((P.coeff j : ℝ) : ℂ) * (((τ : ℝ) : ℂ) ^ j) * key
  rw [hterm]
  have him : ∀ u ψ : ℝ, (((u : ℝ) : ℂ) * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)).im
      = u * Real.sin ψ := by
    intro u ψ
    have hsplit : (((u : ℝ) : ℂ) * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)).im
        = u * (Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)).im := by
      simp [Complex.mul_im]
    rw [hsplit, Complex.exp_ofReal_mul_I_im]
  rw [him]
  -- `sin((1-j)(π + φ)) = (-1)^{j+1} sin((1-j)φ)`
  have hsplit : (1 - (j : ℝ)) * (π + φ)
      = (1 - (j : ℝ)) * φ + ((1 - (j : ℤ) : ℤ) : ℝ) * π := by push_cast; ring
  rw [hsplit, Real.sin_add_int_mul_pi]
  have hne : (-1 : ℝ) ≠ 0 := by norm_num
  have hsq : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨j, by ring⟩
  have hinv : ((-1 : ℝ) ^ j)⁻¹ = (-1 : ℝ) ^ j := inv_eq_of_mul_eq_one_right hsq
  have hpow : ((-1 : ℝ) ^ ((1 : ℤ) - (j : ℤ))) = (-1 : ℝ) ^ (j + 1) := by
    rw [zpow_sub₀ hne, zpow_one, zpow_natCast, div_eq_mul_inv, hinv, pow_succ]
    ring
  rw [hpow]
  ring

/-- **The factorization.**  `ftPencilIm P 1 τ (π + φ) = φ · ftUpperReduced P τ φ`, exactly and
at every `(τ, φ)`.  The branch equation's degeneracy at `θ = π` is the factor `φ`, and what is
left is `ftUpperReduced`. -/
theorem ftPencilIm_pi_add (P : Polynomial ℝ) (τ φ : ℝ) :
    ftPencilIm P 1 τ (π + φ) = φ * ftUpperReduced P τ φ := by
  rw [ftPencilIm_pi_add_sum, ftUpperReduced, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (1 - (j : ℝ)) * φ = φ * (1 - (j : ℝ)) from by ring, sin_eq_mul_sinc]
  rw [show φ * (1 - (j : ℝ)) = (1 - (j : ℝ)) * φ from by ring]
  ring

/-- The coefficients of `E = XP' - rP` are `(j - r)` times those of `P`. -/
theorem coeff_ftCriticalReal (P : Polynomial ℝ) (r j : ℕ) :
    (ftCriticalReal P r).coeff j = ((j : ℝ) - r) * P.coeff j := by
  rcases j with _ | j
  · simp [ftCriticalReal]
  · simp [ftCriticalReal, coeff_X_mul, coeff_derivative]
    ring

/-- `E` is no wider than `P` shifted by one, which is all the range the sum below needs. -/
theorem natDegree_ftCriticalReal_lt (P : Polynomial ℝ) (r : ℕ) :
    (ftCriticalReal P r).natDegree < P.natDegree + 2 := by
  refine Nat.lt_succ_of_le (le_trans (natDegree_sub_le _ _) (max_le ?_ ?_))
  · refine le_trans natDegree_mul_le ?_
    have h := natDegree_derivative_le P
    simp only [natDegree_X]
    omega
  · exact le_trans (natDegree_C_mul_le _ _) (by omega)

/-- **The reduced equation at the endpoint is the critical polynomial at the collision.**
`E = XP' - P` at `r = 1`, evaluated at `-τ`: so the endpoint value `L` is picked out by
`E(-L) = 0`, which is `EndpointUpperOneBinders`' deficit equation `∑_k L/(a_k + L) = r`. -/
theorem ftUpperReduced_zero (P : Polynomial ℝ) (τ : ℝ) :
    ftUpperReduced P τ 0 = (ftCriticalReal P 1).eval (-τ) := by
  classical
  rw [Polynomial.eval_eq_sum_range' (natDegree_ftCriticalReal_lt P 1),
    Finset.sum_range_succ]
  have hlast : (ftCriticalReal P 1).coeff (P.natDegree + 1) * (-τ) ^ (P.natDegree + 1) = 0 := by
    rw [coeff_ftCriticalReal, coeff_eq_zero_of_natDegree_lt (by omega)]
    ring
  rw [hlast, add_zero, ftUpperReduced]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_ftCriticalReal]
  simp only [mul_zero, Real.sinc_zero, mul_one, Nat.cast_one]
  rw [neg_pow]
  ring

/-- **`ftUpperReduced` is even in `φ`.**  Every term is a `sinc`, and `Real.sinc` is even.
This is why the branch radius has zero slope at the `r = 1` upper endpoint: the branch and its
conjugate meet at `-L`, so `τ` is even about `π`, and the endpoint's content is in `τ''`. -/
theorem ftUpperReduced_neg (P : Polynomial ℝ) (τ φ : ℝ) :
    ftUpperReduced P τ (-φ) = ftUpperReduced P τ φ := by
  rw [ftUpperReduced, ftUpperReduced]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (1 - (j : ℝ)) * -φ = -((1 - (j : ℝ)) * φ) from by ring, Real.sinc_neg]

/-- The factorization read the other way: `ftPencilIm` vanishes at `π` for every radius, so
the `r = 1` upper endpoint carries no information until the factor is divided out. -/
@[simp] theorem ftPencilIm_pi (P : Polynomial ℝ) (τ : ℝ) : ftPencilIm P 1 τ π = 0 := by
  have h := ftPencilIm_pi_add P τ 0
  rw [add_zero] at h
  rw [h, zero_mul]

/-- **Joint continuity**, which is what carries the endpoint's non-degeneracy along the arc. -/
theorem continuous_ftUpperReduced (P : Polynomial ℝ) :
    Continuous fun p : ℝ × ℝ => ftUpperReduced P p.1 p.2 := by
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_const.mul ((continuous_fst).pow j)).mul
    (continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_snd))))

/-! ### The quadratic rate, from evenness

`ftUpperReduced` is even in `φ`, so its `φ`-derivative vanishes at `0` and the difference from
the endpoint value is quadratic.  Nothing here needs that derivative: `Real.sinc` is within
`x^2/6` of `1`, which is `\sin x = x - x^3/6 + \dots` and no more, and the sum inherits it
termwise.  This is what turns `H(τ(θ), θ - π) = 0` into `|τ(θ) - L| = O((π - θ)^2)` once the
simple zero of `E` supplies the lower bound on the other side. -/

/-- `|\sin x - x| ≤ |x|^3/6`, from Mathlib's two one-sided bounds. -/
theorem abs_sin_sub_self_le (x : ℝ) : |Real.sin x - x| ≤ |x| ^ 3 / 6 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hx' : 0 < -x := by linarith
    have h1 := Real.sin_lt hx'
    have h2 := Real.sin_gt_sub_cube hx'
    rw [Real.sin_neg] at h1 h2
    rw [abs_of_neg hx]
    rw [abs_le]
    constructor <;> nlinarith
  · simp
  · have h1 := Real.sin_lt hx
    have h2 := Real.sin_gt_sub_cube hx
    rw [abs_of_pos hx, abs_le]
    constructor <;> nlinarith

/-- `|\operatorname{sinc} x - 1| ≤ x^2/6`, at every `x` including `0`. -/
theorem abs_sinc_sub_one_le (x : ℝ) : |Real.sinc x - 1| ≤ x ^ 2 / 6 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.sinc_of_ne_zero hx]
    have hx0 : |x| ≠ 0 := abs_ne_zero.2 hx
    have hkey : |Real.sin x / x - 1| = |Real.sin x - x| / |x| := by
      rw [← abs_div]
      congr 1
      field_simp
    rw [hkey, div_le_iff₀ (abs_pos.2 hx)]
    have h := abs_sin_sub_self_le x
    have hsq : |x| ^ 3 / 6 = x ^ 2 / 6 * |x| := by
      rw [← sq_abs x]; ring
    linarith [hsq ▸ h]

/-- The constant the quadratic rate is measured with: the coefficient sum at radius `T`. -/
noncomputable def ftUpperReducedBound (P : Polynomial ℝ) (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j| * T ^ j * |1 - (j : ℝ)| ^ 3 / 6

/-- **The endpoint value is approached quadratically.**  `ftUpperReduced` is even in `φ`, so
the difference from `φ = 0` is `O(φ^2)`, with a constant that depends on the pencil and on a
bound for the radius alone. -/
theorem abs_ftUpperReduced_sub_zero_le (P : Polynomial ℝ) {τ T : ℝ} (φ : ℝ)
    (hτ : |τ| ≤ T) :
    |ftUpperReduced P τ φ - ftUpperReduced P τ 0| ≤ ftUpperReducedBound P T * φ ^ 2 := by
  have hT0 : 0 ≤ T := le_trans (abs_nonneg τ) hτ
  rw [ftUpperReduced, ftUpperReduced, ← Finset.sum_sub_distrib, ftUpperReducedBound,
    Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  simp only [mul_zero, Real.sinc_zero, mul_one]
  have hrw : P.coeff j * (-1) ^ (j + 1) * τ ^ j * ((1 - (j : ℝ))
        * Real.sinc ((1 - (j : ℝ)) * φ))
      - P.coeff j * (-1) ^ (j + 1) * τ ^ j * (1 - (j : ℝ))
      = P.coeff j * (-1) ^ (j + 1) * τ ^ j * (1 - (j : ℝ))
        * (Real.sinc ((1 - (j : ℝ)) * φ) - 1) := by ring
  rw [hrw, abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_pow]
  have hsinc := abs_sinc_sub_one_le ((1 - (j : ℝ)) * φ)
  have hτj : |τ| ^ j ≤ T ^ j := pow_le_pow_left₀ (abs_nonneg τ) hτ j
  have hstep : |P.coeff j| * |τ| ^ j * |1 - (j : ℝ)|
      * |Real.sinc ((1 - (j : ℝ)) * φ) - 1|
      ≤ |P.coeff j| * T ^ j * |1 - (j : ℝ)| * (((1 - (j : ℝ)) * φ) ^ 2 / 6) := by
    refine mul_le_mul ?_ hsinc (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hτj (abs_nonneg _)) (abs_nonneg _)
  refine le_trans hstep (le_of_eq ?_)
  have habs : |1 - (j : ℝ)| ^ 3 = |1 - (j : ℝ)| * (1 - (j : ℝ)) ^ 2 := by
    rw [← sq_abs (1 - (j : ℝ))]; ring
  rw [habs]
  ring

end ForgacsTran
