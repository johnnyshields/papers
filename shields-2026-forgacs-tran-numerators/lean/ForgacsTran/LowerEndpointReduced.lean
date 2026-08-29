/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.UpperEndpointSlope

/-!
# The branch equation at the LOWER endpoint, with its degeneracy divided out

`FTBranchEndpoint.ftPencilIm_zero` records that the branch equation vanishes identically in
`τ` at `θ = 0`, at **every** `r` — which is why the lower endpoint is read through
`ftPencilImDeriv` rather than through `ftPencilIm`.  `UpperEndpointReduced` divides that
degeneracy out at the `r = 1` upper end; this module does the same at the lower end, where
the arithmetic is simpler because no shift is involved:

    ftPencilIm P r τ θ = ∑_j p_j τ^j \sin((r-j)θ),

so every term carries a factor `θ`, and `ftLowerReduced` is that sum with the factor divided
out through `Real.sinc`.  Then

* `ftLowerReduced P r τ 0 = -E(τ)`, `E = XP' - rP`, so the endpoint value is a zero of the
  critical polynomial — which is `FTBranchEndpoint`'s `ftPencilImDeriv_zero` in the form the
  rate arguments consume;
* `ftLowerReduced` is **even in `θ`**, since `Real.sinc` is.

**Evenness alone does not make the endpoint quadratic.**  The rate needs the zero of `E` to
be *simple*, and at a smallest zero of multiplicity `ρ` it has multiplicity `ρ - 1`.  So the
quadratic rate holds at `ρ = 1` and at `ρ = 2` and fails from `ρ = 3` on, which is exactly
where the cluster expansion's slope `-x₁\cot(π/ρ)` stops vanishing.  The two accounts agree,
and that agreement is the check on both.

Sorry-free.

## Main statements

* `ftPencilIm_eq_mul_ftLowerReduced` — the factorization, exactly.
* `ftLowerReduced_zero`, `ftLowerReduced_neg` — the endpoint value and evenness.
* `abs_ftLowerReduced_sub_zero_le` — the quadratic rate of the equation itself.
* `hasDerivAt_ftLowerReduced_along` — differentiated along the branch.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`, `sec:geometry`, `eq:ab-def`,
`lem:principal-endpoint-regularity`.

## Tags

lower endpoint, branch equation, sinc, even function, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

/-- **The branch equation at the lower endpoint, with the factor `θ` divided out.** -/
noncomputable def ftLowerReduced (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * τ ^ j * (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * θ))

/-- The coefficient expansion of `ftPencilIm`. -/
theorem ftPencilIm_eq_sum (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) :
    ftPencilIm P r τ θ
      = ∑ j ∈ Finset.range (P.natDegree + 1),
        P.coeff j * τ ^ j * Real.sin (((r : ℝ) - j) * θ) := by
  classical
  set Q : Polynomial ℂ := P.map (algebraMap ℝ ℂ) with hQ
  have hdeg : Q.natDegree = P.natDegree := by
    rw [hQ, natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
  have hco : ∀ j, Q.coeff j = ((P.coeff j : ℝ) : ℂ) := fun j => by
    rw [hQ, coeff_map]; rfl
  have hev : Q.eval (ftArcPoint τ θ)
      = ∑ j ∈ Finset.range (P.natDegree + 1),
        ((P.coeff j : ℝ) : ℂ) * (ftArcPoint τ θ) ^ j := by
    rw [Polynomial.eval_eq_sum_range, hdeg]
    exact Finset.sum_congr rfl fun j _ => by rw [hco]
  rw [ftPencilIm, ← hQ, hev, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have key : Complex.exp ((((r : ℕ) : ℝ) * θ : ℝ) * Complex.I)
      * Complex.exp ((j : ℂ) * (-((θ : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((((r : ℝ) - j) * θ : ℝ)) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hterm : Complex.exp ((((r : ℕ) : ℝ) * θ : ℝ) * Complex.I)
        * (((P.coeff j : ℝ) : ℂ) * (ftArcPoint τ θ) ^ j)
      = ((P.coeff j * τ ^ j : ℝ) : ℂ)
        * Complex.exp (((((r : ℝ) - j) * θ : ℝ)) * Complex.I) := by
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

/-- **The factorization.**  `ftPencilIm P r τ θ = θ · ftLowerReduced P r τ θ`, exactly and at
every `(τ, θ)`. -/
theorem ftPencilIm_eq_mul_ftLowerReduced (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) :
    ftPencilIm P r τ θ = θ * ftLowerReduced P r τ θ := by
  rw [ftPencilIm_eq_sum, ftLowerReduced, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((r : ℝ) - j) * θ = θ * ((r : ℝ) - j) from by ring, sin_eq_mul_sinc,
    show θ * ((r : ℝ) - j) = ((r : ℝ) - j) * θ from by ring]
  ring

/-- **The reduced equation at the endpoint is `-E(τ)`.** -/
theorem ftLowerReduced_zero (P : Polynomial ℝ) (r : ℕ) (τ : ℝ) :
    ftLowerReduced P r τ 0 = -((ftCriticalReal P r).eval τ) := by
  classical
  rw [Polynomial.eval_eq_sum_range' (natDegree_ftCriticalReal_lt P r), Finset.sum_range_succ]
  have hlast : (ftCriticalReal P r).coeff (P.natDegree + 1) * τ ^ (P.natDegree + 1) = 0 := by
    rw [coeff_ftCriticalReal, coeff_eq_zero_of_natDegree_lt (by omega)]
    ring
  rw [hlast, add_zero, ftLowerReduced, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_ftCriticalReal]
  simp only [mul_zero, Real.sinc_zero, mul_one]
  ring

/-- **`ftLowerReduced` is even in `θ`.**  Every term is a `sinc`, and `Real.sinc` is even. -/
theorem ftLowerReduced_neg (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) :
    ftLowerReduced P r τ (-θ) = ftLowerReduced P r τ θ := by
  rw [ftLowerReduced, ftLowerReduced]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((r : ℝ) - j) * -θ = -(((r : ℝ) - j) * θ) from by ring, Real.sinc_neg]

/-- The constant the rates below are measured with. -/
noncomputable def ftLowerReducedBound (P : Polynomial ℝ) (r : ℕ) (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j| * T ^ j * |(r : ℝ) - j| ^ 3 / 6

/-- **The endpoint value is approached quadratically.** -/
theorem abs_ftLowerReduced_sub_zero_le (P : Polynomial ℝ) (r : ℕ) {τ T : ℝ} (θ : ℝ)
    (hτ : |τ| ≤ T) :
    |ftLowerReduced P r τ θ - ftLowerReduced P r τ 0| ≤ ftLowerReducedBound P r T * θ ^ 2 := by
  have hT0 : 0 ≤ T := le_trans (abs_nonneg τ) hτ
  rw [ftLowerReduced, ftLowerReduced, ← Finset.sum_sub_distrib, ftLowerReducedBound,
    Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  simp only [mul_zero, Real.sinc_zero, mul_one]
  have hrw : P.coeff j * τ ^ j * (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * θ))
      - P.coeff j * τ ^ j * ((r : ℝ) - j)
      = P.coeff j * τ ^ j * ((r : ℝ) - j) * (Real.sinc (((r : ℝ) - j) * θ) - 1) := by ring
  rw [hrw, abs_mul, abs_mul, abs_mul, abs_pow]
  have hτj : |τ| ^ j ≤ T ^ j := pow_le_pow_left₀ (abs_nonneg τ) hτ j
  have hsinc := abs_sinc_sub_one_le (((r : ℝ) - j) * θ)
  have hstep : |P.coeff j| * |τ| ^ j * |(r : ℝ) - j| * |Real.sinc (((r : ℝ) - j) * θ) - 1|
      ≤ |P.coeff j| * T ^ j * |(r : ℝ) - j| * ((((r : ℝ) - j) * θ) ^ 2 / 6) := by
    refine mul_le_mul ?_ hsinc (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hτj (abs_nonneg _)) (abs_nonneg _)
  refine le_trans hstep (le_of_eq ?_)
  have habs : |(r : ℝ) - j| ^ 3 = |(r : ℝ) - j| * ((r : ℝ) - j) ^ 2 := by
    rw [← sq_abs ((r : ℝ) - j)]; ring
  rw [habs]
  ring

/-! ### The two partials -/

/-- The radial partial of `ftLowerReduced`. -/
noncomputable def ftLowerReducedRadial (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * ((j : ℝ) * τ ^ (j - 1))
      * (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * θ))

/-- The angular partial of `ftLowerReduced`. -/
noncomputable def ftLowerReducedSlope (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * τ ^ j
      * (((r : ℝ) - j) * (((r : ℝ) - j) * sincDeriv (((r : ℝ) - j) * θ)))

/-- **The reduced equation differentiated along the branch.** -/
theorem hasDerivAt_ftLowerReduced_along (P : Polynomial ℝ) (r : ℕ) {T : ℝ → ℝ} {dT θ : ℝ}
    (hT : HasDerivAt T dT θ) (hθ : θ ≠ 0) :
    HasDerivAt (fun t : ℝ => ftLowerReduced P r (T t) t)
      (ftLowerReducedRadial P r (T θ) θ * dT + ftLowerReducedSlope P r (T θ) θ) θ := by
  have hterm : ∀ j ∈ Finset.range (P.natDegree + 1),
      HasDerivAt (fun t : ℝ => P.coeff j * T t ^ j
          * (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * (t - 0))))
        (P.coeff j * ((j : ℝ) * T θ ^ (j - 1))
            * (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * (θ - 0))) * dT
          + P.coeff j * T θ ^ j
            * (((r : ℝ) - j) * (((r : ℝ) - j) * sincDeriv (((r : ℝ) - j) * (θ - 0))))) θ := by
    intro j _
    have hpow : HasDerivAt (fun t : ℝ => P.coeff j * T t ^ j)
        (P.coeff j * ((j : ℝ) * T θ ^ (j - 1) * dT)) θ := (hT.pow j).const_mul _
    have hs : HasDerivAt
        (fun t : ℝ => ((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * (t - 0)))
        (((r : ℝ) - j) * (((r : ℝ) - j) * sincDeriv (((r : ℝ) - j) * (θ - 0)))) θ :=
      (hasDerivAt_sinc_mul_sub ((r : ℝ) - j) 0 hθ).const_mul _
    have h := hpow.mul hs
    refine h.congr_deriv ?_
    ring
  have hsum := HasDerivAt.fun_sum hterm
  have hfun : (fun t : ℝ => ∑ j ∈ Finset.range (P.natDegree + 1),
      P.coeff j * T t ^ j * (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * (t - 0))))
      = fun t : ℝ => ftLowerReduced P r (T t) t := by
    funext t
    rw [ftLowerReduced]
    exact Finset.sum_congr rfl fun j _ => by rw [sub_zero]
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  rw [ftLowerReducedRadial, ftLowerReducedSlope, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [sub_zero]

/-- The radial partial is the `τ`-derivative of the endpoint equation. -/
theorem hasDerivAt_ftLowerReduced_radial (P : Polynomial ℝ) (r : ℕ) (τ : ℝ) :
    HasDerivAt (fun x : ℝ => ftLowerReduced P r x 0) (ftLowerReducedRadial P r τ 0) τ := by
  have hterm : ∀ j ∈ Finset.range (P.natDegree + 1),
      HasDerivAt (fun x : ℝ => P.coeff j * x ^ j
          * (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * 0)))
        (P.coeff j * ((j : ℝ) * τ ^ (j - 1))
          * (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * 0))) τ := by
    intro j _
    have h := ((hasDerivAt_pow j τ).const_mul (P.coeff j)).mul_const
      (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * 0))
    refine h.congr_deriv ?_
    ring
  have hsum := HasDerivAt.fun_sum hterm
  have hfun : (fun x : ℝ => ∑ j ∈ Finset.range (P.natDegree + 1),
      P.coeff j * x ^ j * (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * 0)))
      = fun x : ℝ => ftLowerReduced P r x 0 := rfl
  rw [hfun] at hsum
  exact hsum

/-- **The radial partial at the endpoint is `-E'(τ)`**, so it is nonzero at the collision
exactly when the zero of `E` is simple. -/
theorem ftLowerReducedRadial_zero (P : Polynomial ℝ) (r : ℕ) (τ : ℝ) :
    ftLowerReducedRadial P r τ 0 = -((derivative (ftCriticalReal P r)).eval τ) := by
  have h1 := hasDerivAt_ftLowerReduced_radial P r τ
  have hfun : (fun x : ℝ => ftLowerReduced P r x 0)
      = fun x : ℝ => -((ftCriticalReal P r).eval x) :=
    funext fun x => ftLowerReduced_zero P r x
  rw [hfun] at h1
  exact h1.unique (((ftCriticalReal P r).hasDerivAt τ).neg)

/-- The radial partial is continuous along any pair of limits. -/
theorem tendsto_ftLowerReducedRadial (P : Polynomial ℝ) (r : ℕ) {ι : Type*} {F : Filter ι}
    {T φ : ι → ℝ} {L : ℝ} (hT : Tendsto T F (𝓝 L)) (hφ : Tendsto φ F (𝓝 0)) :
    Tendsto (fun i => ftLowerReducedRadial P r (T i) (φ i)) F
      (𝓝 (ftLowerReducedRadial P r L 0)) := by
  simp only [ftLowerReducedRadial]
  refine tendsto_finsetSum _ fun j _ => ?_
  have h1 : Tendsto (fun i => P.coeff j * ((j : ℝ) * T i ^ (j - 1))) F
      (𝓝 (P.coeff j * ((j : ℝ) * L ^ (j - 1)))) := ((hT.pow (j - 1)).const_mul _).const_mul _
  have h2 : Tendsto (fun i => ((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * φ i)) F
      (𝓝 (((r : ℝ) - j) * Real.sinc (((r : ℝ) - j) * 0))) :=
    (((Real.continuous_sinc.tendsto (((r : ℝ) - j) * 0)).comp
      (hφ.const_mul ((r : ℝ) - j))).const_mul _)
  exact h1.mul h2

/-- **The angular partial is `O(θ)`**, with the same constant. -/
theorem abs_ftLowerReducedSlope_le (P : Polynomial ℝ) (r : ℕ) {τ T : ℝ} (θ : ℝ)
    (hτ : |τ| ≤ T) :
    |ftLowerReducedSlope P r τ θ| ≤ 3 * ftLowerReducedBound P r T * |θ| := by
  have hT0 : 0 ≤ T := le_trans (abs_nonneg τ) hτ
  rw [ftLowerReducedSlope, ftLowerReducedBound, Finset.mul_sum, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_mul, abs_mul]
  have hτj : |τ| ^ j ≤ T ^ j := pow_le_pow_left₀ (abs_nonneg τ) hτ j
  have hsinc := abs_sincDeriv_le (((r : ℝ) - j) * θ)
  rw [abs_mul] at hsinc
  have hstep : |P.coeff j| * |τ| ^ j * (|(r : ℝ) - j|
        * (|(r : ℝ) - j| * |sincDeriv (((r : ℝ) - j) * θ)|))
      ≤ |P.coeff j| * T ^ j * (|(r : ℝ) - j|
        * (|(r : ℝ) - j| * (|(r : ℝ) - j| * |θ| / 2))) := by
    have h1 : |P.coeff j| * |τ| ^ j ≤ |P.coeff j| * T ^ j :=
      mul_le_mul_of_nonneg_left hτj (abs_nonneg _)
    have h2 : |(r : ℝ) - j| * (|(r : ℝ) - j| * |sincDeriv (((r : ℝ) - j) * θ)|)
        ≤ |(r : ℝ) - j| * (|(r : ℝ) - j| * (|(r : ℝ) - j| * |θ| / 2)) := by
      have h := mul_le_mul_of_nonneg_left hsinc (abs_nonneg ((r : ℝ) - j))
      exact mul_le_mul_of_nonneg_left h (abs_nonneg ((r : ℝ) - j))
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  have habs : |(r : ℝ) - j| ^ 3 = |(r : ℝ) - j| * (|(r : ℝ) - j| * |(r : ℝ) - j|) := by ring
  rw [habs]
  ring

theorem ftLowerReducedBound_nonneg (P : Polynomial ℝ) (r : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ ftLowerReducedBound P r T := by
  rw [ftLowerReducedBound]
  exact Finset.sum_nonneg fun j _ => by positivity

end ForgacsTran
