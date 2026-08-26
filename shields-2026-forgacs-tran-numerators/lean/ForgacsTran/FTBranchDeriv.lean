/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchAngle

/-!
# The `θ`-derivative of a branch angle

At fixed `τ`, each angle `θ_k` of `Forgacs2017RationalDenominator` Lemma 2 is an
explicit elementary function of `θ`, and

`dθ_k/dθ = sin θ_k cos (θ_k - θ) / sin θ`,

which is the quantity summed in their (15).

## Main statements

* `hasDerivAt_ftArccot` — the derivative of the inverse cotangent.
* `hasDerivAt_ftAngle` — the displayed formula.
* `hasDerivAt_ftAngleSum` — its sum over `k`.

## Implementation notes

**Differs from the paper's route.**  The paper obtains this derivative by
logarithmic differentiation of `∏_k (τ_k - t₀ e^{2iθ}) = e^{2irθ} ∏_k (τ_k - t₀)`
and then eliminates `dτ`; here `τ` is held fixed and the closed form of
`FTBranchAngle` is differentiated directly, so no implicit relation is
differentiated and the result is the partial derivative their (14) isolates.

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

branch angle, derivative, angle system
-/

namespace ForgacsTran

open Real Set

theorem hasDerivAt_ftArccot (x : ℝ) : HasDerivAt ftArccot (-(1 / (1 + x ^ 2))) x := by
  have h : HasDerivAt (fun t : ℝ => π / 2 - Real.arctan t) (0 - 1 / (1 + x ^ 2)) x :=
    (hasDerivAt_const x (π / 2)).sub (Real.hasDerivAt_arctan x)
  rw [zero_sub] at h
  exact h

/-- **`Forgacs2017RationalDenominator` (14)–(15), the summand.** -/
theorem hasDerivAt_ftAngle {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) :
    HasDerivAt (fun t => ftAngle a τ t)
      (Real.sin (ftAngle a τ s) * Real.cos (ftAngle a τ s - s) / Real.sin s) s := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  have hsin' : Real.sin s ≠ 0 := hsin.ne'
  have hτ' : τ ≠ 0 := hτ.ne'
  have hymem := ftAngle_mem_Ioo ha hτ hs
  have hsy : 0 < Real.sin (ftAngle a τ s) :=
    sin_pos_of_pos_of_lt_pi (lt_trans hs.1 hymem.1) hymem.2
  set y := ftAngle a τ s with hy
  set g : ℝ → ℝ := fun t => Real.cos t / Real.sin t - a / (τ * Real.sin t) with hgdef
  have hgs : Real.cos y = g s * Real.sin y := cos_ftArccot _
  have hspec : a * Real.sin y = τ * Real.sin (y - s) := ftAngle_spec hτ' hs
  have hgval : g s = Real.cos y / Real.sin y := by
    rw [eq_div_iff hsy.ne']
    exact hgs.symm
  have hone : 1 + g s ^ 2 = 1 / Real.sin y ^ 2 := by
    rw [hgval]
    field_simp
    linear_combination (Real.sin_sq_add_cos_sq y)
  have hkey : Real.sin y * (τ - a * Real.cos s) = τ * Real.sin s * Real.cos (y - s) := by
    rw [Real.cos_sub]
    rw [Real.sin_sub] at hspec
    linear_combination (-Real.cos s) * hspec + (-(τ * Real.sin y)) * (Real.sin_sq_add_cos_sq s)
  have hden : τ * Real.sin s ≠ 0 := mul_ne_zero hτ' hsin'
  have h1 : HasDerivAt (fun t => Real.cos t / Real.sin t)
      ((-Real.sin s * Real.sin s - Real.cos s * Real.cos s) / Real.sin s ^ 2) s :=
    (Real.hasDerivAt_cos s).div (Real.hasDerivAt_sin s) hsin'
  have h2 : HasDerivAt (fun t => a / (τ * Real.sin t))
      ((0 * (τ * Real.sin s) - a * (τ * Real.cos s)) / (τ * Real.sin s) ^ 2) s :=
    (hasDerivAt_const s a).div ((Real.hasDerivAt_sin s).const_mul τ) hden
  have hcomp := (hasDerivAt_ftArccot (g s)).comp s (h1.sub h2)
  have hfun : (ftArccot ∘ g) = fun t => ftAngle a τ t := rfl
  rw [hfun] at hcomp
  refine hcomp.congr_deriv ?_
  have hA : (-Real.sin s * Real.sin s - Real.cos s * Real.cos s) / Real.sin s ^ 2
      = -(1 / Real.sin s ^ 2) := by
    field_simp
    linear_combination -(Real.sin_sq_add_cos_sq s)
  have hB : (0 * (τ * Real.sin s) - a * (τ * Real.cos s)) / (τ * Real.sin s) ^ 2
      = -(a * Real.cos s / (τ * Real.sin s ^ 2)) := by
    field
  have h9 : Real.sin y ^ 2 * (τ - a * Real.cos s)
      = Real.sin y * (τ * Real.sin s * Real.cos (y - s)) := by
    linear_combination Real.sin y * hkey
  rw [hone, hA, hB, one_div_one_div]
  field_simp
  linear_combination hkey

/-- The full sum `∑_k dθ_k/dθ` of `Forgacs2017RationalDenominator` (15). -/
theorem hasDerivAt_ftAngleSum {n : ℕ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) {τ s : ℝ}
    (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) :
    HasDerivAt (fun t => ftAngleSum a τ t)
      (∑ k, Real.sin (ftAngle (a k) τ s) * Real.cos (ftAngle (a k) τ s - s) / Real.sin s) s :=
  HasDerivAt.fun_sum fun k _ => hasDerivAt_ftAngle (ha k) hτ hs

end ForgacsTran
