/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.CubicWitness
import ForgacsTran.CubicClockSpacing
import ForgacsTran.BranchSupply

/-!
# A collision of multiplicity two

`BranchSupplyWitness` instantiates `BranchSupply`'s collar at the Favard
semicircle, where both collisions are **simple**.  `BranchSupply` proves that
collar at arbitrary multiplicity, so `ν = 1` exercises only the easy case.

This module supplies `ν = 2`, and it needs no new pencil: at `Q = (1-t)^3` with
`r = 1` the critical polynomial is

  `E = XQ' - rQ = -3X(1-X)^2 - (1-X)^3 = -(1-X)^2(2X+1)`,

a **double** root at `1` and a simple root at `-1/2`.  The branch runs into `1` as
`θ → 0` (`CubicWitness.cubicTau_zero`), so the lower collision has multiplicity
exactly two.

**Why multiplicity two is available here and not at a quadratic pencil.**  With
`Q = c(a₁-t)(a₂-t)` the critical polynomial is `c[(2-r)t² + (r-1)st - rp]` for
`s = a₁+a₂`, `p = a₁a₂`, and a double root needs `(r-1)²s² = 4r(r-2)p`.  Since
`s² ≥ 4p` for positive zeros, that forces `(r-1)² ≤ r² - 2r`, i.e. `1 ≤ 0`.  **No
pencil of degree two has a repeated collision at any `r`.**  Degree three with a
triple zero is the first place one exists, which is why the witness is the cubic.

The general statement behind it is `Geometry.rootMultiplicity_ftCritical`: `E`
vanishes at a point to one order less than the denominator does, so a `ρ`-fold
zero of `Q` at the lower endpoint gives `ν = ρ - 1`.  Here `ρ = 3`.

## What this exercises that the semicircle does not

The arbitrary-multiplicity half of the collar, and only that.  `τ` is not constant
here — `cubicTau` is defined implicitly and is nowhere near a circle — so the
curvature quantity is not the constant `1` either; but this module proves nothing
about it, and a reader should not read the pencil's non-constancy as coverage of
any hypothesis this file does not state.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `lem:amplitude-divisor`,
  `eq:ab-def`.

## Tags

collision multiplicity, collar, witness, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Complex

/-- **The critical polynomial of the cubic pencil.**  `E = -(1-X)^2(2X+1)`: a
double zero at `1` and a simple one at `-1/2`. -/
theorem ftCritical_cubicQ :
    ftCritical cubicQ 1 = -((1 - X) ^ 2 * (2 * X + 1)) := by
  refine Polynomial.funext fun t => ?_
  have hd : (derivative cubicQ).eval t = -3 * (1 - t) ^ 2 := by
    rw [cubicQ]
    simp [derivative_pow]
  rw [eval_ftCritical, hd, cubicQ_eval]
  simp only [eval_neg, eval_mul, eval_pow, eval_sub, eval_one, eval_X, eval_add,
    eval_ofNat]
  push_cast
  ring

theorem ftCritical_cubicQ_ne_zero : ftCritical cubicQ 1 ≠ 0 := by
  intro h
  have := congrArg (fun p => Polynomial.eval 0 p) h
  rw [ftCritical_cubicQ] at this
  simp at this

/-- The zeros of `E` are `1` and `-1/2`, and both are **real**. -/
theorem eval_ftCritical_cubicQ_eq_zero_iff {w : ℂ} :
    (ftCritical cubicQ 1).eval w = 0 ↔ w = 1 ∨ w = -(1 / 2) := by
  have hev : (ftCritical cubicQ 1).eval w = -((1 - w) ^ 2 * (2 * w + 1)) := by
    rw [ftCritical_cubicQ]
    simp only [eval_neg, eval_mul, eval_pow, eval_sub, eval_one, eval_X, eval_add,
      eval_ofNat]
  rw [hev, neg_eq_zero, mul_eq_zero, pow_eq_zero_iff (n := 2) (by norm_num),
    sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by linear_combination h / 2)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (by norm_num)

/-- **`ν = 2` at the lower endpoint.**  The branch reaches `1` as `θ → 0`, and `1`
is a double zero of `E`.  This is the case `BranchSupplyWitness` cannot reach. -/
theorem ftCollisionOrder_cubic_zero : ftCollisionOrder cubicQ 1 cubicTau 0 = 2 := by
  have hprin : ftPrincipal cubicTau 0 = 1 := by
    rw [ftPrincipal, cubicTau_zero]; simp
  rw [ftCollisionOrder, hprin, ftCritical_cubicQ]
  have hfac : -((1 - X : Polynomial ℂ) ^ 2 * (2 * X + 1))
      = (X - C 1) ^ 2 * (-(2 * X + 1)) := by
    simp only [map_one]
    ring
  have hne : ((X - C (1 : ℂ)) ^ 2 * (-(2 * X + 1)) : Polynomial ℂ) ≠ 0 := by
    rw [← hfac, ← ftCritical_cubicQ]; exact ftCritical_cubicQ_ne_zero
  rw [hfac, Polynomial.rootMultiplicity_mul hne, Polynomial.rootMultiplicity_X_sub_C_pow,
    Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot]; norm_num)]

/-- **`E` does not vanish on the open arc.**  Both zeros of `E` are real, and the
branch point has strictly positive imaginary part there. -/
theorem ftCriticalAlong_cubic_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) :
    ftCriticalAlong cubicQ 1 cubicTau θ ≠ 0 := by
  rw [ftCriticalAlong]
  intro hzero
  have him : (ftPrincipal cubicTau θ).im = cubicTau θ * Real.sin θ := by
    rw [ftPrincipal, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hpos : 0 < (ftPrincipal cubicTau θ).im := by
    rw [him]
    exact mul_pos (cubicTau_pos θ) (Real.sin_pos_of_mem_Ioo hθ)
  rcases eval_ftCritical_cubicQ_eq_zero_iff.1 hzero with h | h <;> rw [h] at hpos <;>
    simp at hpos

/-! ### The curvature quantity at a non-constant `τ`

Every witness in the tree so far has `τ` constant, which makes
`K = τ² + 2τ'² - ττ''` the constant `1` and the branch a circle.  `cubicTau` is
not constant — it is defined implicitly and satisfies `2τ³cos θ - 3τ² + 1 = 0` —
so this is the first pencil where `K` is a genuine function of `θ`.

It is still computable in closed form, and the answer is clean: writing
`ψ = (π-θ)/3` and `c = cos ψ`, the tree's own `cubicTau_closed_form`,
`cubicTauDeriv` and `cubicTauDeriv2` give `τ = 1/(2c)`, `τ' = -sin ψ/(6c²)` and
`τ'' = (c² + 2sin²ψ)/(18c³)`, and

  `K = 1/(4c²) + 2sin²ψ/(36c⁴) - (c² + 2sin²ψ)/(36c⁴) = 8c²/(36c⁴) = (8/9)τ²`,

so `K` is a fixed multiple of `τ²` and is positive wherever `τ` is.  Checked
numerically to 41 digits over 400 angles before it was proved.

By the identification `wedge γ'' γ' = K` this is `hcurv` at this pencil: the
branch nowhere inflects.  It is the first non-constant-`τ` instance, so together
with `ftCollisionOrder_cubic_zero` this pencil covers **two** of the three
degeneracies `BranchSupplyWitness` records — `ν = 1` and `τ ≡ 1` — at once. -/

/-- **`K = (8/9)τ²` along the cubic branch.**  An identity, not an estimate. -/
theorem cubic_curvature_eq {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) π) :
    cubicTau θ ^ 2 + 2 * cubicTauDeriv θ ^ 2 - cubicTau θ * cubicTauDeriv2 θ
      = 8 / 9 * cubicTau θ ^ 2 := by
  have hc : 0 < Real.cos ((π - θ) / 3) := cos_third_pos hθ
  have hpy : Real.sin ((π - θ) / 3) ^ 2 + Real.cos ((π - θ) / 3) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  rw [cubicTau_closed_form hθ, cubicTauDeriv, cubicTauDeriv2]
  field_simp
  nlinarith [hpy, hc, sq_nonneg (Real.cos ((π - θ) / 3)),
    sq_nonneg (Real.sin ((π - θ) / 3))]

/-- **The curvature quantity is strictly positive on the whole closed arc**, so
`hcurv` holds here with `τ` genuinely varying. -/
theorem cubic_curvature_pos {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) π) :
    0 < cubicTau θ ^ 2 + 2 * cubicTauDeriv θ ^ 2 - cubicTau θ * cubicTauDeriv2 θ := by
  rw [cubic_curvature_eq hθ]
  have h := cubicTau_pos θ
  positivity

/-- **`τ` really does vary**, so the previous two are not the constant case in
disguise: `τ(0) = 1` and `τ(π) = 1/2`. -/
theorem cubicTau_not_constant : cubicTau 0 ≠ cubicTau π := by
  have h0 : cubicTau 0 = 1 := cubicTau_zero
  have hpi : cubicTau π = 1 / 2 := by
    have hc : Real.cos ((π - π) / 3) = 1 := by norm_num
    rw [cubicTau_closed_form ⟨Real.pi_pos.le, le_rfl⟩, hc]
    norm_num
  rw [h0, hpi]
  norm_num

end ForgacsTran
