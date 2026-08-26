/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchFunction
import ForgacsTran.CubicWitnessInterior

/-!
# The witness pencil is an instance of the general branch

The tree carries two descriptions of the same object and, until now, no identity
between them.  `cubicTau` is defined at the witness pencil by the cubic relation
`2τ³cos θ - 3τ² + 1 = 0` and has the closed form `1/(2cos((π-θ)/3))`;
`ftTau a r l` is defined for a general admissible pencil as the solution of the
angle-sum equation of `Forgacs2017RationalDenominator` Lemma 2(ii), which is the
branch `thm:FT-geometry` parameterizes.  `cubicTau_eq_ftTau` says they agree
at `a = ![1,1,1]`, `r = 1`, `l = 2`, and `ftRootPoly_one_eq_cubicQ` says the
pencils they are branches of are the same polynomial.

Without these, nothing proved about the witness pencil composes with anything
proved about the general branch, in either direction — the two halves of the
development are about objects with no stated relation.

## Main statements

* `ftAngle_one_cubicTau` — the single branch angle at the witness is `(θ+2π)/3`.
* `cubicTau_eq_ftTau` — `cubicTau = ftTau ![1,1,1] 1 2` on the open arc.
* `ftRootPoly_one_eq_cubicQ` — `ftRootPoly 1 ![1,1,1] = cubicQ`.

## Implementation notes

**The index is `l = 2`, and it is the largest admissible one — not the only one.**
The branch equation asks for `∑_k θ_k = rθ + lπ`; here the three roots coincide
at `1`, so the sum is `3 arg(τe^{iθ} - 1)` and the equation reads `3θ₁ = θ + lπ`.
`ftBranchAt_of_arc` needs `l < n = 3`, and its solvability range `nθ < rθ + lπ`
puts `l = 2` in range at every angle of `(0,π)`, `l = 1` in range exactly for
`θ < π/2`, and `l = 0` nowhere — the last because every branch angle exceeds `θ`,
so the sum of three exceeds `3θ`.  Below `π/2` the index `l = 1` therefore names a
**genuinely different branch**, at a radius above `1` rather than below.
`ftAngleSum` is strictly decreasing in `τ`, so the largest index gives the
smallest radius: `l = 2` is the minimum-modulus branch, which is the one
`thm:FT-geometry` is about.  `scripts/check_cubic_branch_bridge.py` exhibits the
`l = 1` solutions and the monotonicity that orders them.

**Differs from the paper's route.**  `thm:FT-geometry` identifies the branch
through the implicit angle-sum equation and its monotonicity in `τ`, which is
what `ftTau_eq_of` reproduces.  The verification here goes the other way: the
witness has a closed form, so the angle is *computed* — with
`ψ = (π-θ)/3` the branch angle is `π - ψ` and the whole content collapses to
`sin 2ψ = sin 2ψ` after the triple-angle formulas.  The paper has no reason to
do this, since it never fixes a pencil; it is available only because this one is
concrete.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `thm:FT-geometry`), via
`Forgacs2017RationalDenominator` Lemma 2.

## Tags

branch equation, witness pencil, viewing angle, cubic pencil
-/

namespace ForgacsTran

open Real Set

/-- The trigonometric core of the branch equation at the witness: after the
triple-angle formulas both sides are `sin 2ψ`. -/
private theorem cubic_branch_trig (ψ : ℝ) :
    -Real.cos ψ * Real.sin (3 * ψ)
      = (-Real.cos (3 * ψ) - 2 * Real.cos ψ) * Real.sin ψ := by
  rw [Real.sin_three_mul, Real.cos_three_mul]
  linear_combination (4 * Real.cos ψ * Real.sin ψ) * Real.sin_sq_add_cos_sq ψ

/-- **The branch angle at the witness pencil.**  All three roots of
`Q = (1-t)^3` sit at `1`, so there is one branch angle, and it is `(θ+2π)/3`.

The proof computes rather than solves: `cubicTau_closed_form` puts
`τ = 1/(2cos ψ)` with `ψ = (π-θ)/3`, the candidate angle is `π - ψ`, and
`ftArccot_eq_of_cos_eq` reduces the claim to `cubic_branch_trig`. -/
theorem ftAngle_one_cubicTau {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ftAngle 1 (cubicTau θ) θ = (θ + 2 * π) / 3 := by
  have hθ1 := hθ.1
  have hθ2 := hθ.2
  have hpi := Real.pi_pos
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ1 hθ2
  have hc : 0 < Real.cos ((π - θ) / 3) := cos_third_pos ⟨hθ1.le, hθ2.le⟩
  have hτ : cubicTau θ = 1 / (2 * Real.cos ((π - θ) / 3)) :=
    cubicTau_closed_form ⟨hθ1.le, hθ2.le⟩
  have hy : (θ + 2 * π) / 3 ∈ Ioo 0 π := ⟨by linarith, by linarith⟩
  refine (ftArccot_eq_of_cos_eq hy ?_).symm
  set ψ : ℝ := (π - θ) / 3 with hψ
  have hθψ : θ = π - 3 * ψ := by rw [hψ]; ring
  have hcosθ : Real.cos θ = -Real.cos (3 * ψ) := by
    conv_lhs => rw [hθψ]
    rw [Real.cos_pi_sub]
  have hsinθ : Real.sin θ = Real.sin (3 * ψ) := by
    conv_lhs => rw [hθψ]
    rw [Real.sin_pi_sub]
  have hyψ : (θ + 2 * π) / 3 = π - ψ := by rw [hψ]; ring
  have hs3 : Real.sin (3 * ψ) ≠ 0 := by rw [← hsinθ]; exact hs.ne'
  rw [hyψ, Real.cos_pi_sub, Real.sin_pi_sub, hτ, hcosθ, hsinθ]
  field_simp
  linear_combination cubic_branch_trig ψ

/-- **`cubicTau` is the general branch at `a = ![1,1,1]`, `r = 1`, `l = 2`.**
The identity the rest of the tree needs in order to read a witness result as an
instance of a general one, or a general result at the witness. -/
theorem cubicTau_eq_ftTau {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    cubicTau θ = ftTau ![1, 1, 1] 1 2 θ := by
  refine ftTau_eq_of (by norm_num) (fun k => ?_) hθ (cubicTau_pos θ) ?_
  · fin_cases k <;> norm_num
  · rw [ftAngleSum, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [ftAngle_one_cubicTau hθ]
    push_cast
    ring

/-- **The pencils agree.**  `ftRootPoly 1 ![1,1,1]` is `(1-t)^3`, which is
`cubicQ` — so `cubicTau_eq_ftTau` relates two branches of *one* polynomial
family rather than two unrelated objects. -/
theorem ftRootPoly_one_eq_cubicQ : ftRootPoly 1 ![1, 1, 1] = cubicQ := by
  rw [ftRootPoly, cubicQ, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Complex.ofReal_one, map_one, one_mul]
  ring

end ForgacsTran
