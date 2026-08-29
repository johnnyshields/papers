/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.BigOperators

/-!
# The equality case of the triangle inequality over `ℂ`

`‖∑ u_k‖ ≤ ∑ ‖u_k‖` holds in any normed space; equality forces every summand onto the ray
through the total.  Over `ℂ` that alignment is stated multiplicatively,
`‖S‖ · u_j = ‖u_j‖ · S`, which is the form the consumers use.

## Main results

* `Shields.norm_smul_eq_of_norm_sum_eq`: equality in the triangle inequality for a finite sum
  of complex numbers aligns every term with the sum.

## Implementation notes

The proof runs through real parts rather than `SameRay`.  Mathlib carries the two-term equality
case (`sameRay_iff_norm_add`, `sameRay_iff_norm_smul_eq`) but no finite-sum form of it; the
`SameRay` route would need the termwise conclusion assembled from those anyway, and the real-part
argument reaches it in one pass.

Mathlib PR #39915, *the equality case of the triangle inequality*, adds
`Complex.triangle_equality_iff_aligned`, which subsumes this file.  Retire it when that lands.

## Tags

triangle inequality, equality case, complex numbers, same ray, alignment
-/

open scoped BigOperators

namespace Shields

/-- A complex number whose real part is its modulus is that modulus. -/
private theorem eq_ofReal_norm_of_re_eq_norm {w : ℂ} (h : w.re = ‖w‖) : w = ((‖w‖ : ℝ) : ℂ) := by
  have him : w.im = 0 :=
    Complex.abs_re_eq_norm.mp (by rw [abs_of_nonneg (by rw [h]; exact norm_nonneg w), h])
  exact Complex.ext (by rw [Complex.ofReal_re, h]) (by rw [him, Complex.ofReal_im])

/-- **Equality in the triangle inequality over `ℂ`.**  If the norm of a finite
sum equals the sum of the norms and the sum is nonzero, then every term is a
nonnegative real multiple of the total: `‖S‖ · u j = ‖u j‖ · S`.

Proved through real parts rather than `SameRay`: with `w j = conj S · u j`, the
sum of the `w j` is the real number `‖S‖²`, each `Re (w j) ≤ ‖w j‖ = ‖S‖‖u j‖`,
and the totals agree — so every inequality is an equality, forcing each `w j`
real and nonnegative. -/
theorem norm_smul_eq_of_norm_sum_eq {α : Type*} {s : Finset α} {u : α → ℂ}
    (h : ‖∑ k ∈ s, u k‖ = ∑ k ∈ s, ‖u k‖) {j : α} (hj : j ∈ s) :
    (‖∑ k ∈ s, u k‖ : ℂ) * u j = (‖u j‖ : ℂ) * (∑ k ∈ s, u k) := by
  set S : ℂ := ∑ k ∈ s, u k with hS
  rcases eq_or_ne S 0 with h0 | h0
  · -- Every term vanishes, since the norms sum to zero.
    have hsum : ∑ k ∈ s, ‖u k‖ = 0 := by rw [← h, h0, norm_zero]
    have hzj : ‖u j‖ = 0 := le_antisymm
      (hsum ▸ Finset.single_le_sum (fun i _ => norm_nonneg (u i)) hj) (norm_nonneg _)
    rw [h0, norm_zero, hzj]
    simp [norm_eq_zero.mp hzj]
  · have hSn : (0 : ℝ) < ‖S‖ := norm_pos_iff.mpr h0
    -- `∑ conj S * u k = ‖S‖²`, a real number.
    have hconj : ∑ k ∈ s, (starRingEnd ℂ) S * u k = ((‖S‖ * ‖S‖ : ℝ) : ℂ) := by
      rw [← Finset.mul_sum, ← hS, mul_comm, Complex.mul_conj,
        Complex.norm_mul_self_eq_normSq]
    -- Termwise `Re ≤ norm`, with equal totals.
    have hre : ∀ k ∈ s, ((starRingEnd ℂ) S * u k).re ≤ ‖S‖ * ‖u k‖ := fun k _ => by
      have h1 := Complex.re_le_norm ((starRingEnd ℂ) S * u k)
      rwa [norm_mul, RCLike.norm_conj] at h1
    have htot : ∑ k ∈ s, ((starRingEnd ℂ) S * u k).re = ∑ k ∈ s, ‖S‖ * ‖u k‖ := by
      rw [← Complex.re_sum, hconj, Complex.ofReal_re, ← Finset.mul_sum, ← h]
    have heq := (Finset.sum_eq_sum_iff_of_le hre).1 htot j hj
    -- A complex number whose real part equals its norm is that norm.
    have hreal : (starRingEnd ℂ) S * u j = ((‖S‖ * ‖u j‖ : ℝ) : ℂ) := by
      rw [eq_ofReal_norm_of_re_eq_norm (w := (starRingEnd ℂ) S * u j)
        (by rw [heq, norm_mul, RCLike.norm_conj]), norm_mul, RCLike.norm_conj]
    -- Multiply through by `S` and cancel one factor of `‖S‖`.
    have hmul : S * ((starRingEnd ℂ) S * u j) = S * ((‖S‖ * ‖u j‖ : ℝ) : ℂ) := by rw [hreal]
    rw [← mul_assoc, Complex.mul_conj, ← Complex.norm_mul_self_eq_normSq] at hmul
    refine mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hSn.ne' : (‖S‖ : ℂ) ≠ 0) ?_
    push_cast at hmul ⊢
    linear_combination hmul


/-! ### Axiom footprint -/

/-- info: 'Shields.norm_smul_eq_of_norm_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_smul_eq_of_norm_sum_eq

end Shields
