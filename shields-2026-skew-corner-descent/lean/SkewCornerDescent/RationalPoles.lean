/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.RingTheory.Algebraic.LinearIndependent

/-!
# Finite rational pole sums

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original coefficients»
(`sec:dual`, `lem:dual-identities`). Distinct rational poles cannot cancel a nonzero finite
coefficient inventory at a transcendental coordinate. The actual residue coordinate must
still be supplied by the ordered determinant chart. Sorry-free.
-/

namespace SkewCornerDescent.RationalPoles

/-- Every coefficient of a vanishing finite inverse-pole sum is zero. Distinct labels
are retained as a finite set; multiplicities belong in the coefficients. -/
theorem coefficients_zero_of_pole_sum_zero {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (hx : Transcendental F x) (s : Finset F) (c : F → F)
    (h : ∑ a ∈ s, c a • (x - algebraMap F E a)⁻¹ = 0) :
    ∀ a ∈ s, c a = 0 := by
  exact linearIndependent_iff'.mp hx.linearIndependent_sub_inv s c h

/-- A nonzero total coefficient forces the complete finite inverse-pole sum nonzero. -/
theorem pole_sum_ne_zero_of_total_ne_zero {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (hx : Transcendental F x) (s : Finset F) (c : F → F)
    (hc : ∑ a ∈ s, c a ≠ 0) :
    ∑ a ∈ s, c a • (x - algebraMap F E a)⁻¹ ≠ 0 := by
  intro h
  exact hc (Finset.sum_eq_zero (coefficients_zero_of_pole_sum_zero x hx s c h))

/-- Clearing a shared nonzero response factor preserves the full inverse-pole detector. -/
theorem scaled_pole_sum_ne_zero {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x scale : E) (hx : Transcendental F x) (hscale : scale ≠ 0)
    (s : Finset F) (c : F → F) (hc : ∑ a ∈ s, c a ≠ 0) :
    ∑ a ∈ s, c a • (scale * (x - algebraMap F E a))⁻¹ ≠ 0 := by
  have heq : (∑ a ∈ s, c a • (scale * (x - algebraMap F E a))⁻¹) =
      scale⁻¹ * ∑ a ∈ s, c a • (x - algebraMap F E a)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [mul_inv_rev, Algebra.smul_def]
    ring
  rw [heq]
  exact mul_ne_zero (inv_ne_zero hscale) (pole_sum_ne_zero_of_total_ne_zero x hx s c hc)

end SkewCornerDescent.RationalPoles
