/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import SkewGluing.RowInvariants

/-!
# Generator span of symmetric-function polynomials

Formalizes the generator-index span and its product rule in `shields-2026-skew-corner-descent.tex`,
«Corner cofactors and common cores» (`eq:polynomial-span`, `eq:product-span`).

`polynomialSpan` is the largest generator index occurring in a polynomial, with value zero for
constants.  For nonzero factors, the span of a product is the maximum of their spans.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The largest complete-homogeneous generator index occurring in a polynomial. -/
noncomputable def polynomialSpan (f : Lambda) : ℕ :=
  f.vars.sup fun k => (k : ℕ)

/-- A nonzero scalar has generator span zero.
This is the scalar clause of `eq:polynomial-span`; the product-law proof does not consume it. -/
@[simp]
theorem polynomialSpan_C (q : ℚ) : polynomialSpan (MvPolynomial.C q) = 0 := by
  simp [polynomialSpan]

/-- The generator span of a product of nonzero polynomials is the maximum of their spans. -/
theorem polynomialSpan_mul (f g : Lambda) (hf : f ≠ 0) (hg : g ≠ 0) :
    polynomialSpan (f * g) = max (polynomialSpan f) (polynomialSpan g) := by
  classical
  have hvars : (f * g).vars = f.vars ∪ g.vars := by
    ext k
    simp only [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, Finset.mem_union]
    rw [MvPolynomial.degreeOf_mul_eq hf hg]
    omega
  simp [polynomialSpan, hvars, Finset.sup_union]

/-- Multiplication cannot introduce a generator above both factors' spans. -/
theorem polynomialSpan_mul_le (f g : Lambda) :
    polynomialSpan (f * g) ≤ max (polynomialSpan f) (polynomialSpan g) := by
  apply Finset.sup_le
  intro k hk
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul f g hk) with hf | hg
  · exact (Finset.le_sup hf).trans (le_max_left _ _)
  · exact (Finset.le_sup hg).trans (le_max_right _ _)

/-- Taking a power introduces no new generator. -/
theorem polynomialSpan_pow_le (f : Lambda) (n : ℕ) :
    polynomialSpan (f ^ n) ≤ polynomialSpan f := by
  apply Finset.sup_le
  intro k hk
  exact Finset.le_sup (MvPolynomial.vars_pow f n hk)

/-- A factor of a nonzero polynomial has no higher generator span than the polynomial. -/
theorem polynomialSpan_le_of_dvd {f g : Lambda} (hg : g ≠ 0) (hd : f ∣ g) :
    polynomialSpan f ≤ polynomialSpan g := by
  obtain ⟨r, rfl⟩ := hd
  have hf : f ≠ 0 := fun hz => hg (by rw [hz, zero_mul])
  have hr : r ≠ 0 := fun hz => hg (by rw [hz, mul_zero])
  rw [polynomialSpan_mul f r hf hr]
  exact le_max_left _ _

end SkewCornerDescent.Matrix
