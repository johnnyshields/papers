/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SimpleExtensionConstants

/-!
# Ordinary affine coefficients in a simple rational extension

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A vanishing second partial derivative yields an actual degree-at-most-one
polynomial over the original coefficient field and identifies its ordinary
linear coefficient. Sorry-free.
-/

namespace SkewCornerDescent
open Polynomial

/-- Vanishing second derivative produces an actual affine polynomial over the
original coefficient field, whose ordinary linear coefficient is the derivative. -/
theorem simple_extension_affine_polynomial {E : Type*} [Field E] [Algebra ℚ E]
    [CharZero E] {m : Module ℚ E} (δ : @Derivation ℚ E E _ _ _ _ _ m) (B : Subfield E)
    (hB : ∀ s : B, δ (s : E) = 0) (x : E) (hx : δ x = 1)
    (hgen : IntermediateField.adjoin B {x} = ⊤) (f : E) (hδδ : δ (δ f) = 0) :
    ∃ p : Polynomial B, p.natDegree ≤ 1 ∧ Polynomial.aeval x p = f ∧
      ((p.coeff 1 : B) : E) = δ f := by
  have hx0 : δ x ≠ 0 := by rw [hx]; exact one_ne_zero
  have hs : δ f ∈ B := simple_extension_derivation_constants δ B hB x (δ f) hx0
    (by rw [hgen]; trivial) hδδ
  have hi : f - x * δ f ∈ B := by
    apply simple_extension_derivation_constants δ B hB x _ hx0
    · rw [hgen]
      trivial
    · rw [map_sub, δ.leibniz, hx, hδδ, smul_zero, zero_add, smul_eq_mul, mul_one, sub_self]
  let slope : B := ⟨δ f, hs⟩
  let intercept : B := ⟨f - x * δ f, hi⟩
  refine ⟨Polynomial.C intercept + Polynomial.C slope * Polynomial.X, ?_, ?_, ?_⟩
  · apply (Polynomial.natDegree_add_le _ _).trans
    simp only [Polynomial.natDegree_C, max_le_iff, zero_le, true_and]
    exact Polynomial.natDegree_mul_le.trans (by simp)
  · simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    change f - x * δ f + δ f * x = f
    ring
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C, one_ne_zero, ite_false,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one, zero_add]
    rfl

end SkewCornerDescent
