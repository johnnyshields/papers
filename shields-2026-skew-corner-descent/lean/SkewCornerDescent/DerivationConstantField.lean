/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Constants of coefficient-field derivations

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A moving coefficient is transcendental over the actual derivation constants,
by characteristic-zero separability of its minimal polynomial. Sorry-free.
-/

namespace SkewCornerDescent
open Polynomial

/-- The genuine constants of a rational coefficient derivation. -/
def derivationConstantField {E : Type*} [Field E] [Algebra ℚ E] {m : Module ℚ E}
    (δ : @Derivation ℚ E E _ _ _ _ _ m) : Subfield E where
  carrier := {x | δ x = 0}
  zero_mem' := map_zero δ
  one_mem' := δ.map_one_eq_zero
  add_mem' {a b} hx hy := by
    change δ a = 0 at hx
    change δ b = 0 at hy
    change δ (a + b) = 0
    rw [map_add, hx, hy, add_zero]
  mul_mem' {a b} hx hy := by
    change δ a = 0 at hx
    change δ b = 0 at hy
    change δ (a * b) = 0
    rw [δ.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  neg_mem' {x} hx := by
    change δ x = 0 at hx
    change δ (-x) = 0
    rw [map_neg, hx, neg_zero]
  inv_mem' x hx := by
    change δ x = 0 at hx
    change δ x⁻¹ = 0
    rw [δ.leibniz_inv, hx, smul_zero]

/-- The same derivation is linear over its full constant field. -/
noncomputable def overConstantField {E : Type*} [Field E] [Algebra ℚ E] {m : Module ℚ E}
    (δ : @Derivation ℚ E E _ _ _ _ _ m) : Derivation (derivationConstantField δ) E E where
  toFun := δ
  map_add' := map_add δ
  map_smul' s x := by
    change δ ((s : E) * x) = (s : E) * δ x
    rw [δ.leibniz, s.property, smul_zero, add_zero, smul_eq_mul]
  map_one_eq_zero' := δ.map_one_eq_zero
  leibniz' := δ.leibniz

@[simp]
theorem overConstantField_apply {E : Type*} [Field E] [Algebra ℚ E] {m : Module ℚ E}
    (δ : @Derivation ℚ E E _ _ _ _ _ m) (x : E) : overConstantField δ x = δ x := rfl

/-- A moving element is transcendental over the actual constants. -/
theorem transcendental_over_derivation_constants {E : Type*} [Field E] [Algebra ℚ E]
    {m : Module ℚ E} [CharZero E] (δ : @Derivation ℚ E E _ _ _ _ _ m) (x : E) (hx : δ x ≠ 0) :
    Transcendental (derivationConstantField δ) x := by
  intro ha
  have hi := ha.isIntegral
  have hs := (minpoly.irreducible hi).separable
  have hn := hs.aeval_derivative_ne_zero (minpoly.aeval (derivationConstantField δ) x)
  have he := (overConstantField δ).map_aeval
    (minpoly (derivationConstantField δ) x) x
  rw [minpoly.aeval, map_zero] at he
  have hm : Polynomial.aeval x (minpoly (derivationConstantField δ) x).derivative * δ x = 0 := by
    simpa only [smul_eq_mul, overConstantField_apply] using he.symm
  exact hx ((mul_eq_zero.mp hm).resolve_left hn)

end SkewCornerDescent
