/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/CompleteAlgebra.lean

import SkewJacobiNegative.Base.CompleteRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Rational complete-generator algebra

The rational polynomial ring of `shields-2026-skew-cofactor-independence.tex`,
«Beta lists and polynomial readings» (`sec:boundary`).  The coefficient extension
from the copied integral ring is injective.  Zero and negative generator indices
retain the manuscript's conventions.  Sorry-free.
-/

namespace SkewJacobiNegative

/-- The free rational algebra on the positive complete generators. -/
abbrev CompleteRing := MvPolynomial ℕ+ ℚ

/-- Faithful extension of the copied integral complete-generator ring to the rationals. -/
noncomputable def integerLift : Base.CompleteRing →+* CompleteRing :=
  MvPolynomial.map (Int.castRingHom ℚ)

/-- A signed generator index, with index zero equal to one and negative indices zero. -/
noncomputable def complete (k : ℤ) : CompleteRing := integerLift (Base.complete k)

/-- Rational coefficient extension loses no integral polynomial identity. -/
theorem integerLift_injective : Function.Injective integerLift := by
  apply MvPolynomial.map_injective
  intro a b h
  change (a : ℚ) = (b : ℚ) at h
  exact_mod_cast h

@[simp]
theorem integerLift_eq_iff (p q : Base.CompleteRing) :
    integerLift p = integerLift q ↔ p = q := integerLift_injective.eq_iff

@[simp]
theorem complete_zero : complete 0 = 1 := by
  simp [complete]

@[simp]
theorem complete_of_neg {k : ℤ} (hk : k < 0) : complete k = 0 := by
  simp [complete, Base.complete_of_neg hk]

/-- A positive-index complete generator is the corresponding independent variable. -/
theorem complete_of_pos {k : ℤ} (hk : 0 < k) :
    complete k = MvPolynomial.X ⟨k.toNat, by omega⟩ := by
  unfold complete
  rw [Base.complete_of_pos hk]
  exact MvPolynomial.map_X _ _

@[simp]
theorem complete_nat (k : ℕ+) : complete (k : ℕ) = MvPolynomial.X k := by
  unfold complete
  rw [Base.complete_nat]
  exact MvPolynomial.map_X _ _

/-- Exactly the nonnegative Jacobi--Trudi indices give nonzero entries. -/
theorem complete_ne_zero_iff (k : ℤ) : complete k ≠ 0 ↔ 0 ≤ k := by
  constructor
  · intro h
    apply (Base.complete_ne_zero_iff k).1
    intro hz
    apply h
    simp [complete, hz]
  · intro h hz
    have hi : Base.complete k = 0 := integerLift_injective (by simpa [complete] using hz)
    exact ((Base.complete_ne_zero_iff k).2 h) hi

/-- Determinants commute with the faithful rational coefficient extension. -/
theorem integerLift_det {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n Base.CompleteRing) :
    integerLift M.det = (M.map integerLift).det := by
  exact integerLift.map_det M

end SkewJacobiNegative
