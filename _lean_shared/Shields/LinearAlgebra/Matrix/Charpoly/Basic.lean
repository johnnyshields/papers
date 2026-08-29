/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Elementary computations with characteristic polynomials

An upper triangular matrix has the product of `X - T i i` over its diagonal for characteristic
polynomial, and the zero matrix has a power of `X`, so `0` is its only root -- and on an empty
index type it has no root at all.  Over an integral domain a scalar is a root exactly when it is
an eigenvalue in the `mulVec` sense, which is the form the two directions are consumed in.

## Main results

* `Shields.charpoly_eq_prod_diag_of_upperTriangular`: the entrywise form of Mathlib's
  `Matrix.charpoly_of_upperTriangular`.
* `Shields.eq_zero_of_charpoly_zero_root`: a root of the characteristic polynomial of the zero
  matrix is `0`.
* `Shields.charpoly_eval_eq_zero_iff`: a scalar is a root of the characteristic polynomial exactly
  when it is a `mulVec` eigenvalue.
* `Shields.charpoly_eval_eq_zero_of_mulVec`, `Shields.exists_eigenvector_of_charpoly_root`: the two
  directions of that equivalence, over `ℝ` and over `ℂ` respectively.

## Tags

characteristic polynomial, triangular matrix, diagonal, root, eigenvalue, eigenvector
-/

namespace Shields

open Matrix

/-- The characteristic polynomial of the zero matrix has only `0` as a root.
`Matrix.charpoly_zero` gives it as `X ^ card ι` outright; on an empty `ι` that is
the constant `1`, which has no root at all. -/
theorem eq_zero_of_charpoly_zero_root {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : ℂ}
    (h : (0 : Matrix ι ι ℂ).charpoly.eval mu = 0) : mu = 0 := by
  rw [Matrix.charpoly_zero, Polynomial.eval_pow, Polynomial.eval_X] at h
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc | hc
  · rw [hc, pow_zero] at h
    exact absurd h one_ne_zero
  · exact (pow_eq_zero_iff hc.ne').mp h

/-- The characteristic polynomial of a triangular matrix is the product of `X - T i i` over the
diagonal.  Mathlib's `Matrix.charpoly_of_upperTriangular` asks for `BlockTriangular id`; this is
the entrywise form. -/
theorem charpoly_eq_prod_diag_of_upperTriangular {R : Type*} [CommRing R] {m : ℕ}
    {T : Matrix (Fin m) (Fin m) R} (hT : ∀ i j, j < i → T i j = 0) :
    T.charpoly = ∏ i, (Polynomial.X - Polynomial.C (T i i)) :=
  Matrix.charpoly_of_upperTriangular T fun _ _ hij => hT _ _ hij

section Eigenvalues

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem scalar_mulVec {R : Type*} [CommRing R] (mu : R) (x : ι → R) :
    (Matrix.scalar ι mu) *ᵥ x = mu • x := by
  ext i
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

/-- **A scalar is a root of the characteristic polynomial exactly when it is an
eigenvalue**, in the `mulVec` sense, over any integral domain. -/
theorem charpoly_eval_eq_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    {M : Matrix ι ι R} {mu : R} :
    M.charpoly.eval mu = 0 ↔ ∃ x : ι → R, x ≠ 0 ∧ M *ᵥ x = mu • x := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun x => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, scalar_mulVec, sub_eq_zero, eq_comm]

/-- An eigenvector in the `mulVec` sense makes its eigenvalue a root of the
characteristic polynomial. -/
theorem charpoly_eval_eq_zero_of_mulVec {A : Matrix ι ι ℝ} {mu : ℝ}
    {x : ι → ℝ} (hx : x ≠ 0) (h : A *ᵥ x = mu • x) : A.charpoly.eval mu = 0 :=
  charpoly_eval_eq_zero_iff.mpr ⟨x, hx, h⟩

/-- A root of the characteristic polynomial has an eigenvector. -/
theorem exists_eigenvector_of_charpoly_root {M : Matrix ι ι ℂ} {mu : ℂ}
    (h : M.charpoly.eval mu = 0) : ∃ z : ι → ℂ, z ≠ 0 ∧ M *ᵥ z = mu • z :=
  charpoly_eval_eq_zero_iff.mp h

end Eigenvalues


/-! ### Axiom footprint -/

/-- info: 'Shields.charpoly_eq_prod_diag_of_upperTriangular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charpoly_eq_prod_diag_of_upperTriangular

/-- info: 'Shields.eq_zero_of_charpoly_zero_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_zero_of_charpoly_zero_root

/-- info: 'Shields.charpoly_eval_eq_zero_of_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charpoly_eval_eq_zero_of_mulVec

/-- info: 'Shields.exists_eigenvector_of_charpoly_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_eigenvector_of_charpoly_root

end Shields
