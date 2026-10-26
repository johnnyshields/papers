/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.CompleteAlgebra
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Dilation of the complete-generator algebra

The injective substitution in `thm:dilation` sends the independent variable
`h_j` to `h_(t*j)`.  It commutes with determinants and signed cofactors and
preserves rational linear independence.
-/

noncomputable section

namespace SkewCofactorIndependence

/-- Multiplication of positive generator indices by a positive dilation factor. -/
def gridIndex (t j : ℕ+) : ℕ+ := t * j

@[simp]
theorem gridIndex_coe (t j : ℕ+) : (gridIndex t j : ℕ) = (t : ℕ) * (j : ℕ) := rfl

/-- No two positive generator indices merge under dilation. -/
theorem gridIndex_injective (t : ℕ+) : Function.Injective (gridIndex t) := by
  intro i j h
  apply Subtype.ext
  have hh := congrArg (fun k : ℕ+ => (k : ℕ)) h
  dsimp [gridIndex] at hh
  exact Nat.eq_of_mul_eq_mul_left t.property hh

/-- The manuscript's actual rational polynomial generator substitution. -/
def dilation (t : ℕ+) : CompleteRing →ₐ[ℚ] CompleteRing :=
  MvPolynomial.rename (gridIndex t)

@[simp]
theorem dilation_X (t j : ℕ+) : dilation t (MvPolynomial.X j) =
    MvPolynomial.X (gridIndex t j) := MvPolynomial.rename_X _ _

/-- Dilation is faithful on the whole polynomial algebra. -/
theorem dilation_injective (t : ℕ+) : Function.Injective (dilation t) :=
  MvPolynomial.rename_injective _ (gridIndex_injective t)

@[simp]
theorem dilation_eq_zero_iff (t : ℕ+) (p : CompleteRing) :
    dilation t p = 0 ↔ p = 0 := by
  constructor
  · intro h
    exact dilation_injective t (h.trans (map_zero (dilation t)).symm)
  · intro h
    rw [h, map_zero]

/-- The negative-index convention survives the substitution. -/
theorem dilation_complete_of_neg (t : ℕ+) {k : ℤ} (hk : k < 0) :
    dilation t (complete k) = 0 := by simp [complete_of_neg hk]

/-- The positive-index formula, including its precise positive variable index. -/
theorem dilation_complete_nat (t j : ℕ+) :
    dilation t (complete (j : ℕ)) = complete ((t : ℕ) * (j : ℕ)) := by
  change dilation t (complete (j : ℕ)) = complete (gridIndex t j : ℕ)
  rw [complete_nat j, dilation_X]
  exact (complete_nat (gridIndex t j)).symm

/-- The signed generator formula includes zero and negative indices. -/
theorem dilation_complete (t : ℕ+) (k : ℤ) :
    dilation t (complete k) = complete ((t : ℕ) * k) := by
  have ht : (0 : ℤ) < (t : ℕ) := by exact_mod_cast t.property
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [complete_of_neg hk, map_zero, complete_of_neg (mul_neg_of_pos_of_neg ht hk)]
  · subst k
    simp
  · let j : ℕ+ := ⟨k.toNat, by omega⟩
    have hj : ((j : ℕ) : ℤ) = k := by simp [j, Int.toNat_of_nonneg (le_of_lt hk)]
    have h := dilation_complete_nat t j
    simpa only [Nat.cast_mul, hj] using h

/-- Polynomial determinants commute with dilation. -/
theorem dilation_det (t : ℕ+) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n CompleteRing) :
    dilation t M.det = (M.map (dilation t)).det :=
  (dilation t).toRingHom.map_det M

/-- Jacobi--Trudi determinants commute with the actual signed-index substitution. -/
theorem dilation_complete_det (t : ℕ+) {n : Type*} [Fintype n] [DecidableEq n]
    (k : n → n → ℤ) :
    dilation t (Matrix.of (fun i j => complete (k i j))).det =
      (Matrix.of (fun i j => complete ((t : ℕ) * k i j))).det := by
  rw [dilation_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact dilation_complete t (k i j)

/-- Adjugate entries are transposed signed cofactors, and commute with dilation. -/
theorem dilation_cofactor (t : ℕ+) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n CompleteRing) (i j : n) :
    dilation t (M.adjugate j i) = (M.map (dilation t)).adjugate j i := by
  have h := (dilation t).map_adjugate M
  exact congrArg (fun A : Matrix n n CompleteRing => A j i) h

/-- The signed-minor form of cofactor commutation, for arbitrary deletion maps. -/
theorem dilation_signed_minor (t : ℕ+) {n m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix n n CompleteRing) (row col : m → n) (sign : ℚ) :
    dilation t (MvPolynomial.C sign * (M.submatrix row col).det) =
      MvPolynomial.C sign * ((M.map (dilation t)).submatrix row col).det := by
  rw [map_mul, MvPolynomial.algHom_C, dilation_det]
  rfl

/-- Every rationally independent family remains independent after dilation. -/
theorem linearIndependent_dilation {ι : Type*} (t : ℕ+) {f : ι → CompleteRing}
    (hf : LinearIndependent ℚ f) : LinearIndependent ℚ (fun i => dilation t (f i)) := by
  exact hf.map_injOn (dilation t).toLinearMap (dilation_injective t).injOn

end SkewCofactorIndependence
