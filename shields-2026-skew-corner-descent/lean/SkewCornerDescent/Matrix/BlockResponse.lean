/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.Derivation.Basic

/-!
# Complete block elimination and inverse derivatives

Supports local algebraic steps in `shields-2026-skew-corner-descent.tex`, «Equal windows and
the determinant defect» (`sec:normal-chart`) and «From response functions to literal copies»
(`sec:one-active`).

The matrix calculus underlying `lem:actual-elimination` and `lem:profile-derivative`.
The retained block is unrestricted: in particular neither exterior row nor exterior column
is removed. The derivative acts on the entire inverse of the removed block.

These are block-matrix primitives, not a construction of the selected components of an
actual Jacobi--Trudi matrix. Sorry-free.
-/

open scoped Matrix

namespace SkewCornerDescent.Matrix

variable {R K m n l : Type*} [CommRing R] [CommRing K] [Algebra R K]

/-- Apply a derivation to every matrix entry. -/
def entryDeriv (D : Derivation R K K) (M : Matrix m n K) : Matrix m n K :=
  fun i j => D (M i j)

@[simp]
theorem entryDeriv_add (D : Derivation R K K) (A B : Matrix m n K) :
    entryDeriv D (A + B) = entryDeriv D A + entryDeriv D B := by
  ext i j
  exact map_add D _ _

@[simp]
theorem entryDeriv_sub (D : Derivation R K K) (A B : Matrix m n K) :
    entryDeriv D (A - B) = entryDeriv D A - entryDeriv D B := by
  ext i j
  exact map_sub D _ _

@[simp]
theorem entryDeriv_one [DecidableEq m] (D : Derivation R K K) :
    entryDeriv D (1 : Matrix m m K) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [entryDeriv, Matrix.one_apply, h]

theorem entryDeriv_mul [Fintype n] (D : Derivation R K K)
    (A : Matrix m n K) (B : Matrix n l K) :
    entryDeriv D (A * B) = entryDeriv D A * B + A * entryDeriv D B := by
  ext i j
  simp only [entryDeriv, Matrix.mul_apply, Matrix.add_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The exact reduced matrix after removing a complete invertible block. -/
noncomputable def retainedResponse [Fintype n] [DecidableEq n] (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (P : Matrix n n K) [Invertible P] : Matrix m m K :=
  A - B * ⅟P * C

/-- Full block elimination retains the original removed determinant as its unit factor. -/
theorem det_eq_removed_mul_response [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K)
    (P : Matrix n n K) [Invertible P] :
    (Matrix.fromBlocks A B C P).det = P.det * (retainedResponse A B C P).det :=
  Matrix.det_fromBlocks₂₂ A B C P

/-- Differentiating the complete inverse; no residue-zero inverse entry is discarded. -/
theorem entryDeriv_invOf [Fintype n] [DecidableEq n] (D : Derivation R K K)
    (P : Matrix n n K) [Invertible P] :
    entryDeriv D (⅟P) = -(⅟P * entryDeriv D P * ⅟P) := by
  have h := congrArg (entryDeriv D) (mul_invOf_self P)
  rw [entryDeriv_mul, entryDeriv_one] at h
  have h' := congrArg (fun M => ⅟P * M) h
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, invOf_mul_self,
    Matrix.one_mul, Matrix.mul_zero] at h'
  exact eq_neg_of_add_eq_zero_right h'

/-- The four terms of the full Schur-complement derivative, including the internal term. -/
theorem entryDeriv_retainedResponse [Fintype n] [DecidableEq n]
    (D : Derivation R K K) (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (P : Matrix n n K) [Invertible P] :
    entryDeriv D (retainedResponse A B C P) =
      entryDeriv D A - entryDeriv D B * ⅟P * C - B * ⅟P * entryDeriv D C +
        B * ⅟P * entryDeriv D P * ⅟P * C := by
  rw [retainedResponse, entryDeriv_sub, entryDeriv_mul, entryDeriv_mul,
    entryDeriv_invOf]
  simp only [Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

end SkewCornerDescent.Matrix
