/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Complete inverses of literal singleton row blocks

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Triangular support with injective component labels makes a literal unit pivot
have inverse diagonal entry one. An equal row/column coordinate cannot see a
cross-component inverse entry. Off-diagonal inverse entries at other positions
remain unrestricted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {ν α F : Type*} [Fintype ν] [DecidableEq ν] [LinearOrder α] [CommRing F]

/-- A literal unit diagonal entry in singleton ordered blocks has inverse
entry one, using the complete inverse and its actual left-inverse identity. -/
theorem row_block_inverse_unit_diagonal (M : Matrix ν ν F) [Invertible M]
    (label : ν → α) (hlabel : Function.Injective label) (hM : M.BlockTriangular label)
    (i : ν) (hunit : M i i = 1) : (⅟M) i i = 1 := by
  classical
  have hI := Matrix.blockTriangular_inv_of_blockTriangular hM
  have h : (⅟M * M) i i = 1 := by
    rw [invOf_mul_self]
    simp only [Matrix.one_apply, ite_true]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
  · rwa [hunit, mul_one] at h
  · intro k _ hki
    rcases lt_trichotomy (label k) (label i) with hlt | he | hgt
    · have hz : (⅟M) i k = 0 := by
        simpa only [Matrix.invOf_eq_nonsing_inv] using hI hlt
      rw [hz, zero_mul]
    · exact (hki (hlabel he)).elim
    · rw [hM hgt, mul_zero]
  · intro hni
    exact (hni (Finset.mem_univ i)).elim

omit [Fintype ν] [DecidableEq ν] [CommRing F] in
/-- At an equal physical row/column coordinate, every cross-component inverse
entry vanishes. Singleton labels and actual strict separation supply the
exclusion, not a diagonal approximation to the inverse. -/
theorem row_block_inverse_equal_coordinate_zero [Zero F] (I : Matrix ν ν F)
    (row col : ν → ℤ) (label : ν → α) (hlabel : Function.Injective label)
    (hI : I.BlockTriangular label)
    (hseparation : ∀ i j, label i < label j → row j < col i)
    (i j : ν) (hij : i ≠ j) (hcoord : row j = col i) : I i j = 0 := by
  rcases lt_trichotomy (label i) (label j) with hlt | he | hgt
  · have h := hseparation i j hlt
    rw [hcoord] at h
    exact (lt_irrefl _ h).elim
  · exact (hij (hlabel he)).elim
  · exact hI hgt

end SkewCornerDescent.Matrix
