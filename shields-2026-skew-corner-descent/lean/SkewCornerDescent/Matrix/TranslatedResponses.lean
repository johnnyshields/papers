/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OrderedResponses

/-!
# Complete responses on translated actual intervals

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`).

A common translation of every retained and removed endpoint preserves the entire original
response, including all normal-dependent off-diagonal inverse entries. Reindexing only
renames the actual removed occurrences; multiplicities are retained.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Translated complete endpoint lists identify the full removed matrix after reindexing. -/
theorem intervalMatrix_affine_reindex {ν μ : Type*} (e : ν ≃ μ)
    (row col : ν → ℤ) (row' col' : μ → ℤ) (d : ℤ)
    (hr : ∀ i, row' (e i) = row i + d) (hc : ∀ i, col' (e i) = col i + d) :
    (intervalMatrix row' col').submatrix e e = intervalMatrix row col := by
  ext i j
  simp only [Matrix.submatrix_apply, intervalMatrix, hr, hc, add_sub_add_right_eq_sub]

/-- Complete original responses agree under a common affine translation of their intervals. -/
theorem intervalResponse_affine_reindex {ν μ : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ]
    (e : ν ≃ μ) (x y x' y' d : ℤ) (row col : ν → ℤ) (row' col' : μ → ℤ)
    [Invertible (intervalMatrix row col)] [Invertible (intervalMatrix row' col')]
    (hx : x' = x + d) (hy : y' = y + d)
    (hr : ∀ i, row' (e i) = row i + d) (hc : ∀ i, col' (e i) = col i + d) :
    intervalResponse x' y' row' col' = intervalResponse x y row col := by
  have hM := intervalMatrix_affine_reindex e row col row' col' d hr hc
  have hInv : (intervalMatrix row' col')⁻¹.submatrix e e =
      (intervalMatrix row col)⁻¹ := by
    rw [← Matrix.inv_submatrix_equiv, hM]
  rw [intervalResponse_eq_sub_inverseContraction, intervalResponse_eq_sub_inverseContraction]
  have htop : x' - y' = x - y := by omega
  rw [htop]
  congr 1
  unfold inverseContraction
  apply Fintype.sum_equiv e.symm
  intro i
  apply Fintype.sum_equiv e.symm
  intro j
  have hc' := hc (e.symm i)
  have hr' := hr (e.symm j)
  have hentry := congrArg (fun A => A (e.symm i) (e.symm j)) hInv
  simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply] at hentry hc' hr'
  have hin : x' - col' i = x - col (e.symm i) := by omega
  have hout : row' j - y' = row (e.symm j) - y := by omega
  exact congrArg₂ (fun a b : actualField => a * b)
    (congrArg₂ (fun a b : actualField => a * b)
      (congrArg (fun z : ℤ => originalMap (hh z)) hin) hentry)
    (congrArg (fun z : ℤ => originalMap (hh z)) hout)

end SkewCornerDescent.Matrix
