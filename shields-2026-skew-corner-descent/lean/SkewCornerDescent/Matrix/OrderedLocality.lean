/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact locality of ordered removed inverses

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Restricting an ordered block inverse retains
all coupling entries inside the relevant block interval. No inverse is frozen or replaced
by its diagonal blocks. The actual component partition is a separate geometric obligation.
Sorry-free.
-/

open scoped Matrix

namespace SkewCornerDescent.Matrix

variable {ν α R : Type*} [Fintype ν] [DecidableEq ν] [LinearOrder α] [CommRing R]

/-- The complete double contraction by the removed inverse. -/
noncomputable def inverseContraction (r c : ν → R) (M : Matrix ν ν R) : R :=
  ∑ i, ∑ j, r i * M⁻¹ i j * c j

/-- When the outgoing endpoint vector vanishes outside an ordered prefix, its complete
inverse suffices. Triangularity excludes incoming positions outside the prefix. -/
theorem inverseContraction_prefix (r c : ν → R) (M : Matrix ν ν R)
    [Invertible M] (b : ν → α) (hM : M.BlockTriangular b) (k : α)
    (hc : ∀ i, ¬b i < k → c i = 0) :
    inverseContraction r c M = inverseContraction
      (fun i : {i : ν // b i < k} => r i.1) (fun i => c i.1)
      (M.toBlock (fun i => b i < k) (fun i => b i < k)) := by
  classical
  unfold inverseContraction
  apply Finset.sum_congr_set {i : ν | b i < k}
  · intro i hi
    apply Finset.sum_congr_set {j : ν | b j < k}
    · intro j hj
      have he := congrFun (congrFun (hM.inv_toBlock k) ⟨i, hi⟩) ⟨j, hj⟩
      change (M.toBlock (fun i => b i < k) (fun i => b i < k))⁻¹ ⟨i, hi⟩ ⟨j, hj⟩ =
        M⁻¹ i j at he
      rw [he]
    · intro j hj
      rw [hc j hj, mul_zero]
  · intro i hi
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : b j < k
    · have hi' : k ≤ b i := le_of_not_gt hi
      have hzero := Matrix.blockTriangular_inv_of_blockTriangular hM
        (lt_of_lt_of_le hj hi')
      rw [hzero, mul_zero, zero_mul]
    · rw [hc j hj, mul_zero]

/-- Reversing the two endpoint vectors transposes the complete inverse contraction. -/
theorem inverseContraction_transpose (r c : ν → R) (M : Matrix ν ν R) :
    inverseContraction r c M = inverseContraction c r Mᵀ := by
  unfold inverseContraction
  rw [← Matrix.transpose_nonsing_inv, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.transpose_apply]
  ring

/-- Suffix locality follows from the same ordered inverse theorem by transposition,
without discarding a coupling or changing its normal dependence. -/
theorem inverseContraction_suffix (r c : ν → R) (M : Matrix ν ν R)
    [Invertible M] (b : ν → α) (hM : M.BlockTriangular b) (k : α)
    (hr : ∀ i, ¬k < b i → r i = 0) :
    inverseContraction r c M = inverseContraction
      (fun i : {i : ν // k < b i} => r i.1) (fun i => c i.1)
      (M.toBlock (fun i => k < b i) (fun i => k < b i)) := by
  rw [inverseContraction_transpose]
  have h := inverseContraction_prefix c r Mᵀ
    (fun i => (OrderDual.toDual (b i))) hM.transpose (OrderDual.toDual k) hr
  rw [h]
  exact (inverseContraction_transpose _ _ _).symm

/-- Ordered path support restricts a full inverse contraction to exactly the blocks
between its endpoints. Only the incoming lower cutoff and outgoing upper cutoff are
required; triangularity supplies the other two restrictions. -/
theorem inverseContraction_interval (r c : ν → R) (M : Matrix ν ν R)
    [Invertible M] (b : ν → α) (hM : M.BlockTriangular b) (lo hi : α)
    (hr : ∀ i, ¬lo < b i → r i = 0) (hc : ∀ i, ¬b i < hi → c i = 0) :
    inverseContraction r c M = inverseContraction
      (fun i : {i : {i : ν // b i < hi} // lo < b i.1} => r i.1.1)
      (fun i => c i.1.1)
      ((M.toBlock (fun i => b i < hi) (fun i => b i < hi)).toBlock
        (fun i => lo < b i.1) (fun i => lo < b i.1)) := by
  classical
  rw [inverseContraction_prefix r c M b hM hi hc]
  let := hM.invertibleToBlock hi
  apply inverseContraction_suffix
    (fun i : {i : ν // b i < hi} => r i.1) (fun i => c i.1)
    (M.toBlock (fun i => b i < hi) (fun i => b i < hi))
    (fun i => b i.1) hM.submatrix lo
  intro i hi'
  exact hr i.1 hi'

/-- The ordered block interval, represented as a suffix of the relevant prefix. -/
abbrev OrderedIntervalIndex (b : ν → α) (lo hi : α) :=
  {i : {i : ν // b i < hi} // lo < b i.1}

/-- The interval inverse is produced from the full removed inverse and its ordering,
not carried as an independent invertibility assumption. -/
@[instance_reducible]
noncomputable def orderedIntervalInverse (M : Matrix ν ν R) [Invertible M]
    (b : ν → α) (hM : M.BlockTriangular b) (lo hi : α) :
    Invertible ((M.toBlock (fun i => b i < hi) (fun i => b i < hi)).toBlock
      (fun i => lo < b i.1) (fun i => lo < b i.1)) := by
  classical
  let := hM.invertibleToBlock hi
  have hP : (M.toBlock (fun i => b i < hi) (fun i => b i < hi)).BlockTriangular
      (fun i => b i.1) := hM.submatrix
  let inv := hP.transpose.invertibleToBlock (OrderDual.toDual lo)
  change Invertible ((M.toBlock (fun i => b i < hi) (fun i => b i < hi)).toBlock
    (fun i => lo < b i.1) (fun i => lo < b i.1))ᵀ at inv
  letI := inv
  exact Matrix.invertibleOfInvertibleTranspose _

end SkewCornerDescent.Matrix
