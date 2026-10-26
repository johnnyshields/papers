/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OrderedLocality

/-!
# Ordered locality of individual full endpoint-profile coefficients

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). A
complete incoming coefficient depends on the prefix through its own block;
a complete outgoing coefficient depends on the suffix through its own block.
All inverse couplings inside that prefix or suffix remain. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- The full incoming inverse coefficient uses exactly the prefix through its
original row, independently of the values in later incoming positions. -/
theorem incoming_inverse_prefix {ν α F : Type*}
    [Fintype ν] [DecidableEq ν] [LinearOrder α] [CommRing F]
    (r : ν → F) (M : Matrix ν ν F) [Invertible M]
    (b : ν → α) (hM : M.BlockTriangular b) (cut : α) (k : ν) (hk : b k < cut) :
    (∑ i, r i * M⁻¹ i k) =
      ∑ i : {i : ν // b i < cut}, r i.1 *
        (M.toBlock (fun i => b i < cut) (fun i => b i < cut))⁻¹ i ⟨k, hk⟩ := by
  classical
  apply Finset.sum_congr_set {i : ν | b i < cut}
  · intro i hi
    have he := congrFun (congrFun (hM.inv_toBlock cut) ⟨i, hi⟩) ⟨k, hk⟩
    change (M.toBlock (fun i => b i < cut) (fun i => b i < cut))⁻¹ ⟨i, hi⟩ ⟨k, hk⟩ =
      M⁻¹ i k at he
    rw [he]
  · intro i hi
    have hki : b k < b i := lt_of_lt_of_le hk (le_of_not_gt hi)
    rw [Matrix.blockTriangular_inv_of_blockTriangular hM hki, mul_zero]

/-- The symmetric full outgoing inverse coefficient uses the complete suffix
through its own block, not only the block-diagonal inverse. -/
theorem outgoing_inverse_suffix {ν α F : Type*}
    [Fintype ν] [DecidableEq ν] [LinearOrder α] [CommRing F]
    (c : ν → F) (M : Matrix ν ν F) [Invertible M]
    (b : ν → α) (hM : M.BlockTriangular b) (cut : α) (k : ν) (hk : cut < b k) :
    (∑ j, M⁻¹ k j * c j) =
      ∑ j : {j : ν // cut < b j},
        (M.toBlock (fun i => cut < b i) (fun i => cut < b i))⁻¹ ⟨k, hk⟩ j * c j.1 := by
  have h := incoming_inverse_prefix c (Matrix.transpose M) (fun i => OrderDual.toDual (b i))
    hM.transpose (OrderDual.toDual cut) k hk
  change (∑ i, c i * (Matrix.transpose M)⁻¹ i k) =
    ∑ i : {i : ν // cut < b i}, c i.1 *
      (Matrix.transpose (M.toBlock (fun i => cut < b i) (fun i => cut < b i)))⁻¹
        i ⟨k, hk⟩ at h
  simpa only [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply, mul_comm] using h

end SkewCornerDescent.Matrix
