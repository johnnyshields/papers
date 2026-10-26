/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OrderedLocality
import SkewCornerDescent.Matrix.ProtectedGenerator

/-!
# Complete responses on ordered removed intervals

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Endpoint support restricts the entire
removed inverse to the intervening blocks, and the resulting response is monic in its
geometric top. The actual source component partition and the cap endpoint arithmetic
remain separate geometric obligations. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

variable {ν α : Type*} [Fintype ν] [DecidableEq ν] [LinearOrder α]

/-- Expand the actual complete response as a double inverse contraction. -/
theorem intervalResponse_eq_sub_inverseContraction (x y : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] :
    intervalResponse x y row col = originalMap (hh (x - y)) -
      inverseContraction (fun i => originalMap (hh (x - col i)))
        (fun i => originalMap (hh (row i - y))) (intervalMatrix row col) := by
  unfold intervalResponse retainedResponse inverseContraction
  change originalMap (hh (x - y)) -
    (intervalIncoming x col * ⅟(intervalMatrix row col) * intervalOutgoing y row) () () = _
  simp only [Matrix.mul_apply, Matrix.invOf_eq_nonsing_inv,
    intervalIncoming, intervalOutgoing, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The complete interval inverse is supplied by the full ordered removed matrix. -/
@[instance_reducible]
noncomputable def orderedResponseInverse (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] (b : ν → α)
    (hM : (intervalMatrix row col).BlockTriangular b) (lo hi : α) :
    Invertible (intervalMatrix
      (fun i : OrderedIntervalIndex b lo hi => row i.1.1) (fun i => col i.1.1)) :=
  orderedIntervalInverse (intervalMatrix row col) b hM lo hi

/-- The actual full inverse response equals its ordered interval response. Outside
blocks vanish by endpoint support, not by replacing their inverse with a diagonal one. -/
theorem intervalResponse_ordered_restriction (x y : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] (b : ν → α)
    (hM : (intervalMatrix row col).BlockTriangular b) (lo hi : α)
    (hin : ∀ i, ¬lo < b i → x < col i) (hout : ∀ i, ¬b i < hi → row i < y) :
    letI := orderedResponseInverse row col b hM lo hi
    intervalResponse x y row col = intervalResponse x y
      (fun i : OrderedIntervalIndex b lo hi => row i.1.1) (fun i => col i.1.1) := by
  classical
  let := orderedResponseInverse row col b hM lo hi
  rw [intervalResponse_eq_sub_inverseContraction, intervalResponse_eq_sub_inverseContraction]
  congr 1
  apply inverseContraction_interval _ _ _ b hM lo hi
  · intro i hi'
    rw [hh_of_neg (by have := hin i hi'; omega), map_zero]
  · intro i hi'
    rw [hh_of_neg (by have := hout i hi'; omega), map_zero]

/-- Exact monicity of the full original response follows from ordered path support.
The entire normal-dependent inverse remains in the lower correction. -/
theorem ordered_intervalResponse_triangular (x y : ℤ) (row col : ν → ℤ)
    [Invertible (intervalMatrix row col)] (b : ν → α)
    (hM : (intervalMatrix row col).BlockTriangular b) (lo hi : α)
    (hin : ∀ i, ¬lo < b i → x < col i) (hout : ∀ i, ¬b i < hi → row i < y)
    (hr : ∀ i : OrderedIntervalIndex b lo hi, row i.1.1 < x)
    (hc : ∀ i : OrderedIntervalIndex b lo hi, y < col i.1.1)
    (K : ℕ+) (hK : x - y = (K : ℤ)) :
    ∃ A ∈ lowerGeneratorField K,
      intervalResponse x y row col = originalMap (MvPolynomial.X K) + A ∧
      generatorDeriv K (intervalResponse x y row col) = 1 := by
  classical
  let := orderedResponseInverse row col b hM lo hi
  rw [intervalResponse_ordered_restriction x y row col b hM lo hi hin hout]
  exact intervalResponse_triangular x y _ _ K hK hr hc

end SkewCornerDescent.Matrix
