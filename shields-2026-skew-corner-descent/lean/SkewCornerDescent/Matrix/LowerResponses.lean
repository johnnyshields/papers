/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.IntervalMonicity
import Mathlib.LinearAlgebra.Matrix.BaseChange
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Lower-generator support of complete interval responses

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). An interval's full inverse correction
belongs to the rational subfield generated strictly below its retained top. No frozen
inverse or leading-residue replacement is made. The sharper lower-local denominator
bound still requires the ordered multi-component construction. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The rational subfield in generators strictly below the specified retained top. -/
noncomputable def lowerGeneratorField (K : ℕ+) : Subfield actualField :=
  Subfield.closure (Set.range (fun j : {j : ℕ+ // j < K} => originalMap (MvPolynomial.X j.1)))

/-- Increasing the allowed generator ceiling embeds the lower rational fields. -/
theorem lowerGeneratorField_mono {K L : ℕ+} (h : K ≤ L) :
    lowerGeneratorField K ≤ lowerGeneratorField L := by
  apply Subfield.closure_mono
  rintro z ⟨j, rfl⟩
  exact ⟨⟨j.1, lt_of_lt_of_le j.2 h⟩, rfl⟩

/-- Every actual entry below the retained top belongs to its lower rational subfield. -/
theorem hh_mem_lowerGeneratorField (K : ℕ+) (z : ℤ) (hz : z < (K : ℤ)) :
    originalMap (hh z) ∈ lowerGeneratorField K := by
  by_cases hn : z < 0
  · rw [hh_of_neg hn, map_zero]
    exact (lowerGeneratorField K).zero_mem
  by_cases h0 : z = 0
  · rw [h0, hh_zero, map_one]
    exact (lowerGeneratorField K).one_mem
  let j : ℕ+ := ⟨z.toNat, by omega⟩
  have hj : (j : ℤ) = z := Int.toNat_of_nonneg (by omega)
  have hjK : j < K := by change z.toNat < (K : ℕ); omega
  rw [← hj, hh_pnat]
  exact Subfield.subset_closure ⟨⟨j, hjK⟩, rfl⟩

/-- Inverting a complete block with lower entries introduces no larger generator. -/
theorem inverse_entries_mem_subfield {E ν : Type*} [Field E] [Fintype ν] [DecidableEq ν]
    (F : Subfield E) (P : Matrix ν ν E) [Invertible P]
    (hP : ∀ i j, P i j ∈ F) (i j : ν) : (⅟P) i j ∈ F := by
  exact Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right (Equiv.refl ν) F
    (mul_invOf_self P) hP i j

/-- The entire correction, not merely its residue, uses only generators below the top. -/
theorem intervalResponse_lower_correction {ν : Type*} [Fintype ν] [DecidableEq ν]
    (x y : ℤ) (row col : ν → ℤ) [Invertible (intervalMatrix row col)] (K : ℕ+)
    (hK : x - y = (K : ℤ)) (hr : ∀ i, row i < x) (hc : ∀ i, y < col i) :
    intervalResponse x y row col - originalMap (hh (x - y)) ∈ lowerGeneratorField K := by
  have hP (i j : ν) : intervalMatrix row col i j ∈ lowerGeneratorField K := by
    apply hh_mem_lowerGeneratorField
    have := hr i; have := hc j; omega
  have hi (i j : ν) := inverse_entries_mem_subfield (lowerGeneratorField K)
    (intervalMatrix row col) hP i j
  have hB (i : ν) : intervalIncoming x col () i ∈ lowerGeneratorField K := by
    apply hh_mem_lowerGeneratorField
    have := hc i; omega
  have hC (i : ν) : intervalOutgoing y row i () ∈ lowerGeneratorField K := by
    apply hh_mem_lowerGeneratorField
    have := hr i; omega
  change (originalMap (hh (x - y)) -
    (intervalIncoming x col * ⅟(intervalMatrix row col) * intervalOutgoing y row) () ()) -
    originalMap (hh (x - y)) ∈ lowerGeneratorField K
  rw [sub_sub_cancel_left]
  apply (lowerGeneratorField K).neg_mem
  rw [Matrix.mul_apply]
  apply (lowerGeneratorField K).sum_mem
  intro i _
  apply (lowerGeneratorField K).mul_mem _ (hC i)
  rw [Matrix.mul_apply]
  apply (lowerGeneratorField K).sum_mem
  intro j _
  exact (lowerGeneratorField K).mul_mem (hB j) (hi j i)

/-- An exact triangular response in its own retained top generator. This is a full-field
identity, with the complete inverse inside its lower correction. -/
theorem intervalResponse_triangular {ν : Type*} [Fintype ν] [DecidableEq ν]
    (x y : ℤ) (row col : ν → ℤ) [Invertible (intervalMatrix row col)] (K : ℕ+)
    (hK : x - y = (K : ℤ)) (hr : ∀ i, row i < x) (hc : ∀ i, y < col i) :
    ∃ A ∈ lowerGeneratorField K,
      intervalResponse x y row col = originalMap (MvPolynomial.X K) + A ∧
      generatorDeriv K (intervalResponse x y row col) = 1 := by
  refine ⟨intervalResponse x y row col - originalMap (hh (x - y)),
    intervalResponse_lower_correction x y row col K hK hr hc, ?_,
    generatorDeriv_intervalResponse_top x y row col K hK hr hc⟩
  rw [hK, hh_pnat]
  ring

end SkewCornerDescent.Matrix
