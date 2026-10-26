/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# One zero column in a singular common core

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`). A produced kernel
vector supplies one invertible column change. Its determinant is a nonzero vector
coordinate; no rank or proper-minor invertibility hypothesis is carried. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- A singular core can be changed to have a zero column at any chosen index by a
produced invertible column transformation.

**Differs from the paper's route.** A kernel vector and an identity-column replacement
replace inversion of a common proper minor. -/
theorem singularCore_zero_column_at {F ν : Type*} [Field F] [Fintype ν] [DecidableEq ν]
    (C : Matrix ν ν F) (hC : C.det = 0) (i₀ : ν) :
    ∃ P : Matrix ν ν F, P.det ≠ 0 ∧ ∀ i, (C * P) i i₀ = 0 := by
  classical
  obtain ⟨v, hv, hCv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hC
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  let P := (1 : Matrix ν ν F).updateCol j v
  have hcol : (fun k => ∑ i, v i • (1 : Matrix ν ν F) k i) = v := by
    funext k
    simp [Matrix.one_apply, smul_eq_mul]
  have hd : P.det = v j := by
    have he := Matrix.det_updateCol_sum (1 : Matrix ν ν F) j v
    rw [hcol, Matrix.det_one, smul_eq_mul, mul_one] at he
    exact he
  let σ := Equiv.swap i₀ j
  refine ⟨P.submatrix id σ, ?_, ?_⟩
  · rw [Matrix.det_permute', hd]
    apply mul_ne_zero
    · rcases Int.isUnit_iff.mp (Equiv.Perm.sign σ).isUnit with h | h <;> norm_num [h]
    · exact hj
  · intro i
    have he := congrFun hCv i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, P, σ, Matrix.updateCol_apply] using he

end SkewCornerDescent.Matrix
