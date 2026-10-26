/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.BlockResponse
import Mathlib.Tactic.Ring

/-!
# The full cofactor formula for an algebraic determinant derivative

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). Differentiation retains every original matrix entry and every
complete cofactor, including singular and empty matrices. No inverse of the
selected determinant is used. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

private theorem derivation_prod {ι R A : Type*}
    [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, D.map_one_eq_zero]
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Derivation.leibniz, ih, smul_eq_mul, smul_eq_mul,
      Finset.sum_insert hx, Finset.erase_insert hx]
    have hrest : (∑ i ∈ s, D (f i) * ∏ j ∈ (insert x s).erase i, f j) =
        f x * ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hxi : x ≠ i := fun h => hx (h.symm ▸ hi)
      rw [Finset.erase_insert_of_ne hxi,
        Finset.prod_insert (fun h => hx (Finset.mem_of_mem_erase h))]
      ring
    rw [hrest]
    ring

/-- Differentiating the complete determinant is the sum of determinants with
one differentiated original column. All terms of the permutation expansion remain. -/
theorem derivation_det_columns {ν R A : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (M : Matrix ν ν A) :
    D M.det = ∑ i, (M.updateCol i (fun j => D (M j i))).det := by
  classical
  have hconstant (z : ℤ) : D (z : A) = 0 := by
    simpa only [map_intCast] using D.map_algebraMap (z : R)
  have hprod (σ : Equiv.Perm ν) (i : ν) :
      (∏ j, (M.updateCol i (fun k => D (M k i))) (σ j) j) =
        D (M (σ i) i) * ∏ j ∈ Finset.univ.erase i, M (σ j) j := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => (M.updateCol i (fun k => D (M k i))) (σ j) j) (Finset.mem_univ i)]
    rw [Matrix.updateCol_apply, ite_eq_left rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Matrix.updateCol_apply, ite_eq_right (Finset.mem_erase.mp hj).1]
  rw [Matrix.det_apply', map_sum]
  simp_rw [Derivation.leibniz, hconstant, smul_zero, add_zero, smul_eq_mul,
    derivation_prod, Finset.mul_sum]
  simp_rw [Matrix.det_apply', hprod]
  rw [Finset.sum_comm]

/-- The algebraic derivative of a determinant is its full signed cofactor sum,
valid also at a singular selected component and at the empty-matrix boundary. -/
theorem derivation_det_cofactors {ν R A : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (M : Matrix ν ν A) :
    D M.det = ∑ i, ∑ j, M.adjugate j i * D (M i j) := by
  rw [derivation_det_columns]
  have hcolumn (j : ν) : (M.updateCol j (fun i => D (M i j))).det =
      ∑ i, M.adjugate j i * D (M i j) := by
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec]
    rfl
  simp_rw [hcolumn]
  rw [Finset.sum_comm]

end SkewCornerDescent.Matrix
