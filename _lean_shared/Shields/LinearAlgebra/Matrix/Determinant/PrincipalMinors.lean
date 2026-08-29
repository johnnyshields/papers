/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The principal-minor expansion of `det(1 + \xi M)`

For a square matrix `M` over a commutative ring,

\[
  \det(1+\xi M)=\sum_{r}\xi^{r}\sum_{|S|=r}\det M_{S},
\]

the inner sum running over the principal minors of size `r`.  Mathlib has the Weinstein–Aronszajn
identity `Matrix.det_one_add_mul_comm` but not this expansion, which is the statement that the
characteristic polynomial's coefficients *are* the sums of principal minors.

`Shields.minorGen` packages the right-hand side as a polynomial of degree at most the size, so the
expansion is an evaluation rather than a sum manipulation at the point of use.  Two small
determinant vanishing lemmas travel with it: a matrix with one row (or column) a scalar multiple of
another is singular.

## Main results

* `Shields.minorGen`, `Shields.minorGen_coeff`, `Shields.minorGen_eval`,
  `Shields.minorGen_natDegree_le`
* `Shields.det_one_add_smul_eq_sum_principal` — **the expansion**
* `Shields.det_eq_zero_of_row_eq_smul`, `Shields.det_eq_zero_of_col_eq_smul`

## Tags

determinant, principal minor, characteristic polynomial, weinstein aronszajn
-/

open Finset Matrix Polynomial

namespace Shields

variable {R : Type*} [CommRing R] {m : ℕ}

/-- `det(1 + X M)`, whose `r`-th coefficient is the sum of the `r × r` principal minors
of `M`. -/
noncomputable def minorGen (M : Matrix (Fin m) (Fin m) R) : Polynomial R :=
  Matrix.det (1 + (Polynomial.X : Polynomial R) • M.map Polynomial.C)

theorem minorGen_coeff (M : Matrix (Fin m) (Fin m) R) (r : ℕ) :
    (minorGen M).coeff r
      = ∑ s ∈ Finset.univ.powersetCard r,
          (M.submatrix (Subtype.val : s → Fin m) Subtype.val).det :=
  Matrix.coeff_det_one_add_X_smul_eq_sum_minors M r

theorem minorGen_eval (M : Matrix (Fin m) (Fin m) R) (ξ : R) :
    (minorGen M).eval ξ = (1 + ξ • M).det := by
  rw [minorGen, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h] <;> ring

theorem minorGen_natDegree_le (M : Matrix (Fin m) (Fin m) R) : (minorGen M).natDegree ≤ m := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun r hr => ?_
  rw [minorGen_coeff, Finset.powersetCard_eq_empty.mpr (by simpa using hr), Finset.sum_empty]

/-- **The principal-minor expansion.**  The expansion
`det(Id_m + ξ M) = ∑_J ξ^{|J|} det M[J,J]`, the sum over all subsets of the index set. -/
theorem det_one_add_smul_eq_sum_principal (M : Matrix (Fin m) (Fin m) R) (ξ : R) :
    (1 + ξ • M).det
      = ∑ s : Finset (Fin m), ξ ^ s.card *
          (M.submatrix (Subtype.val : s → Fin m) Subtype.val).det := by
  rw [← minorGen_eval M ξ,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (minorGen_natDegree_le M)) ξ,
    ← Finset.powerset_univ, Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [minorGen_coeff, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s hs => by
    rw [(Finset.mem_powersetCard.mp hs).2, mul_comm]

/-- A matrix with one row a scalar multiple of another has vanishing determinant. -/
theorem det_eq_zero_of_row_eq_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) R) {i i' : Fin n}
    (hne : i ≠ i') (c : R) (h : M i = c • M i') : M.det = 0 := by
  have h1 : M.updateRow i (c • M i') = M := by rw [← h, Matrix.updateRow_eq_self]
  have h2 : (M.updateRow i (M i')).det = 0 := by
    refine Matrix.det_zero_of_row_eq hne ?_
    rw [Matrix.updateRow_self, Matrix.updateRow_ne (Ne.symm hne)]
  rw [← h1, Matrix.det_updateRow_smul, h2, mul_zero]

/-- A matrix with one column a scalar multiple of another has vanishing determinant. -/
theorem det_eq_zero_of_col_eq_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) R) {j j' : Fin n}
    (hne : j ≠ j') (c : R) (h : ∀ i, M i j = c * M i j') : M.det = 0 := by
  rw [← Matrix.det_transpose]
  refine det_eq_zero_of_row_eq_smul _ hne c ?_
  funext i
  simpa [Matrix.transpose_apply, smul_eq_mul] using h i


/-! ### Axiom footprint -/

/-- info: 'Shields.det_one_add_smul_eq_sum_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_one_add_smul_eq_sum_principal

/-- info: 'Shields.det_eq_zero_of_col_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_eq_zero_of_col_eq_smul

end Shields
