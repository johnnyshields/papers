/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.BetaDiagrams
import SkewJacobiNegative.PositiveEntries

/-!
# Actual first-variation polynomials and relation spaces

Formalizes `eq:unit-intro` and `lem:endpoint-cancellation` in
`sec:restoration` of `shields-2026-skew-cofactor-independence.tex`.
Return factors are strictly positive-entry values, whereas the underlying
Jacobi--Trudi matrix retains index-zero units.  Sorry-free.
-/

namespace SkewJacobiNegative

open scoped BigOperators
open StrictTriangularPaths

/-- Away from equality, suppressing index-zero units changes no complete entry. -/
theorem positiveGap_complete_of_ne {a b : ℤ} (hab : a ≠ b) :
    positiveGap complete a b = complete (a - b) := by
  by_cases h : b < a
  · exact positiveGap_of_lt complete h
  · have he : a < b := by omega
    rw [positiveGap_of_le complete he.le, complete_of_neg (by omega)]

namespace BetaDiagram

variable {n : ℕ}

/-- No beta entry is common to the row and column lists. -/
def ZeroFree (D : BetaDiagram n) : Prop := ∀ i j, D.row i ≠ D.col j

/-- Density supplies zero-freeness rather than exposing it as an extra hypothesis. -/
theorem Dense.zeroFree {D : BetaDiagram n} (hD : D.Dense) : D.ZeroFree :=
  fun i j => ne_of_gt (hD i j)

/-- The manuscript's signed cofactor is the transposed adjugate entry. -/
theorem cofactor_eq_adjugate (D : BetaDiagram (n + 1)) (i j : Fin (n + 1)) :
    D.cofactor i j = D.matrix.adjugate j i := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rfl

/-- Insertion of a single common beta at an arbitrary integer position. -/
noncomputable def unitVariation (D : BetaDiagram (n + 1)) (z : ℤ) : CompleteRing :=
  ∑ i, ∑ j, D.cofactor i j * positiveGap complete (D.row i) z *
    positiveGap complete z (D.col j)

/-- The exact finite set of available restoration positions. -/
noncomputable def availablePositions (D : BetaDiagram (n + 1)) : Finset ℤ :=
  (Finset.Ioo (D.col (Fin.last n)) (D.row 0)).filter
    (fun z => z ∉ Finset.univ.image D.row ∧ z ∉ Finset.univ.image D.col)

/-- The finite coordinate domain of the paper's first-variation kernel. -/
abbrev Available (D : BetaDiagram (n + 1)) := ↥D.availablePositions

/-- The actual linear relation map, with rational rather than polynomial coefficients. -/
noncomputable def unitRelationMap (D : BetaDiagram (n + 1)) :
    (D.Available → ℚ) →ₗ[ℚ] CompleteRing where
  toFun c := ∑ z, c z • D.unitVariation z.val
  map_add' := by
    intro c d
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    simp [smul_smul, Finset.smul_sum]

/-- The first-variation kernel is the kernel of the actual polynomial relation map. -/
noncomputable def unitKernel (D : BetaDiagram (n + 1)) :
    Submodule ℚ (D.Available → ℚ) := D.unitRelationMap.ker

/-- Membership has exactly the manuscript's rational unit-relation meaning. -/
theorem mem_unitKernel_iff (D : BetaDiagram (n + 1)) (c : D.Available → ℚ) :
    c ∈ D.unitKernel ↔ ∑ z, c z • D.unitVariation z.val = 0 := Iff.rfl

/-- At a row endpoint, the right return vector is the actual corresponding matrix row. -/
theorem row_endpoint_right (D : BetaDiagram (n + 1)) (hD : D.ZeroFree)
    (l j : Fin (n + 1)) :
    positiveGap complete (D.row l) (D.col j) = D.matrix l j :=
  positiveGap_complete_of_ne (hD l j)

/-- At a column endpoint, the left return vector is the actual corresponding matrix column. -/
theorem col_endpoint_left (D : BetaDiagram (n + 1)) (hD : D.ZeroFree)
    (i l : Fin (n + 1)) :
    positiveGap complete (D.row i) (D.col l) = D.matrix i l :=
  positiveGap_complete_of_ne (hD i l)

/-- The first-variation polynomial vanishes at every row beta endpoint. -/
theorem unitVariation_row_endpoint (D : BetaDiagram (n + 1)) (hD : D.ZeroFree)
    (l : Fin (n + 1)) : D.unitVariation (D.row l) = 0 := by
  classical
  unfold unitVariation
  simp_rw [cofactor_eq_adjugate, row_endpoint_right D hD]
  calc
    (∑ i, ∑ j, D.matrix.adjugate j i * positiveGap complete (D.row i) (D.row l) *
        D.matrix l j) =
        ∑ i, positiveGap complete (D.row i) (D.row l) *
          (D.matrix * D.matrix.adjugate) l i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = 0 := by
      rw [Matrix.mul_adjugate]
      simp [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, positiveGap_self]

/-- The first-variation polynomial vanishes at every column beta endpoint. -/
theorem unitVariation_col_endpoint (D : BetaDiagram (n + 1)) (hD : D.ZeroFree)
    (l : Fin (n + 1)) : D.unitVariation (D.col l) = 0 := by
  classical
  unfold unitVariation
  simp_rw [cofactor_eq_adjugate, col_endpoint_left D hD]
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, D.matrix.adjugate j i * D.matrix i l *
        positiveGap complete (D.col l) (D.col j)) =
        ∑ j, (D.matrix.adjugate * D.matrix) j l *
          positiveGap complete (D.col l) (D.col j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Matrix.mul_apply, Finset.sum_mul]
    _ = 0 := by
      rw [Matrix.adjugate_mul]
      simp [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_mul, positiveGap_self]

/-- All beta endpoints vanish, independent of connectedness or density. -/
theorem unitVariation_endpoint (D : BetaDiagram (n + 1)) (hD : D.ZeroFree) (z : ℤ)
    (hz : (∃ i, z = D.row i) ∨ ∃ j, z = D.col j) : D.unitVariation z = 0 := by
  rcases hz with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact D.unitVariation_row_endpoint hD i
  · exact D.unitVariation_col_endpoint hD j

end BetaDiagram
end SkewJacobiNegative
