-- TODO-COPIED: skew-cofactor-independence/lean/SkewCofactorIndependence/OrdinaryReadings.lean
/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.WeightedReadings
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Ordinary degree and row-count recovery

Formalizes the ordinary-degree reading of `lem:polynomial-readings` in
`sec:boundary` of `shields-2026-skew-cofactor-independence.tex`.  A surviving
coefficient-one diagonal monomial supplies the lower bound; the full
permutation expansion supplies the upper bound.  Sorry-free.
-/

namespace SkewCofactorIndependence

open scoped BigOperators

/-- Every complete entry has ordinary degree at most one, including its zero/unit conventions. -/
theorem complete_totalDegree_le_one (k : ℤ) : (complete k).totalDegree ≤ 1 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · simp [complete_of_neg hk]
  · subst k
    simp
  · rw [complete_of_pos hk]
    exact (MvPolynomial.totalDegree_X (⟨k.toNat, by omega⟩ : ℕ+)).le

set_option backward.isDefEq.respectTransparency false in
/-- A list of positive generator indices records exactly one exponent per list entry. -/
theorem exponentVector_degree_of_pos (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    Finsupp.degree (Base.exponentVector l) = l.length := by
  classical
  induction l with
  | nil => simp [Base.exponentVector]
  | cons k l ih =>
    have hk : 0 < k := hl k (by simp)
    have ht : ∀ j ∈ l, 0 < j := fun j hj => hl j (by simp [hj])
    change Finsupp.degree (Base.completeIndexExponent k + Base.exponentVector l) = _
    rw [map_add, ih ht]
    have he : Base.completeIndexExponent k = Finsupp.single (⟨k, hk⟩ : ℕ+) 1 := by
      simp only [Base.completeIndexExponent, dite_eq_left hk]
    rw [he, Finsupp.degree_single]
    simp only [List.length_cons]
    omega

namespace BetaDiagram

variable {n m : ℕ}

/-- The initial component's unit coefficient is a coefficient of the actual determinant. -/
theorem diagonal_coefficient_one (D : BetaDiagram n) :
    D.schur.coeff D.diagonalExponent = 1 := by
  have h := D.square_initial_coefficient
  rw [Base.initialForm, MvPolynomial.coeff_weightedHomogeneousComponent] at h
  split_ifs at h with hd
  · exact h
  · norm_num at h

/-- Every diagonal index is strictly positive, with no omitted index-zero factor. -/
theorem rowLengthList_positive (D : BetaDiagram n) :
    ∀ k ∈ (List.ofFn fun i => (D.rowLength i).toNat), 0 < k := by
  intro k hk
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hk
  rw [← hi]
  have h := D.rowLength_pos i
  omega

/-- The exponent count of the actual leading row monomial is the row count. -/
theorem diagonalExponent_degree (D : BetaDiagram n) :
    Finsupp.degree D.diagonalExponent = n := by
  rw [diagonalExponent_eq_rowLengths,
    exponentVector_degree_of_pos _ D.rowLengthList_positive, List.length_ofFn]

/-- No determinant term can have more ordinary factors than the number of rows. -/
theorem schur_totalDegree_le (D : BetaDiagram n) : D.schur.totalDegree ≤ n := by
  classical
  unfold schur
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  change (((Equiv.Perm.sign σ : ℤ) •
    ∏ i, complete (D.row i - D.col (σ i)))).totalDegree ≤ n
  apply (MvPolynomial.totalDegree_smul_le (Equiv.Perm.sign σ : ℤ) _).trans
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  calc
    (∑ i, (complete (D.row i - D.col (σ i))).totalDegree) ≤ ∑ _ : Fin n, 1 :=
      Finset.sum_le_sum (fun i _ => complete_totalDegree_le_one _)
    _ = n := by simp

/-- The coefficient-one diagonal really attains ordinary degree equal to the row count. -/
theorem schur_totalDegree (D : BetaDiagram n) : D.schur.totalDegree = n := by
  apply le_antisymm D.schur_totalDegree_le
  have hc : D.diagonalExponent ∈ D.schur.support := by
    rw [MvPolynomial.mem_support_iff, D.diagonal_coefficient_one]
    norm_num
  have h := MvPolynomial.le_totalDegree hc
  change Finsupp.degree D.diagonalExponent ≤ D.schur.totalDegree at h
  rw [D.diagonalExponent_degree] at h
  exact h

/-- Equality of actual polynomial observations supplies the row-count identification. -/
theorem row_count_of_schur_eq (D : BetaDiagram n) (E : BetaDiagram m)
    (h : D.schur = E.schur) : n = m := by
  have hd := congrArg MvPolynomial.totalDegree h
  simpa only [schur_totalDegree] using hd

end BetaDiagram
end SkewCofactorIndependence
