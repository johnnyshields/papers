/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.HomogeneousIrreducibility
import SkewJacobiNegative.NegativeBoards
import Mathlib.GroupTheory.Perm.Fin

/-!
# One opened matrix position

The opening inventory and the full-order expansion in `sec:five-base`,
`eq:five-open-decomposition` of `shields-2026-skew-jacobi-negative.tex`.
All support conditions are derived from the actual beta inequalities.
The opened label can be zero.  Zeroing a position never specializes a variable.
The permutation sums collect repeated monomials automatically; neither layer
is claimed to be invariant under Schur equality.
-/

namespace SkewJacobiNegative

open Finset MvPolynomial

namespace FiveOpening

/-- Zero-based positions `(2,0)`, `(3,1)`, `(4,2)`. -/
def openedRow (k : Fin 3) : Fin 5 := ⟨k.val + 2, by omega⟩
def openedCol (k : Fin 3) : Fin 5 := ⟨k.val, by omega⟩

/-- The genuine negative pattern; this is a proposition about original labels. -/
def HasOpening (D : BetaDiagram 5) (k : Fin 3) : Prop :=
  ∀ i j : Fin 5, D.row i < D.col j ↔
    j.val + 1 < i.val ∧ ¬ (i = openedRow k ∧ j = openedCol k)

/-- Five negatives exhaust all but one of the six possible negative positions. -/
theorem opening_inventory (D : BetaDiagram 5) (hD : D.Connected)
    (hν : negativeCount D = 5) : ∃ k : Fin 3, HasOpening D k := by
  have hsum := D.negativeCount_eq_sum
  rw [hν] at hsum
  simp [Fin.sum_univ_succ] at hsum
  change 5 = negativeRowCount D 0 + (negativeRowCount D 1 +
    (negativeRowCount D 2 + (negativeRowCount D 3 + negativeRowCount D 4))) at hsum
  have h0 := D.connected_negativeRowCount_le hD (0 : Fin 5)
  have h1 := D.connected_negativeRowCount_le hD (1 : Fin 5)
  have h2 := D.connected_negativeRowCount_le hD (2 : Fin 5)
  have h3 := D.connected_negativeRowCount_le hD (3 : Fin 5)
  have h4 := D.connected_negativeRowCount_le hD (4 : Fin 5)
  norm_num at h0 h1 h2 h3 h4
  have hcases :
      (negativeRowCount D 2 = 0 ∧ negativeRowCount D 3 = 2 ∧ negativeRowCount D 4 = 3) ∨
      (negativeRowCount D 2 = 1 ∧ negativeRowCount D 3 = 1 ∧ negativeRowCount D 4 = 3) ∨
      (negativeRowCount D 2 = 1 ∧ negativeRowCount D 3 = 2 ∧ negativeRowCount D 4 = 2) := by
    omega
  rcases hcases with h | h | h
  · refine ⟨0, ?_⟩
    intro i j
    rw [D.negative_iff_lt_rowCount]
    fin_cases i <;> fin_cases j <;> simp [openedRow, openedCol] <;> omega
  · refine ⟨1, ?_⟩
    intro i j
    rw [D.negative_iff_lt_rowCount]
    fin_cases i <;> fin_cases j <;> simp [openedRow, openedCol] <;> omega
  · refine ⟨2, ?_⟩
    intro i j
    rw [D.negative_iff_lt_rowCount]
    fin_cases i <;> fin_cases j <;> simp [openedRow, openedCol] <;> omega

/-- The nonnegative index of the one original position, not a renamed label. -/
def openingLabel (D : BetaDiagram 5) (k : Fin 3) : ℤ :=
  D.row (openedRow k) - D.col (openedCol k)

theorem openingLabel_nonneg (D : BetaDiagram 5) {k : Fin 3} (h : HasOpening D k) :
    0 ≤ openingLabel D k := by
  have hh : ¬ D.row (openedRow k) < D.col (openedCol k) := by
    intro hn
    exact (h (openedRow k) (openedCol k)).mp hn |>.2 ⟨rfl, rfl⟩
  dsimp [openingLabel]
  omega

/-- Literal single-position zeroing.  All other occurrences of the label survive. -/
noncomputable def zeroPosition {R : Type*} [Zero R]
    (A : Matrix (Fin 5) (Fin 5) R) (i j : Fin 5) : Matrix (Fin 5) (Fin 5) R :=
  A.updateRow i (Function.update (A i) j 0)

@[simp] theorem zeroPosition_apply {R : Type*} [Zero R]
    (A : Matrix (Fin 5) (Fin 5) R) (i j a b : Fin 5) :
    zeroPosition A i j a b = if a = i ∧ b = j then 0 else A a b := by
  by_cases ha : a = i <;> by_cases hb : b = j <;>
    simp [zeroPosition, Matrix.updateRow_apply, Function.update_apply, ha, hb]

/-- The manuscript's `A⁽⁰⁾`. -/
noncomputable def closedMatrix (D : BetaDiagram 5) (k : Fin 3) :=
  zeroPosition D.homMatrix (openedRow k) (openedCol k)

/-- The signed complementary determinant of the matrix with that one site zeroed. -/
noncomputable def openedCofactor (D : BetaDiagram 5) (k : Fin 3) : Gluing.HomLambda :=
  (-1) ^ ((openedRow k).val + (openedCol k).val) *
    ((closedMatrix D k).submatrix (openedRow k).succAbove (openedCol k).succAbove).det

/-- Position multilinearity, valid even if the opened generator occurs elsewhere. -/
theorem det_zeroPosition {R : Type*} [CommRing R]
    (A : Matrix (Fin 5) (Fin 5) R) (i j : Fin 5) :
    A.det = (zeroPosition A i j).det + A i j *
      ((-1) ^ (i.val + j.val) * (A.submatrix i.succAbove j.succAbove).det) := by
  classical
  have hm (l : Fin 5) :
      (zeroPosition A i j).submatrix i.succAbove l.succAbove =
        A.submatrix i.succAbove l.succAbove := by
    simp [zeroPosition, Matrix.submatrix_updateRow_succAbove]
  rw [Matrix.det_succ_row A i, Matrix.det_succ_row (zeroPosition A i j) i]
  simp only [hm, zeroPosition_apply, eq_self_iff_true, true_and]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j)]
  simp only [ite_true, mul_zero, zero_mul, zero_add]
  have hs :
      (∑ x ∈ univ \ {j}, (-1 : R) ^ (i.val + x.val) * A i x *
        (A.submatrix i.succAbove x.succAbove).det) =
      ∑ x ∈ univ \ {j}, (-1 : R) ^ (i.val + x.val) * (if x = j then 0 else A i x) *
        (A.submatrix i.succAbove x.succAbove).det := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ j := by simpa using (Finset.mem_sdiff.mp hx).2
    rw [if_neg hne]
  rw [← hs]
  ring

/-- The exact displayed decomposition, retaining `H₀`. -/
theorem open_decomposition (D : BetaDiagram 5) (k : Fin 3) :
    D.homSchur = (closedMatrix D k).det +
      Gluing.hTilde (openingLabel D k) * openedCofactor D k := by
  have h := det_zeroPosition D.homMatrix (openedRow k) (openedCol k)
  simpa [BetaDiagram.homSchur, closedMatrix, openedCofactor, openingLabel,
    BetaDiagram.homMatrix, zeroPosition, Matrix.submatrix_updateRow_succAbove] using h

/-- Every other position is unchanged, even when its generator equals the opened one. -/
theorem closedMatrix_other (D : BetaDiagram 5) (k : Fin 3) (i j : Fin 5)
    (h : ¬ (i = openedRow k ∧ j = openedCol k)) :
    closedMatrix D k i j = Gluing.hTilde (D.row i - D.col j) := by
  simp [closedMatrix, zeroPosition_apply, h, BetaDiagram.homMatrix]

/-- An original unit opening is multiplied by the independent generator `H₀`, not by one. -/
theorem unit_open_decomposition (D : BetaDiagram 5) (k : Fin 3)
    (hτ : openingLabel D k = 0) :
    D.homSchur = (closedMatrix D k).det + (X 0 : Gluing.HomLambda) * openedCofactor D k := by
  simpa [hτ, Gluing.hTilde] using open_decomposition D k

/-- The sixteen interval permutations are exactly the upper-Hessenberg matchings. -/
def intervalPermutations : Finset (Equiv.Perm (Fin 5)) :=
  univ.filter fun σ => ∀ i : Fin 5, i.val ≤ (σ i).val + 1

/-- Supported permutations of the genuinely deleted four-by-four board. -/
def cofactorPermutations (k : Fin 3) : Finset (Equiv.Perm (Fin 4)) :=
  univ.filter fun σ => ∀ i : Fin 4,
    ((openedRow k).succAbove i).val ≤ ((openedCol k).succAbove (σ i)).val + 1

/-- Supported terms of the full five-by-five determinant. -/
def fullPermutations (k : Fin 3) : Finset (Equiv.Perm (Fin 5)) :=
  univ.filter fun σ => ∀ i : Fin 5,
    i.val ≤ (σ i).val + 1 ∨ (i = openedRow k ∧ σ i = openedCol k)

private theorem hTilde_ne_zero_iff (j : ℤ) : Gluing.hTilde j ≠ 0 ↔ 0 ≤ j := by
  by_cases hj : j < 0
  · simp [Gluing.hTilde, hj] <;> omega
  · simp [Gluing.hTilde, hj, X_ne_zero] <;> omega

/-- Symbolic matrix support, independent of numerical beta ranges. -/
theorem homMatrix_support (D : BetaDiagram 5) {k : Fin 3} (h : HasOpening D k)
    (i j : Fin 5) : D.homMatrix i j ≠ 0 ↔
      i.val ≤ j.val + 1 ∨ (i = openedRow k ∧ j = openedCol k) := by
  rw [BetaDiagram.homMatrix, Matrix.of_apply, hTilde_ne_zero_iff]
  have hh := h i j
  omega

/-- Removing the opening gives precisely the usual Hessenberg support. -/
theorem closedMatrix_support (D : BetaDiagram 5) {k : Fin 3} (h : HasOpening D k)
    (i j : Fin 5) : closedMatrix D k i j ≠ 0 ↔ i.val ≤ j.val + 1 := by
  rw [closedMatrix, zeroPosition_apply]
  by_cases hij : i = openedRow k ∧ j = openedCol k
  · rcases hij with ⟨rfl, rfl⟩
    simp [openedRow, openedCol]
  · rw [if_neg hij, homMatrix_support D h]
    simp [hij]

/-- Exact symbolic support of the complementary matrix. -/
theorem cofactorMatrix_support (D : BetaDiagram 5) {k : Fin 3} (h : HasOpening D k)
    (i j : Fin 4) :
    (closedMatrix D k).submatrix (openedRow k).succAbove (openedCol k).succAbove i j ≠ 0 ↔
      ((openedRow k).succAbove i).val ≤ ((openedCol k).succAbove j).val + 1 :=
  closedMatrix_support D h _ _

/-- The signed sum for any matrix, restricted to its actual support. -/
theorem det_supported {n : ℕ} {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (A : Matrix (Fin n) (Fin n) R) (s : Finset (Equiv.Perm (Fin n)))
    (hs : ∀ σ, σ ∈ s ↔ ∀ i, A i (σ i) ≠ 0) :
    A.det = ∑ σ ∈ s, (Equiv.Perm.sign σ : ℤ) • ∏ i, A i (σ i) := by
  classical
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook]
  simp only [Units.smul_def]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro σ _ hσ
  have hh : ¬ ∀ i, A i (σ i) ≠ 0 := by simpa [hs σ] using hσ
  push_neg at hh
  obtain ⟨i, hi⟩ := hh
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, smul_zero]

/-- The sixteen interval terms, as actual signed products of beta labels. -/
theorem closed_det_expansion (D : BetaDiagram 5) {k : Fin 3} (h : HasOpening D k) :
    (closedMatrix D k).det = ∑ σ ∈ intervalPermutations,
      (Equiv.Perm.sign σ : ℤ) • ∏ i : Fin 5, closedMatrix D k i (σ i) := by
  apply det_supported
  intro σ
  simp only [intervalPermutations, Finset.mem_filter, Finset.mem_univ, true_and,
    closedMatrix_support D h]

/-- The eight terms are supported products of the actual deleted matrix. -/
theorem cofactor_det_expansion (D : BetaDiagram 5) {k : Fin 3} (h : HasOpening D k) :
    openedCofactor D k = (-1) ^ ((openedRow k).val + (openedCol k).val) *
      ∑ σ ∈ cofactorPermutations k, (Equiv.Perm.sign σ : ℤ) •
        ∏ i : Fin 4, closedMatrix D k ((openedRow k).succAbove i)
          ((openedCol k).succAbove (σ i)) := by
  unfold openedCofactor
  congr 1
  apply det_supported
  intro σ
  simp only [cofactorPermutations, Finset.mem_filter, Finset.mem_univ, true_and,
    cofactorMatrix_support D h]

/-- The full expansion is a single signed sum, prior to any monomial collection. -/
theorem full_det_expansion (D : BetaDiagram 5) {k : Fin 3} (h : HasOpening D k) :
    D.homSchur = ∑ σ ∈ fullPermutations k,
      (Equiv.Perm.sign σ : ℤ) • ∏ i : Fin 5, Gluing.hTilde (D.row i - D.col (σ i)) := by
  unfold BetaDiagram.homSchur
  apply det_supported
  intro σ
  simp only [fullPermutations, Finset.mem_filter, Finset.mem_univ, true_and,
    homMatrix_support D h]

/-- The bit mask records which of the four adjacent edges are joined. -/
def joinedEdges (m : Fin 16) : Finset (Fin 4) :=
  univ.filter fun e => m.val / (2 ^ e.val) % 2 = 1

/-- Maximal consecutive intervals after joining precisely the selected edges. -/
def intervalBlocks (m : Fin 16) : Finset (Fin 5 × Fin 5) :=
  univ.filter fun p =>
    p.1 ≤ p.2 ∧
    (p.1.val = 0 ∨ ∀ e ∈ joinedEdges m, e.val + 1 ≠ p.1.val) ∧
    (p.2.val = 4 ∨ ∀ e ∈ joinedEdges m, e.val ≠ p.2.val) ∧
    (∀ e : Fin 4, p.1.val ≤ e.val → e.val < p.2.val → e ∈ joinedEdges m)

/-- An interval's beta label, before any collection of equal generators. -/
def intervalLabel (D : BetaDiagram 5) (a b : Fin 5) : ℤ := D.row a - D.col b

/-- The manuscript's sum of row lengths minus internal overlaps is the same label. -/
theorem intervalLabel_eq_rows_sub_overlaps (D : BetaDiagram 5) (a b : Fin 5) (hab : a ≤ b) :
    intervalLabel D a b =
      (∑ i ∈ univ.filter (fun i : Fin 5 => a ≤ i ∧ i ≤ b), D.rowLength i) -
      ∑ e ∈ univ.filter (fun e : Fin 4 => a.val ≤ e.val ∧ e.val < b.val),
        (D.row (⟨e.val + 1, by omega⟩ : Fin 5) - D.col (⟨e.val, by omega⟩ : Fin 5)) := by
  simp only [Finset.sum_filter]
  fin_cases a <;> fin_cases b <;> norm_num at hab <;>
    norm_num [intervalLabel, BetaDiagram.rowLength, Fin.sum_univ_succ] <;> ring

/-- One of the sixteen signed interval terms, with no substitution of `H₀`. -/
noncomputable def intervalTerm (D : BetaDiagram 5) (m : Fin 16) : Gluing.HomLambda :=
  (-1) ^ (joinedEdges m).card *
    (∏ e ∈ joinedEdges m,
      Gluing.hTilde (D.row (⟨e.val + 1, by omega⟩ : Fin 5) -
        D.col (⟨e.val, by omega⟩ : Fin 5))) *
    ∏ p ∈ intervalBlocks m, Gluing.hTilde (intervalLabel D p.1 p.2)

/-- The position-zeroed matrix is the actual upper-Hessenberg beta matrix. -/
theorem closedMatrix_eq_band (D : BetaDiagram 5) {k : Fin 3} (h : HasOpening D k) :
    closedMatrix D k = Matrix.of fun i j : Fin 5 =>
      if i.val ≤ j.val + 1 then Gluing.hTilde (D.row i - D.col j) else 0 := by
  ext i j
  by_cases hij : i.val ≤ j.val + 1
  · have hne : ¬ (i = openedRow k ∧ j = openedCol k) := by
      rintro ⟨rfl, rfl⟩
      dsimp [openedRow, openedCol] at hij
      omega
    simp [closedMatrix, zeroPosition_apply, hne, hij, BetaDiagram.homMatrix]
  · have hz := (closedMatrix_support D h i j).not.mpr hij
    simp only [not_not] at hz
    simp [Matrix.of_apply, hij, hz]

private def joinedEdgesTable : Fin 16 → Finset (Fin 4) :=
  ![∅, {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2},
    {3}, {0, 3}, {1, 3}, {0, 1, 3}, {2, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}]

private def intervalBlocksTable : Fin 16 → Finset (Fin 5 × Fin 5) :=
  ![{(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)},
    {(0, 1), (2, 2), (3, 3), (4, 4)},
    {(0, 0), (1, 2), (3, 3), (4, 4)},
    {(0, 2), (3, 3), (4, 4)},
    {(0, 0), (1, 1), (2, 3), (4, 4)},
    {(0, 1), (2, 3), (4, 4)},
    {(0, 0), (1, 3), (4, 4)},
    {(0, 3), (4, 4)},
    {(0, 0), (1, 1), (2, 2), (3, 4)},
    {(0, 1), (2, 2), (3, 4)},
    {(0, 0), (1, 2), (3, 4)},
    {(0, 2), (3, 4)},
    {(0, 0), (1, 1), (2, 4)},
    {(0, 1), (2, 4)},
    {(0, 0), (1, 4)},
    {(0, 4)}]

private theorem joinedEdges_eq_table (m : Fin 16) :
    joinedEdges m = joinedEdgesTable m := by
  fin_cases m <;> decide +kernel

private theorem intervalBlocks_eq_table (m : Fin 16) :
    intervalBlocks m = intervalBlocksTable m := by
  fin_cases m <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Expanding the full five-row determinant and the sixteen interval products is finite but large.
/-- The sixteen subset terms give the complete first determinant, symbolically in all labels. -/
theorem closed_det_interval_expansion (D : BetaDiagram 5) {k : Fin 3} (h : HasOpening D k) :
    (closedMatrix D k).det = ∑ m : Fin 16, intervalTerm D m := by
  rw [closedMatrix_eq_band D h]
  simp_rw [intervalTerm, joinedEdges_eq_table, intervalBlocks_eq_table]
  norm_num [Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
    Matrix.of_apply, Fin.sum_univ_succ, Fin.succAbove, intervalLabel,
    joinedEdgesTable, intervalBlocksTable, Finset.prod_insert,
    Finset.card_insert_of_notMem]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Bit-mask indexing covers every subset exactly once. -/
theorem joinedEdges_bijective : Function.Bijective joinedEdges := by
  decide +kernel

/-- The interval layer and the actual cofactor layer reconstruct the polynomial. -/
theorem sixteen_plus_eight (D : BetaDiagram 5) {k : Fin 3} (h : HasOpening D k) :
    D.homSchur = (∑ m : Fin 16, intervalTerm D m) +
      Gluing.hTilde (openingLabel D k) *
        ((-1) ^ ((openedRow k).val + (openedCol k).val) *
          ∑ σ ∈ cofactorPermutations k, (Equiv.Perm.sign σ : ℤ) •
            ∏ i : Fin 4, closedMatrix D k ((openedRow k).succAbove i)
              ((openedCol k).succAbove (σ i))) := by
  rw [open_decomposition, closed_det_interval_expansion D h, cofactor_det_expansion D h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exhaustive fixed-order combinatorics, not a census of bounded beta parameters. -/
theorem interval_permutation_count : intervalPermutations.card = 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cofactor_permutation_count (k : Fin 3) : (cofactorPermutations k).card = 8 := by
  fin_cases k <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem full_permutation_count (k : Fin 3) : (fullPermutations k).card = 24 := by
  fin_cases k <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Twelve of each sign before repeated-label collection. -/
theorem full_permutation_sign_counts (k : Fin 3) :
    ((fullPermutations k).filter fun σ => Equiv.Perm.sign σ = 1).card = 12 ∧
    ((fullPermutations k).filter fun σ => Equiv.Perm.sign σ = -1).card = 12 := by
  fin_cases k <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interval_permutation_sign_counts :
    (intervalPermutations.filter fun σ => Equiv.Perm.sign σ = 1).card = 8 ∧
    (intervalPermutations.filter fun σ => Equiv.Perm.sign σ = -1).card = 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cofactor_permutation_sign_counts (k : Fin 3) :
    ((cofactorPermutations k).filter fun σ => Equiv.Perm.sign σ = 1).card = 4 ∧
    ((cofactorPermutations k).filter fun σ => Equiv.Perm.sign σ = -1).card = 4 := by
  fin_cases k <;> decide +kernel

/-- Collection is an equality of coefficients, including cancellations across both layers. -/
theorem coefficient_collection (D : BetaDiagram 5) (k : Fin 3) (d : ℕ →₀ ℕ) :
    D.homSchur.coeff d = (closedMatrix D k).det.coeff d +
      (Gluing.hTilde (openingLabel D k) * openedCofactor D k).coeff d := by
  rw [open_decomposition D k, MvPolynomial.coeff_add]

/-- Arbitrary same-order mates are compared only after the two layers are added. -/
theorem mate_comparison (D E : BetaDiagram 5) (k l : Fin 3) :
    D.schur = E.schur ↔
      (closedMatrix D k).det + Gluing.hTilde (openingLabel D k) * openedCofactor D k =
      (closedMatrix E l).det + Gluing.hTilde (openingLabel E l) * openedCofactor E l := by
  rw [← D.homSchur_eq_iff E, ← open_decomposition D k, ← open_decomposition E l]

end FiveOpening
end SkewJacobiNegative
