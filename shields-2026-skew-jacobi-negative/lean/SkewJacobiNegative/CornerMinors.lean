/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.OrdinaryReadings
import Mathlib.Algebra.MvPolynomial.PDeriv
import Shields.LinearAlgebra.Matrix.DesnanotJacobi

/-!
# Private corner coefficients

Actual complementary determinants for `lem:polynomial-readings` and the
induction in `sec:boundary`.  Complementary diagonal indices may be zero;
nonvanishing uses the strict-Monge theorem with its weak feasibility condition.
-/

namespace SkewJacobiNegative

open scoped BigOperators

/-- A Jacobi--Trudi board without the nonempty-diagonal restriction. -/
noncomputable def betaBoard {n : ℕ} (u v : Fin n → ℤ) :
    Matrix (Fin n) (Fin n) CompleteRing :=
  Matrix.of fun i j => complete (u i - v j)

/-- Strict ordered lists and a weakly feasible diagonal suffice for nonvanishing. -/
theorem betaBoard_det_ne_zero {n : ℕ} (u v : Fin n → ℤ)
    (hu : StrictAnti u) (hv : StrictAnti v) (hf : ∀ i, v i ≤ u i) :
    (betaBoard u v).det ≠ 0 := by
  let M : Matrix (Fin n) (Fin n) Base.CompleteRing :=
    Base.staircaseMatrix (fun i => -u i) (fun i => -v i)
  have hn : M.det ≠ 0 := Base.monge_minor_ne_zero Base.squareWeight
    (fun i j hij => by have := hu hij; omega)
    (fun i j hij => by have := hv hij; omega)
    (fun i => by have := hf i; omega)
  have he : betaBoard u v = M.map integerLift := by
    ext i j
    simp only [betaBoard, M, Base.staircaseMatrix, Matrix.of_apply,
      Matrix.map_apply, complete]
    congr 2
    ring_nf
  rw [he, ← integerLift_det]
  intro hz
  apply hn
  apply integerLift_injective
  simpa using hz

/-- The padded diagonal remains the exact minimum-square monomial. -/
theorem betaBoard_square_initialForm {n : ℕ} (u v : Fin n → ℤ)
    (hu : StrictAnti u) (hv : StrictAnti v) (hf : ∀ i, v i ≤ u i) :
    Base.initialForm Base.squareWeight.generatorWeight (betaBoard u v).det =
      ∏ i, complete (u i - v i) := by
  have hm : betaBoard u v =
      (Base.staircaseMatrix (fun i => -u i) (fun i => -v i)).map integerLift := by
    ext i j
    simp only [betaBoard, Base.staircaseMatrix, Matrix.of_apply, Matrix.map_apply,
      complete]
    congr 2
    ring_nf
  rw [hm, ← integerLift_det, integerLift_initialForm,
    Base.monge_minor_initialForm Base.squareWeight
      (fun i j hij => by have := hu hij; omega)
      (fun i j hij => by have := hv hij; omega)
      (fun i => by have := hf i; omega), map_prod]
  apply Finset.prod_congr rfl
  intro i _
  change integerLift (Base.complete (-v i - -u i)) = complete (u i - v i)
  congr 2
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Every variable in a complete entry is its strictly positive index. -/
theorem mem_vars_complete_iff (k : ℤ) (j : ℕ+) :
    j ∈ (complete k).vars ↔ (j.val : ℤ) = k := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [complete_of_neg hk]
    simp only [MvPolynomial.vars_0, Finset.notMem_empty, false_iff]
    have := j.pos
    omega
  · subst k
    have hj : (j.val : ℤ) ≠ 0 := ne_of_gt (by exact_mod_cast j.pos)
    simpa only [complete_zero, MvPolynomial.vars_one, Finset.notMem_empty, false_iff] using hj
  · let v : ℕ+ := ⟨k.toNat, by omega⟩
    have he : complete k = (MvPolynomial.X v : CompleteRing) := complete_of_pos hk
    rw [he, MvPolynomial.vars_X, Finset.mem_singleton]
    constructor
    · intro h
      subst j
      change (k.toNat : ℤ) = k
      omega
    · intro h
      apply Subtype.ext
      change j.val = k.toNat
      omega

/-- Absence of one variable is preserved by finite sums. -/
theorem not_mem_vars_sum {ι : Type*} (s : Finset ι) (f : ι → CompleteRing)
    (v : ℕ+) (h : ∀ i ∈ s, v ∉ (f i).vars) : v ∉ (∑ i ∈ s, f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      intro hv
      rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hv) with hv | hv
      · exact h i (Finset.mem_insert_self _ _) hv
      · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) hv

/-- Absence of one variable is preserved by finite products. -/
theorem not_mem_vars_prod {ι : Type*} (s : Finset ι) (f : ι → CompleteRing)
    (v : ℕ+) (h : ∀ i ∈ s, v ∉ (f i).vars) : v ∉ (∏ i ∈ s, f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      intro hv
      rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hv | hv
      · exact h i (Finset.mem_insert_self _ _) hv
      · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) hv

/-- A determinant cannot introduce a variable absent from all its entries. -/
theorem not_mem_vars_det {n : ℕ} (M : Matrix (Fin n) (Fin n) CompleteRing)
    (v : ℕ+) (h : ∀ i j, v ∉ (M i j).vars) : v ∉ M.det.vars := by
  classical
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook]
  apply not_mem_vars_sum
  intro σ _
  have hp := not_mem_vars_prod Finset.univ (fun i => M i (σ i)) v
    (fun i _ => h i (σ i))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using hp

/-- Every board determinant has its exact geometric weighted degree. -/
theorem betaBoard_reverse_homogeneous {n : ℕ} (u v : Fin n → ℤ) :
    MvPolynomial.IsWeightedHomogeneous reverseIndexWeight (betaBoard u v).det
      (-((∑ i, u i - ∑ i, v i : ℤ) : ℝ)) := by
  classical
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro σ _
  have hp := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i => complete (u i - v (σ i)))
    (fun i => -((u i - v (σ i) : ℤ) : ℝ))
    (fun i _ => complete_reverse_homogeneous _)
  have he : (∑ i, -((u i - v (σ i) : ℤ) : ℝ)) =
      -((∑ i, u i - ∑ i, v i : ℤ) : ℝ) := by
    have := Equiv.sum_comp σ v
    push_cast
    simp only [Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    congr 1
    exact_mod_cast (congrArg (fun z : ℤ => (∑ i, u i) - z) this)
  rw [he] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [betaBoard, hs] using hp
  · simpa [betaBoard, hs] using hp.neg

namespace BetaDiagram

variable {n : ℕ}

/-- The largest possible entry label; translation normalization is unnecessary. -/
def largestLabel (D : BetaDiagram (n + 1)) : ℤ := D.row 0 - D.col (Fin.last n)

/-- The actual maximal-corner complementary board, including index-zero diagonals. -/
noncomputable def cornerBoard (D : BetaDiagram (n + 1)) :
    Matrix (Fin n) (Fin n) CompleteRing :=
  betaBoard (fun i => D.row i.succ) (fun j => D.col j.castSucc)

/-- Its unsigned polynomial is the manuscript's `Q` in `eq:corner-coefficient`. -/
noncomputable def cornerPolynomial (D : BetaDiagram (n + 1)) : CompleteRing :=
  D.cornerBoard.det

/-- The signed coefficient of the largest generator in the original determinant. -/
noncomputable def cornerCoefficient (D : BetaDiagram (n + 1)) : CompleteRing :=
  (-1) ^ n * D.cornerPolynomial

/-- The row-expansion terms avoiding the unique largest-label site. -/
noncomputable def cornerResidual (D : BetaDiagram (n + 1)) : CompleteRing :=
  ∑ j ∈ Finset.univ.erase (Fin.last n),
    (-1) ^ j.val * D.matrix 0 j *
      (D.matrix.submatrix Fin.succ j.succAbove).det

/-- The largest label is strictly positive at every nonempty beta diagram. -/
theorem largestLabel_pos (D : BetaDiagram (n + 1)) : 0 < D.largestLabel := by
  have hc : D.col (Fin.last n) ≤ D.col 0 := D.col_strictAnti.antitone (Fin.zero_le _)
  have hr := D.row_nonempty 0
  dsimp [largestLabel]
  omega

/-- There is one and only one site with the largest label. -/
theorem index_lt_largestLabel (D : BetaDiagram (n + 1)) (i j : Fin (n + 1))
    (h : i ≠ 0 ∨ j ≠ Fin.last n) : D.row i - D.col j < D.largestLabel := by
  have hr : D.row i ≤ D.row 0 := D.row_strictAnti.antitone (Fin.zero_le i)
  have hc : D.col (Fin.last n) ≤ D.col j := D.col_strictAnti.antitone (Fin.le_last j)
  rcases h with hi | hj
  · have hs := D.row_strictAnti (show (0 : Fin (n + 1)) < i by
      exact Fin.pos_iff_ne_zero.mpr hi)
    dsimp [largestLabel]
    omega
  · have hs := D.col_strictAnti (show j < Fin.last n by
      exact Fin.lt_last_iff_ne_last.mpr hj)
    dsimp [largestLabel]
    omega

/-- Connectedness supplies precisely the padded corner diagonal feasibility. -/
theorem corner_diagonal_nonnegative (D : BetaDiagram (n + 1)) (hD : D.Connected)
    (i : Fin n) : D.col i.castSucc ≤ D.row i.succ :=
  hD.2 i.castSucc (by simp only [Fin.val_castSucc]; omega)

/-- The corner determinant never vanishes, even when overlaps have index zero. -/
theorem cornerPolynomial_ne_zero (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    D.cornerPolynomial ≠ 0 := by
  apply betaBoard_det_ne_zero
  · exact D.row_strictAnti.comp_strictMono Fin.strictMono_succ
  · exact D.col_strictAnti.comp_strictMono Fin.strictMono_castSucc
  · exact D.corner_diagonal_nonnegative hD

/-- The corner's square initial form retains all padded zero overlaps. -/
theorem corner_square_initialForm (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    Base.initialForm Base.squareWeight.generatorWeight D.cornerPolynomial =
      ∏ i : Fin n, complete (D.row i.succ - D.col i.castSucc) := by
  apply betaBoard_square_initialForm
  · exact D.row_strictAnti.comp_strictMono Fin.strictMono_succ
  · exact D.col_strictAnti.comp_strictMono Fin.strictMono_castSucc
  · exact D.corner_diagonal_nonnegative hD

set_option backward.isDefEq.respectTransparency false in
/-- The exact linear decomposition at the largest label. -/
theorem schur_corner_split (D : BetaDiagram (n + 1)) :
    D.schur = D.cornerCoefficient *
      MvPolynomial.X (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) +
      D.cornerResidual := by
  classical
  unfold schur
  rw [Matrix.det_succ_row_zero]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (Fin.last n))]
  have he : D.matrix.submatrix Fin.succ (Fin.last n).succAbove = D.cornerBoard := by
    ext i j
    simp [matrix, cornerBoard, betaBoard, Fin.succAbove_last]
  rw [he]
  change D.cornerResidual +
    (-1) ^ n * complete D.largestLabel * D.cornerPolynomial = _
  let v : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  have hg : complete D.largestLabel = (MvPolynomial.X v : CompleteRing) :=
    complete_of_pos D.largestLabel_pos
  rw [hg]
  change D.cornerResidual + (-1 : CompleteRing) ^ n *
      MvPolynomial.X v * D.cornerPolynomial =
    (-1 : CompleteRing) ^ n * D.cornerPolynomial *
      MvPolynomial.X v + D.cornerResidual
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The largest generator is absent from its complementary determinant. -/
theorem largest_not_mem_corner (D : BetaDiagram (n + 1)) :
    (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) ∉
      D.cornerPolynomial.vars := by
  apply not_mem_vars_det
  intro i j
  change (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) ∉
    (complete (D.row i.succ - D.col j.castSucc)).vars
  rw [mem_vars_complete_iff]
  change ¬ ((D.largestLabel.toNat : ℕ) : ℤ) = D.row i.succ - D.col j.castSucc
  have := D.index_lt_largestLabel i.succ j.castSucc (Or.inl (Fin.succ_ne_zero i))
  have := D.largestLabel_pos
  omega

set_option backward.isDefEq.respectTransparency false in
/-- The residual contains no largest generator. -/
theorem largest_not_mem_residual (D : BetaDiagram (n + 1)) :
    (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) ∉
      D.cornerResidual.vars := by
  classical
  apply not_mem_vars_sum
  intro j hj
  have hjl : j ≠ Fin.last n := (Finset.mem_erase.mp hj).1
  have he : (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) ∉
      (D.matrix 0 j).vars := by
    change (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) ∉
      (complete (D.row 0 - D.col j)).vars
    rw [mem_vars_complete_iff]
    change ¬ ((D.largestLabel.toNat : ℕ) : ℤ) = D.row 0 - D.col j
    have := D.index_lt_largestLabel 0 j (Or.inr hjl)
    have := D.largestLabel_pos
    omega
  have hm : (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) ∉
      (D.matrix.submatrix Fin.succ j.succAbove).det.vars := by
    apply not_mem_vars_det
    intro a b
    change (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) ∉
      (complete (D.row a.succ - D.col (j.succAbove b))).vars
    rw [mem_vars_complete_iff]
    change ¬ ((D.largestLabel.toNat : ℕ) : ℤ) = D.row a.succ - D.col (j.succAbove b)
    have := D.index_lt_largestLabel a.succ (j.succAbove b)
      (Or.inl (Fin.succ_ne_zero a))
    have := D.largestLabel_pos
    omega
  intro hv
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hv | hv
  · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hv | hv
    · have hn := MvPolynomial.vars_pow (-1 : CompleteRing) j.val hv
      simp only [MvPolynomial.vars_neg, MvPolynomial.vars_one, Finset.notMem_empty] at hn
    · exact he hv
  · exact hm hv

set_option backward.isDefEq.respectTransparency false in
/-- Differentiation reads the complete signed corner coefficient, not one scalar monomial. -/
theorem pderiv_schur_largest (D : BetaDiagram (n + 1)) :
    MvPolynomial.pderiv
      (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) D.schur =
      D.cornerCoefficient := by
  rw [D.schur_corner_split, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars D.largest_not_mem_residual]
  have hc : (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) ∉
      D.cornerCoefficient.vars := by
    intro hv
    rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hv | hv
    · have hn := MvPolynomial.vars_pow (-1 : CompleteRing) n hv
      simp only [MvPolynomial.vars_neg, MvPolynomial.vars_one, Finset.notMem_empty] at hn
    · exact D.largest_not_mem_corner hv
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hc]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The largest label actually occurs in every connected Schur determinant. -/
theorem largest_mem_vars (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) ∈ D.schur.vars := by
  by_contra h
  have hz := MvPolynomial.pderiv_eq_zero_of_notMem_vars h
  rw [D.pderiv_schur_largest] at hz
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (D.cornerPolynomial_ne_zero hD) hz

set_option backward.isDefEq.respectTransparency false in
/-- Every occupied generator index is at most the private largest label. -/
theorem vars_le_largestLabel (D : BetaDiagram (n + 1)) (j : ℕ+)
    (hj : j ∈ D.schur.vars) : (j.val : ℤ) ≤ D.largestLabel := by
  by_contra h
  apply (not_mem_vars_det D.matrix j ?_) hj
  intro i k
  change j ∉ (complete (D.row i - D.col k)).vars
  rw [mem_vars_complete_iff]
  have hr := D.row_strictAnti.antitone (Fin.zero_le i)
  have hc := D.col_strictAnti.antitone (Fin.le_last k)
  dsimp [largestLabel] at h
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Equality recovers the largest label without a nonnegative-index assumption on the mate. -/
theorem largestLabel_eq_of_schur_eq (D E : BetaDiagram (n + 1))
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur) :
    D.largestLabel = E.largestLabel := by
  have hd := D.largest_mem_vars hD
  have hf := E.largest_mem_vars hE
  rw [he] at hd
  rw [← he] at hf
  have h₁ := E.vars_le_largestLabel _ hd
  have h₂ := D.vars_le_largestLabel _ hf
  have := D.largestLabel_pos
  have := E.largestLabel_pos
  change ((D.largestLabel.toNat : ℕ) : ℤ) ≤ E.largestLabel at h₁
  change ((E.largestLabel.toNat : ℕ) : ℤ) ≤ D.largestLabel at h₂
  omega

set_option backward.isDefEq.respectTransparency false in
/-- The unsigned corner polynomial is consequently recovered as an actual polynomial. -/
theorem cornerPolynomial_eq_of_schur_eq (D E : BetaDiagram (n + 1))
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur) :
    D.cornerPolynomial = E.cornerPolynomial := by
  have hl := D.largestLabel_eq_of_schur_eq E hD hE he
  have hp := congrArg (MvPolynomial.pderiv
    (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+)) he
  have hv : (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) =
      ⟨E.largestLabel.toNat, by have := E.largestLabel_pos; omega⟩ := by
    apply Subtype.ext
    exact congrArg Int.toNat hl
  rw [D.pderiv_schur_largest, hv, E.pderiv_schur_largest] at hp
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hp

end BetaDiagram
end SkewJacobiNegative
