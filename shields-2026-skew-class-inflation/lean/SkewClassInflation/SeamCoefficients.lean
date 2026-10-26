/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.HessenbergMembership
import SkewJacobiNegative.StaircaseSafeCuts

/-!
# Extreme coefficients at a distinguished positive seam

Formalizes the positive-seam part of `lem:seam-coefficients` and
`eq:seam-extremes` in `shields-2026-skew-class-inflation.tex`.
The seam value need not be a minimum: separation from every row suffices.
Repeated gap values remain separate geometric seam positions.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative
open SkewJacobiNegative.Gluing SkewJacobiNegative.GeneralHessenberg
open SkewJacobiNegative.Staircase
open scoped BigOperators

/-- A generator absent from the actual support contributes a genuinely constant polynomial. -/
theorem minimumPolynomial_eq_C_of_not_mem (z : ℕ+) (p : CompleteRing) (hz : z ∉ p.vars) :
    minimumPolynomial z p = Polynomial.C p := by
  refine MvPolynomial.hom_congr_vars ?_ ?_ rfl
  · ext q
    simp [minimumPolynomial]
  · intro j hj _
    have hjz : j ≠ z := by
      intro he
      subst j
      exact hz hj
    simp [minimumPolynomial, hjz]

/-- A generator below every row can occur only at a first-subdiagonal seam of that value. -/
theorem distinguished_index_iff_seam {n : ℕ} (P : Profile n) (hP : Thick P)
    (z : ℕ+) (hr : ∀ i, z.val < P.r i) (i j : Fin (n + 1)) :
    P.xi i - P.zeta j = (z.val : ℤ) ↔
      ∃ s : Fin n, i = s.succ ∧ j = s.castSucc ∧ P.g s = z.val := by
  constructor
  · intro he
    have hij : j < i := by
      by_contra h
      have hz := P.zeta_strictAnti.antitone (le_of_not_gt h)
      have hi := P.xi_sub_zeta i
      have hh := hr i
      omega
    have hfar : ¬ j.val + 1 < i.val := by
      intro h
      have hn := hP.hessenberg i j h
      have hp := z.pos
      omega
    let s : Fin n := ⟨j.val, by have := i.isLt; change j.val < i.val at hij; omega⟩
    have hs1 : s.succ = i := by
      apply Fin.ext
      change s.val + 1 = i.val
      dsimp [s]
      change j.val < i.val at hij
      omega
    have hs0 : s.castSucc = j := Fin.ext rfl
    refine ⟨s, hs1.symm, hs0.symm, ?_⟩
    have hg := P.xi_succ_sub_zeta_castSucc s
    rw [hs1, hs0, he] at hg
    omega
  · rintro ⟨s, rfl, rfl, hs⟩
    rw [P.xi_succ_sub_zeta_castSucc, hs]

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/StaircaseSafeCuts.lean,
-- minimum_not_mem_cutComponent, generalized from minimum gaps to separated row labels.
/-- Cutting every distinguished seam removes the generator from each genuine component. -/
theorem distinguished_not_mem_component {n : ℕ} (P : Profile n) (hP : Thick P)
    (z : ℕ+) (hr : ∀ i, z.val < P.r i) (b : CutBlock P z) :
    z ∉ (cutComponent P z b).toBetaDiagram.schur.vars := by
  rw [cutComponent_schur]
  apply not_mem_vars_det
  intro i j
  change z ∉ (complete
    (P.xi (blockEmbedding P z b i) - P.zeta (blockEmbedding P z b j))).vars
  rw [mem_vars_complete_iff]
  intro he
  obtain ⟨s, hi, hj, hg⟩ :=
    (distinguished_index_iff_seam P hP z hr
      (blockEmbedding P z b i) (blockEmbedding P z b j)).mp he.symm
  have hs := cutRank_step P z s
  rw [← hi, ← hj, blockEmbedding_rank, blockEmbedding_rank, ite_eq_left hg] at hs
  omega

/-- The constant coefficient is the product of unspecialized actual cut components. -/
theorem distinguished_cut_product {n : ℕ} (P : Profile n) (hP : Thick P)
    (z : ℕ+) (hr : ∀ i, z.val < P.r i) :
    eraseGenerator z P.toBetaDiagram.schur =
      ∏ b : CutBlock P z, (cutComponent P z b).toBetaDiagram.schur := by
  rw [erase_schur_cut_product hP z]
  exact Finset.prod_congr rfl fun b _ => eraseGenerator_eq_self z _
    (distinguished_not_mem_component P hP z hr b)

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/StaircaseSafeCuts.lean,
-- minimum_entry_top, with the distinguished-label producer substituted for minimum separation.
/-- Exact entrywise degree bounds and top coefficients for the determinant calculation. -/
theorem distinguished_entry_top {n : ℕ} (P : Profile n) (hP : Thick P)
    (z : ℕ+) (hr : ∀ i, z.val < P.r i) (i j : Fin (n + 1)) :
    (minimumPolynomial z (P.toBetaDiagram.matrix i j)).natDegree ≤
      (if minimumRow P z i then 1 else 0) ∧
    (minimumPolynomial z (P.toBetaDiagram.matrix i j)).coeff
      (if minimumRow P z i then 1 else 0) = minimumTopMatrix P z i j := by
  classical
  change (minimumPolynomial z (complete (P.xi i - P.zeta j))).natDegree ≤
      (if minimumRow P z i then 1 else 0) ∧
    (minimumPolynomial z (complete (P.xi i - P.zeta j))).coeff
      (if minimumRow P z i then 1 else 0) = minimumTopMatrix P z i j
  rw [minimumPolynomial_complete]
  by_cases he : P.xi i - P.zeta j = (z.val : ℤ)
  · obtain ⟨s, hi, hj, hg⟩ := (distinguished_index_iff_seam P hP z hr i j).mp he
    have hrow : minimumRow P z i := ⟨s, hi, hg⟩
    have hval : i.val = j.val + 1 := by rw [hi, hj]; rfl
    simp only [he, ite_true, minimumTopMatrix, ite_eq_left hrow, hval,
      Polynomial.natDegree_X, Polynomial.coeff_X_one, le_refl, and_self]
  · by_cases hrow : minimumRow P z i
    · have hn : i.val ≠ j.val + 1 := by
        intro h
        obtain ⟨s, hi, hg⟩ := hrow
        have hj : j = s.castSucc := by
          rw [hi] at h
          apply Fin.ext
          change j.val = s.val
          change s.val + 1 = j.val + 1 at h
          omega
        exact he ((distinguished_index_iff_seam P hP z hr i j).mpr ⟨s, hi, hj, hg⟩)
      simp [he, hrow, hn, minimumTopMatrix]
    · simp [he, hrow, minimumTopMatrix]

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/StaircaseSafeCuts.lean,
-- minimum_highest_layer, using the separated-label entry theorem on the actual board.
/-- The highest distinguished-generator coefficient is the signed actual total contraction. -/
theorem distinguished_highest_layer {n : ℕ} (P : Profile n) (hP : Thick P)
    (z : ℕ+) (hr : ∀ i, z.val < P.r i) :
    (minimumPolynomial z P.toBetaDiagram.schur).coeff (minimumMultiplicity P z) =
      (-1 : CompleteRing) ^ minimumMultiplicity P z *
        (contractAllMinimum P z).2.toBetaDiagram.schur := by
  classical
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial CompleteRing) :=
    (minimumPolynomial z).mapMatrix P.toBetaDiagram.matrix
  let d : Fin (n + 1) → ℕ := fun i => if minimumRow P z i then 1 else 0
  have hm : minimumPolynomial z P.toBetaDiagram.schur = M.det :=
    (minimumPolynomial z).map_det P.toBetaDiagram.matrix
  have hc : M.det.coeff (∑ i, d i) =
      (Matrix.of (fun i j : Fin (n + 1) => (M i j).coeff (d i))).det :=
    coeff_det_row_bound M d (fun i j => (distinguished_entry_top P hP z hr i j).1)
  rw [hm, minimumMultiplicity_rows]
  change M.det.coeff (∑ i, d i) =
    (-1 : CompleteRing) ^ (∑ i, d i) *
      (contractAllMinimum P z).2.toBetaDiagram.schur
  rw [hc]
  have he : (Matrix.of (fun i j : Fin (n + 1) => (M i j).coeff (d i))) =
      minimumTopMatrix P z := by
    apply Matrix.ext
    intro i j
    exact (distinguished_entry_top P hP z hr i j).2
  rw [he]
  simpa only [minimumMultiplicity_rows, BetaDiagram.schur, d] using minimumTopMatrix_det P z

/-- Contraction never decreases a retained row below the corresponding original row. -/
theorem contract_rows_above {n : ℕ} (P : Profile (n + 1)) (z : ℕ+)
    (hr : ∀ i, z.val < P.r i) (c : Fin (n + 1)) (i : Fin (n + 1)) :
    z.val < (contract P c).r i := by
  obtain ⟨hx, hz⟩ := contract_beta P c
  have hidx : c.succ.succAbove i ≤ c.castSucc.succAbove i := by
    simp only [Fin.succAbove]
    split_ifs <;>
      simp only [Fin.le_iff_val_le_val, Fin.lt_def,
        Fin.val_castSucc, Fin.val_succ] at * <;> omega
  have hcol := P.zeta_strictAnti.antitone hidx
  have ho := P.xi_sub_zeta (c.succ.succAbove i)
  have hn := (contract P c).xi_sub_zeta i
  rw [congrFun hx i, congrFun hz i] at hn
  have hh := hr (c.succ.succAbove i)
  omega

/-- Every actual row stays above the distinguished label through all seam contractions. -/
theorem contractAll_rows_above {n : ℕ} (P : Profile n) (z : ℕ+)
    (hr : ∀ i, z.val < P.r i) :
    ∀ i, z.val < (contractAllMinimum P z).2.r i := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    by_cases h : ∃ c : Fin (n + 1), P.g c = z.val
    · rw [show contractAllMinimum P z =
        contractAllMinimum (contract P (Classical.choose h)) z by
          simp only [contractAllMinimum, dite_eq_left h]]
      exact ih _ (contract_rows_above P z hr _)
    · rw [show contractAllMinimum P z = ⟨n + 1, P⟩ by
          simp only [contractAllMinimum, dite_eq_right h]]
      exact hr

/-- The total contraction contains no occurrence of the distinguished generator. -/
theorem distinguished_not_mem_contraction {n : ℕ} (P : Profile n) (hP : Thick P)
    (z : ℕ+) (hr : ∀ i, z.val < P.r i) :
    z ∉ (contractAllMinimum P z).2.toBetaDiagram.schur.vars := by
  apply not_mem_vars_det
  intro i j hm
  have he := (mem_vars_complete_iff _ z).mp hm
  obtain ⟨s, _, _, hs⟩ := (distinguished_index_iff_seam _ (contractAllMinimum_thick hP z)
    z (contractAll_rows_above P z hr) i j).mp he.symm
  exact contractAllMinimum_gap_ne P z s hs

/-- The maximum coefficient is nonzero, so its degree is the exact seam multiplicity. -/
theorem distinguished_degree_exact {n : ℕ} (P : Profile n) (hP : Thick P)
    (z : ℕ+) (hr : ∀ i, z.val < P.r i) :
    (minimumPolynomial z P.toBetaDiagram.schur).natDegree = minimumMultiplicity P z := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [BetaDiagram.schur, (minimumPolynomial z).map_det, minimumMultiplicity_rows]
    exact natDegree_det_row_bound _ _
      (fun i j => (distinguished_entry_top P hP z hr i j).1)
  · rw [distinguished_highest_layer P hP z hr]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (contractAllMinimum P z).2.toBetaDiagram.schur_ne_zero

end SkewClassInflation
