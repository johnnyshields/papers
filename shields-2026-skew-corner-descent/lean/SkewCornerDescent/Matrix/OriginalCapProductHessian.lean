/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalIntervals
import SkewCornerDescent.Matrix.OriginalCapNormalization
import SkewCornerDescent.Matrix.ResidueHessianSymmetry

/-!
# Actual true-cap product has unit two-generator coefficient

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`, `cor:row-pencil`).
The source's produced cap tops give mixed second derivative one at distinct
tops and two at a coincident square. Both complete actual caps are retained;
no independent affine cap assignment is supplied. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual protected tops of two full diagonal responses give a unit
mixed product jet, or its doubled value at a coincident square. All top and
lower-support derivatives are supplied by the original response producer. -/
theorem original_diagonal_product_hessian {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (i j : Fin (originalSelectedCount (hD := hD) P + 1))
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    (hi : originalHessenbergDistance (hD := hD) P i i = (p : ℤ))
    (hj : originalHessenbergDistance (hD := hD) P j j = (q : ℤ)) :
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
        (c.regularResidue (c.originalHessenbergResponse P i i) *
          c.regularResidue (c.originalHessenbergResponse P j j))) =
      if p = q then 2 else 1 := by
  let dp := residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
  let dq := residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
  let L := c.regularResidue (c.originalHessenbergResponse P i i)
  let R := c.regularResidue (c.originalHessenbergResponse P j j)
  have hpL : dp L = 1 := by
    have h := c.originalHessenberg_residue_derivative_indicator P hB hmax p hp i i le_rfl hi.le
    rwa [hi, ite_eq_left rfl] at h
  have hqR : dq R = 1 := by
    have h := c.originalHessenberg_residue_derivative_indicator P hB hmax q hq j j le_rfl hj.le
    rwa [hj, ite_eq_left rfl] at h
  by_cases he : p = q
  · subst q
    have hpR : dp R = 1 := hqR
    change dp (dp (L * R)) = if p = p then 2 else 1
    rw [ite_eq_left rfl, dp.leibniz]
    simp only [smul_eq_mul, hpL, hpR, mul_one, map_add]
    norm_num
  · by_cases hpq : p ≤ q
    · have hqL : dq L = 0 := by
        have hdist : originalHessenbergDistance (hD := hD) P i i ≤ (q : ℤ) := by
          rw [hi]
          exact_mod_cast hpq
        have h := c.originalHessenberg_residue_derivative_indicator P hB hmax q hq i i le_rfl hdist
        have hne : (p : ℤ) ≠ (q : ℤ) := by exact_mod_cast he
        rwa [hi, ite_eq_right hne] at h
      change dp (dq (L * R)) = if p = q then 2 else 1
      rw [ite_eq_right he, dq.leibniz]
      simpa only [smul_eq_mul, hqL, hqR, mul_one, mul_zero, add_zero] using hpL
    · have hpR : dp R = 0 := by
        have hdist : originalHessenbergDistance (hD := hD) P j j ≤ (p : ℤ) := by
          rw [hj]
          exact_mod_cast (le_of_not_ge hpq)
        have h := c.originalHessenberg_residue_derivative_indicator P hB hmax p hp j j le_rfl hdist
        have hne : (q : ℤ) ≠ (p : ℤ) := by exact_mod_cast (Ne.symm he)
        rwa [hj, ite_eq_right hne] at h
      have hsecond : dp (dq L) = 0 := by
        have h := c.originalHessenbergResponse_higher_commute P i i p q hp hq
        change dp (dq L) = dq (dp L) at h
        rw [h, hpL, dq.map_one_eq_zero]
      change dp (dq (L * R)) = if p = q then 2 else 1
      rw [ite_eq_right he, dq.leibniz]
      simp only [smul_eq_mul, hqR, mul_one, map_add, dp.leibniz,
        hpR, hsecond, hpL, mul_zero, add_zero]

/-- The original constructed top is genuinely above the selected span. -/
theorem originalHessenbergTop_gt_selected {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j) :
    c.top < c.originalHessenbergTop P hB i j hij := by
  have h := c.originalHessenbergDistance_gt_top P hB i j hij
  rw [← c.originalHessenbergTop_coe P hB i j hij] at h
  exact_mod_cast h

/-- The full actual true-cap product has mixed second jet one at its distinct
produced tops, and two at the coincident square. The chosen generators, their
order and their strict selected-span bounds are all produced from the source. -/
theorem originalTrueCapProduct_hessian {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let leftTop := c.originalHessenbergTop P hB 0 0 le_rfl
    let rightTop := c.originalHessenbergTop P hB (Fin.last _) (Fin.last _) le_rfl
    let p := min leftTop rightTop
    let q := max leftTop rightTop
    let hp : c.top < p := lt_min
      (c.originalHessenbergTop_gt_selected P hB 0 0 le_rfl)
      (c.originalHessenbergTop_gt_selected P hB (Fin.last _) (Fin.last _) le_rfl)
    let hq : c.top < q := lt_of_lt_of_le
      (c.originalHessenbergTop_gt_selected P hB 0 0 le_rfl) (le_max_left _ _)
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩ (c.originalTrueCapProduct P)) =
      if leftTop = rightTop then 2 else 1 := by
  let leftTop := c.originalHessenbergTop P hB 0 0 le_rfl
  let rightTop := c.originalHessenbergTop P hB (Fin.last _) (Fin.last _) le_rfl
  have hL := c.originalHessenbergTop_gt_selected P hB 0 0 le_rfl
  have hR := c.originalHessenbergTop_gt_selected P hB (Fin.last _) (Fin.last _) le_rfl
  dsimp only
  by_cases hle : leftTop ≤ rightTop
  · dsimp only [leftTop, rightTop] at hle
    simp only [min_eq_left hle, max_eq_right hle]
    exact c.original_diagonal_product_hessian P hB hmax 0 (Fin.last _) leftTop rightTop hL hR
      (c.originalHessenbergTop_coe P hB 0 0 le_rfl).symm
      (c.originalHessenbergTop_coe P hB (Fin.last _) (Fin.last _) le_rfl).symm
  · have hle' : rightTop ≤ leftTop := (lt_of_not_ge hle).le
    dsimp only [leftTop, rightTop] at hle'
    simp only [min_eq_right hle', max_eq_left hle']
    have h := c.original_diagonal_product_hessian P hB hmax (Fin.last _) 0 rightTop leftTop
      hR hL (c.originalHessenbergTop_coe P hB (Fin.last _) (Fin.last _) le_rfl).symm
      (c.originalHessenbergTop_coe P hB 0 0 le_rfl).symm
    simpa only [originalTrueCapProduct, mul_comm, eq_comm] using h

/-- The actual first and last cap tops, in source order, give the same
nonzero mixed cap jet. No sorting or coincident-square exclusion is needed. -/
theorem originalTrueCapProduct_hessian_source_order {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let p := c.originalHessenbergTop P hB 0 0 le_rfl
    let q := c.originalHessenbergTop P hB (Fin.last _) (Fin.last _) le_rfl
    let hp := c.originalHessenbergTop_gt_selected P hB 0 0 le_rfl
    let hq := c.originalHessenbergTop_gt_selected P hB (Fin.last _) (Fin.last _) le_rfl
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩ (c.originalTrueCapProduct P)) =
      if p = q then 2 else 1 := by
  exact c.original_diagonal_product_hessian P hB hmax 0 (Fin.last _) _ _
    (c.originalHessenbergTop_gt_selected P hB 0 0 le_rfl)
    (c.originalHessenbergTop_gt_selected P hB (Fin.last _) (Fin.last _) le_rfl)
    (c.originalHessenbergTop_coe P hB 0 0 le_rfl).symm
    (c.originalHessenbergTop_coe P hB (Fin.last _) (Fin.last _) le_rfl).symm

end SkewCornerDescent.Matrix.SelectedCoordinate
