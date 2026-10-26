/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalResidueResponses

/-!
# Literal protected tops of the original Hessenberg response

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`, `lem:component-elimination`). The actual
ordered endpoint differences strictly exceed the selected top on and above the diagonal.
The top indices and their monic residue responses are produced, not assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The first ordered retained row is the literal global top row. -/
theorem originalHessenbergRows_zero {n : ℕ} (P : Profile n) :
    originalHessenbergRows (hD := hD) P 0 = none := by
  simp [originalHessenbergRows]

/-- The last ordered retained column is the literal global last column. -/
theorem originalHessenbergCols_last {n : ℕ} (P : Profile n) :
    originalHessenbergCols (hD := hD) P (Fin.last _) = none := by
  simp [originalHessenbergCols]

/-- Literal endpoint distance of an actual ordered retained response. -/
noncomputable def originalHessenbergDistance {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) : ℤ :=
  P.xi (originalRowSplitEquiv (hD := hD) P
    (.inl (originalHessenbergRows (hD := hD) P i))) -
  P.zeta (originalColSplitEquiv (hD := hD) P
    (.inl (originalHessenbergCols (hD := hD) P j)))

/-- Every actual ordered upper top is strictly protected whenever the selected prime occurs. -/
theorem originalHessenbergDistance_gt_top {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j) :
    (c.top : ℤ) < originalHessenbergDistance (hD := hD) P i j := by
  revert hij
  refine Fin.cases ?_ (fun a => ?_) i
  · intro _
    refine Fin.lastCases ?_ (fun k => ?_) j
    · let b := originalSelectedEnumeration (hD := hD) P ⟨0, hB⟩
      have ht := c.originalLastCapDistance_gt_top P b
      change (c.top : ℤ) < P.xi b.val.val.succ - P.zeta (Fin.last n) at ht
      have hx := P.xi_strictAnti (show (0 : Fin (n + 1)) < b.val.val.succ by
        change 0 < _ + 1
        omega)
      unfold originalHessenbergDistance
      rw [originalHessenbergRows_zero, originalHessenbergCols_last,
        originalRowSplitEquiv_corner, originalColSplitEquiv_corner]
      omega
    · unfold originalHessenbergDistance
      rw [originalHessenbergRows_zero, originalHessenbergCols_castSucc,
        originalRowSplitEquiv_corner, originalColSplitEquiv_selected]
      exact c.originalFirstCapDistance_gt_top P _
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · intro _
      unfold originalHessenbergDistance
      rw [originalHessenbergRows_succ, originalHessenbergCols_last,
        originalRowSplitEquiv_selected, originalColSplitEquiv_corner]
      exact c.originalLastCapDistance_gt_top P _
    · intro hij
      have hak : a < k := by
        change a.val + 1 ≤ k.val at hij
        change a.val < k.val
        omega
      have ht := c.originalSelected_endpoint_distance P
        (originalSelectedEnumeration (hD := hD) P a)
      have hg := c.originalSelected_gap_gt_top P
        (originalSelectedEnumeration (hD := hD) P a)
        (originalSelectedEnumeration (hD := hD) P k)
        (originalSelectedEnumeration_label_strictMono P hak)
      unfold originalHessenbergDistance
      rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc,
        originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
      have hp := c.top.property
      omega

/-- A genuine selected-to-selected interval has top strictly above twice the
selected span (`lem:early-recovery`). Both complete selected endpoint spans and
their strict original separation are supplied by the actual component geometry. -/
theorem originalHessenbergDistance_selected_gt_twice_top {n : ℕ} (P : Profile n)
    (a k : Fin (originalSelectedCount (hD := hD) P)) (hak : a < k) :
    2 * (c.top : ℤ) < originalHessenbergDistance (hD := hD) P a.succ k.castSucc := by
  have ht := c.originalSelected_endpoint_distance P
    (originalSelectedEnumeration (hD := hD) P a)
  have hg := c.originalSelected_gap_gt_top P
    (originalSelectedEnumeration (hD := hD) P a)
    (originalSelectedEnumeration (hD := hD) P k)
    (originalSelectedEnumeration_label_strictMono P hak)
  unfold originalHessenbergDistance
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc,
    originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  omega

/-- The actual positive upper-response top, canonically extracted from its source endpoints. -/
noncomputable def originalHessenbergTop {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j) : ℕ+ :=
  ⟨(originalHessenbergDistance (hD := hD) P i j).toNat, by
    have h := c.originalHessenbergDistance_gt_top P hB i j hij
    have hp := c.top.property
    omega⟩

/-- This top is the literal endpoint distance, not a formal response index. -/
theorem originalHessenbergTop_coe {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j) :
    (c.originalHessenbergTop P hB i j hij : ℤ) = originalHessenbergDistance (hD := hD) P i j := by
  apply Int.toNat_of_nonneg
  have h := c.originalHessenbergDistance_gt_top P hB i j hij
  have hp := c.top.property
  omega

/-- Every original ordered upper response is monic at its produced top after actual reduction. -/
theorem originalHessenbergResponse_residue_triangular {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j) :
    ∃ A ∈ residueLowerField c.top (c.originalHessenbergTop P hB i j hij),
      c.regularResidue (c.originalHessenbergResponse P i j) =
        c.residueMap (MvPolynomial.X (c.originalHessenbergTop P hB i j hij)) + A := by
  apply c.originalLocalResponse_residue_triangular
  · have h := c.originalHessenbergDistance_gt_top P hB i j hij
    have he := c.originalHessenbergTop_coe P hB i j hij
    exact_mod_cast (show (c.top : ℤ) < (c.originalHessenbergTop P hB i j hij : ℤ) by omega)
  · exact (c.originalHessenbergTop_coe P hB i j hij).symm

end SkewCornerDescent.Matrix.SelectedCoordinate
