/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergAffineFrontier
import SkewCornerDescent.Matrix.OriginalNormalIntervals

/-!
# Affine first-fresh jets of the actual original determinant

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). Full
shorter-response jets belong to the lower field; a response at the protected top
has its genuine leading generator plus lower correction. The complete cost
frontier therefore gives affine original determinant coefficients. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Literal shorter intervals supply lower-field membership of every full jet,
not merely vanishing of its protected-generator derivative. -/
theorem originalHessenberg_normalSeries_coeff_mem_below {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j)
    (hdistance : originalHessenbergDistance (hD := hD) P i j < (K : ℤ)) (m : ℕ) :
    PowerSeries.coeff m (c.normalSeries (c.originalHessenbergResponse P i j)) ∈
      residueLowerField c.top K := by
  let J := c.originalHessenbergTop P hB i j hij
  have he : (J : ℤ) = originalHessenbergDistance (hD := hD) P i j :=
    c.originalHessenbergTop_coe P hB i j hij
  have hNJ : c.top < J := by
    have ht := c.originalHessenbergDistance_gt_top P hB i j hij
    exact_mod_cast (show (c.top : ℤ) < (J : ℤ) by omega)
  have hJK : J < K := by
    exact_mod_cast (show (J : ℤ) < (K : ℤ) by omega)
  exact c.originalLocalResponse_normalSeries_coeff_below P
    (originalHessenbergRows P i) (originalHessenbergCols P j) J K hNJ hJK he.symm hmax m

/-- Every eligible original upper residue is affine in the protected generator.
The equality case uses the actual full lower-jet response construction. -/
theorem originalHessenberg_residue_affine_of_le {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j)
    (hdistance : originalHessenbergDistance (hD := hD) P i j ≤ (K : ℤ)) :
    affineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      (c.regularResidue (c.originalHessenbergResponse P i j)) := by
  by_cases he : originalHessenbergDistance (hD := hD) P i j = (K : ℤ)
  · obtain ⟨R, hR, hresponse⟩ := c.originalLocalResponse_normalSeries_lower_jets P
      (originalHessenbergRows P i) (originalHessenbergCols P j) K hK he hmax
    have hre := congrArg PowerSeries.constantCoeff hresponse
    simp only [c.normalSeries_constant_apply, map_add, PowerSeries.constantCoeff_C] at hre
    change c.regularResidue (c.originalHessenbergResponse P i j) =
      residueGenerator c.top ⟨K, ne_of_gt hK⟩ + PowerSeries.constantCoeff R at hre
    refine ⟨PowerSeries.constantCoeff R, ?_, 1, Subfield.one_mem _, ?_⟩
    · simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hR 0
    · rw [hre]
      ring
  · apply affineOver_of_mem
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, c.normalSeries_constant_apply] using
      c.originalHessenberg_normalSeries_coeff_mem_below P hB hmax K i j hij
        (lt_of_le_of_ne hdistance he) 0

/-- The complete original Hessenberg determinant has lower earlier jets and an
actual affine first-fresh jet. Every short and eligible interval is covered. -/
theorem originalHessenberg_normalSeries_jets_affine {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (m : ℕ) (hm : 0 < m)
    (hshort : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1), i ≤ j →
      j.val - i.val < m → originalHessenbergDistance (hD := hD) P i j < (K : ℤ))
    (hlong : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1), i ≤ j →
      j.val - i.val ≤ m → originalHessenbergDistance (hD := hD) P i j ≤ (K : ℤ)) :
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      (c.normalSeries (c.originalHessenbergResponse P).det) m := by
  rw [RingHom.map_det]
  change jetsAffineOver _ _ ((c.originalHessenbergResponse P).map c.normalSeries).det m
  let M := (c.originalHessenbergResponse P).map c.normalSeries
  have hshape : IsUpperHessenberg M := by
    intro i j hij
    change c.normalSeries (c.originalHessenbergResponse P i j) = 0
    rw [c.originalHessenbergResponse_isUpperHessenberg P i j hij, map_zero]
  have ha : (c.normalCoefficient)⁻¹ ∈ residueLowerField c.top K :=
    Subfield.inv_mem _ (residueLowerField_mono hK.le c.normalCoordinate_mem_lower.1)
  have hsub : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) = (j : ℕ) + 1 → M i j = PowerSeries.X * PowerSeries.C (c.normalCoefficient)⁻¹ := by
    intro i j hij
    change c.normalSeries (c.originalHessenbergResponse P i j) = _
    let t : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by omega⟩
    have hi : i = t.succ := by apply Fin.ext; exact hij
    have hj : j = t.castSucc := by apply Fin.ext; rfl
    rw [hi, hj]
    exact c.originalHessenberg_normalSeries_subdiagonal P t
  have hshort' : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → j.val - i.val < m →
      ∀ l, PowerSeries.coeff l (M i j) ∈ residueLowerField c.top K := by
    intro i j hij hcost l
    exact c.originalHessenberg_normalSeries_coeff_mem_below P hB hmax K i j hij
      (hshort i j hij hcost) l
  have hlong' : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → j.val - i.val ≤ m →
      affineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
        (PowerSeries.constantCoeff (M i j)) := by
    intro i j hij hcost
    simpa only [M, Matrix.map_apply, c.normalSeries_constant_apply] using
      c.originalHessenberg_residue_affine_of_le P hB hmax K hK i j hij (hlong i j hij hcost)
  exact hessenberg_jets_affine
    (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
    M hshape (c.normalCoefficient)⁻¹ ha hsub m hm hshort' hlong'

/-- A single actual exact-cost distance bound supplies both shorter support and
first-fresh affineness. No independent shorter-jet hypothesis is required. -/
theorem originalHessenberg_jets_affine_from_length_bound {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ originalSelectedCount (hD := hD) P)
    (hbound : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1), i ≤ j →
      j.val - i.val = m → originalHessenbergDistance (hD := hD) P i j ≤ (K : ℤ)) :
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      (c.normalSeries (c.originalHessenbergResponse P).det) m := by
  have hshort := fun i j hij hlen => c.originalHessenbergDistance_short_of_length_bound
    P hB m hmB (K : ℤ) hbound i j hij hlen
  apply c.originalHessenberg_normalSeries_jets_affine P hB hmax K hK m hm hshort
  intro i j hij hcost
  by_cases he : j.val - i.val = m
  · exact hbound i j hij he
  · exact (hshort i j hij (by omega)).le

end SkewCornerDescent.Matrix.SelectedCoordinate
