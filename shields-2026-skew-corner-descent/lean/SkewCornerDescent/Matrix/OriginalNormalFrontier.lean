/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalMinimumCost
import SkewCornerDescent.Matrix.HessenbergNormalFrontier

/-!
# Actual original determinant first-fresh frontier

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The entire original ordered determinant has its exact signed cost-frontier
formula, with genuine residue entries and its actual selected cofactor.
The cyclic word inventory and its cancellation are separate obligations.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual determinant's first fresh derivative is its complete permutation frontier.
Every shorter interval is discharged by its literal endpoint inequality; all normal-dependent
inverse entries and both true caps remain in the original matrix. -/
theorem originalHessenberg_normalSeries_coeff_frontier {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (m : ℕ)
    (hdistance : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      originalHessenbergDistance (hD := hD) P i j < (K : ℤ)) :
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m (c.normalSeries (c.originalHessenbergResponse P).det)) =
      ∑ σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P + 1)),
        if (∀ i : Fin (originalSelectedCount (hD := hD) P + 1),
            (i : ℕ) ≤ (σ i : ℕ) + 1) ∧
            (Finset.univ.filter (fun i => (σ i : ℕ) < (i : ℕ))).card = m then
          (Equiv.Perm.sign σ : ℤ) •
            ((c.normalCoefficient)⁻¹ ^ m *
              residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
                (∏ i ∈ Finset.univ.filter (fun i => ¬ (σ i : ℕ) < (i : ℕ)),
                  c.regularResidue (c.originalHessenbergResponse P i (σ i))))
        else 0 := by
  classical
  rw [RingHom.map_det]
  change residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
    (PowerSeries.coeff m ((c.originalHessenbergResponse P).map c.normalSeries).det) = _
  have he := hessenberg_coeff_deriv_frontier (residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩)
    ((c.originalHessenbergResponse P).map c.normalSeries)
    (a := (c.normalCoefficient)⁻¹) (m := m)
  have hshape : IsUpperHessenberg ((c.originalHessenbergResponse P).map c.normalSeries) := by
    intro i j hij
    change c.normalSeries (c.originalHessenbergResponse P i j) = 0
    rw [c.originalHessenbergResponse_isUpperHessenberg P i j hij, map_zero]
  have ha : residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩ (c.normalCoefficient)⁻¹ = 0 := by
    apply residueGeneratorDeriv_lower
    exact Subfield.inv_mem _ (residueLowerField_mono hK.le c.normalCoordinate_mem_lower.1)
  have hsub : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) = (j : ℕ) + 1 →
      c.normalSeries (c.originalHessenbergResponse P i j) =
        PowerSeries.X * PowerSeries.C (c.normalCoefficient)⁻¹ := by
    intro i j hij
    let t : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by omega⟩
    have hi : i = t.succ := by apply Fin.ext; exact hij
    have hj : j = t.castSucc := by apply Fin.ext; rfl
    rw [hi, hj]
    exact c.originalHessenberg_normalSeries_subdiagonal P t
  have hshort : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m → ∀ l,
      residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff l (c.normalSeries (c.originalHessenbergResponse P i j))) = 0 := by
    intro i j hij hcost l
    exact c.originalHessenberg_normalSeries_derivative_below P hB hmax K hK i j hij
      (hdistance i j hij hcost) l
  simpa only [Matrix.map_apply, c.normalSeries_constant_apply, smul_eq_mul,
    zsmul_eq_mul] using
    he hshape ha hsub hshort

end SkewCornerDescent.Matrix.SelectedCoordinate
