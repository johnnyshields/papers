/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalMultiplicity
import SkewCornerDescent.Matrix.OriginalResidueFactorization
import SkewCornerDescent.Matrix.ResiduePolynomialBand

/-!
# Component elimination in the actual parent residue

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:component-elimination`). The actual selected multiplicity supplies
exactly one more diagonal response. All literal tops, lower corrections and the nonzero
lower scalar are produced from the original source; no response factorization is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Component elimination for the complete original Jacobi--Trudi determinant, with exact
prime multiplicity and literal protected tops. -/
theorem component_elimination {n : ℕ} (P : Profile n)
    (hd : cellSchur D hD.1 ∣
      (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ t : ℕ, t = primeOrder (cellSchur D hD.1)
        (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det ∧
      0 < t ∧ ∃ K : Fin (t + 1) → ℕ+, ∃ A : Fin (t + 1) → OtherField c.top,
        ∃ F ∈ residueLowerField c.top c.top, F ≠ 0 ∧
          (∀ i, c.top < K i ∧ A i ∈ residuePolynomialBand c.top (K i)) ∧
          c.residueMap P.schur = F * ∏ i, (c.residueMap (MvPolynomial.X (K i)) + A i) ∧
          (∃ ht : t = originalSelectedCount (hD := hD) P, ∀ i,
            (K i : ℤ) = originalHessenbergDistance (hD := hD) P
              (Fin.cast (congrArg (fun x => x + 1) ht) i)
              (Fin.cast (congrArg (fun x => x + 1) ht) i)) ∧
          ∑ i, (K i : ℤ) = P.xi 0 - P.zeta (Fin.last n) + (t : ℤ) * (c.top : ℤ) := by
  have hB := originalSelectedCount_pos_of_dvd (hD := hD) P hd
  let K := fun i : Fin (originalSelectedCount (hD := hD) P + 1) =>
    c.originalHessenbergTop P hB i i le_rfl
  have hresp (i : Fin (originalSelectedCount (hD := hD) P + 1)) :
      ∃ A ∈ residuePolynomialBand c.top (K i),
        c.regularResidue (c.originalHessenbergResponse P i i) =
          c.residueMap (MvPolynomial.X (K i)) + A :=
    c.originalHessenbergResponse_residue_polynomial P hB i i le_rfl hmax
  choose A hA he using hresp
  obtain ⟨F, hF, hF0, hf⟩ := c.originalHessenberg_residue_factorization P hmax
  refine ⟨originalSelectedCount (hD := hD) P, originalSelectedCount_eq_primeOrder P,
    hB, K, A, F, hF, hF0, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, hA i⟩
    have ht := c.originalHessenbergDistance_gt_top P hB i i le_rfl
    have hk : (K i : ℤ) = originalHessenbergDistance (hD := hD) P i i :=
      c.originalHessenbergTop_coe P hB i i le_rfl
    exact_mod_cast (show (c.top : ℤ) < (K i : ℤ) by omega)
  · rw [hf]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => he i)
  · exact ⟨rfl, fun i => c.originalHessenbergTop_coe P hB i i le_rfl⟩
  · have hk (i : Fin (originalSelectedCount (hD := hD) P + 1)) :
        (K i : ℤ) = originalHessenbergDistance (hD := hD) P i i :=
      c.originalHessenbergTop_coe P hB i i le_rfl
    rw [Finset.sum_congr rfl (fun i _ => hk i)]
    exact c.originalHessenbergDistance_sum P

end SkewCornerDescent.Matrix.SelectedCoordinate
