/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.PolynomialBounds

/-!
# Lower-index denominators of the assembled original inverse

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). The complete removed determinant is a
regular denominator bounded by the maximal original component span. Off-diagonal inverse
entries remain full adjugate quotients; no diagonal approximation is used. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- A proper top-right minor has strictly smaller generator support than its component. -/
theorem profile_proper_minor_span_lt {n : ℕ} (P : Profile n) :
    polynomialSpan (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det < (P.topVar : ℕ) := by
  have hb : polynomialSpan (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det ≤ (P.topVar : ℕ) - 1 := by
    apply polynomialSpan_det_le
    intro i j
    apply polynomialSpan_hh_le
    change P.xi i.succ - P.zeta j.castSucc ≤ (((P.topVar : ℕ) - 1 : ℕ) : ℤ)
    have hx := P.xi_strictAnti (Fin.succ_pos i)
    have hz := P.zeta_nonneg j.castSucc
    have ht := P.topVar_coe
    have hp := P.topVar.property
    omega
  have hp := P.topVar.property
  exact lt_of_le_of_lt hb (Nat.sub_lt hp (by decide))

namespace SelectedCoordinate

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The remaining diagonal never exceeds its own complete original component's support. -/
theorem originalRemovedDiagonal_span_le {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    polynomialSpan (originalRemovedDiagonal (hD := hD) P b).det ≤
      polynomialSpan ((jtMatrix (fun j : Fin n => P.xi j.succ)
        (fun j => P.zeta j.castSucc)).toSquareBlock (interiorBlock P)
          (interiorBlock P b.val)).det := by
  by_cases hs : originalBlockSelected (hD := hD) P b
  · have hi := originalBlockSelected_nonempty (hD := hD) P b hs
    rw [originalRemovedDiagonal_det_selected (hD := hD) P b hs,
      originalSelectedMinor_eq_profile P b.val hi, interior_block_det_eq_profile P b.val hi,
      Profile.polynomialSpan_schur]
    exact (profile_proper_minor_span_lt _).le
  · rw [originalRemovedDiagonal_det_nonselected (hD := hD) P b hs]

/-- The actual full removed denominator inherits the maximal original component bound. -/
theorem originalRemovedMatrix_det_span_le {n : ℕ} (P : Profile n) (N : ℕ)
    (hmax : ∀ b : OriginalBlocks P,
      polynomialSpan ((jtMatrix (fun j : Fin n => P.xi j.succ)
        (fun j => P.zeta j.castSucc)).toSquareBlock (interiorBlock P)
          (interiorBlock P b.val)).det ≤ N) :
    polynomialSpan (originalRemovedMatrix (hD := hD) P).det ≤ N := by
  rw [(originalRemovedMatrix_blockTriangular_fst (hD := hD) P).det_fintype]
  apply polynomialSpan_prod_le
  intro b _
  have he := Matrix.det_reindex_self (originalRemovedFiberEquiv (hD := hD) P b).symm
    ((originalRemovedMatrix (hD := hD) P).toSquareBlock Sigma.fst b)
  rw [originalRemovedDiagonal_reindex (hD := hD) P b] at he
  rw [← he]
  exact (originalRemovedDiagonal_span_le P b).trans (hmax b)

/-- Every complete original inverse entry has its exact regular lower-index denominator. -/
theorem originalRemoved_inverse_denominator {n : ℕ} (P : Profile n) (N : ℕ)
    (hmax : ∀ b : OriginalBlocks P,
      polynomialSpan ((jtMatrix (fun j : Fin n => P.xi j.succ)
        (fun j => P.zeta j.castSucc)).toSquareBlock (interiorBlock P)
          (interiorBlock P b.val)).det ≤ N)
    (i j : OriginalRemainingIndices (hD := hD) P) :
    ∃ a b : Lambda,
      ((originalRemovedMatrix (hD := hD) P).map originalMap)⁻¹ i j =
        originalMap a / originalMap b ∧ b ≠ 0 ∧ ¬cellSchur D hD.1 ∣ b ∧ polynomialSpan b ≤ N := by
  let M := originalRemovedMatrix (hD := hD) P
  have hreg : ¬cellSchur D hD.1 ∣ M.det := not_dvd_originalRemovedMatrix (hD := hD) P
  have hne : M.det ≠ 0 := by intro hz; exact hreg (hz ▸ dvd_zero _)
  refine ⟨M.adjugate i j, M.det, ?_, hne, hreg, originalRemovedMatrix_det_span_le P N hmax⟩
  have hd : (M.map originalMap).det = originalMap M.det :=
    (RingHom.map_det originalMap M).symm
  have ha : (M.map originalMap).adjugate = originalMap.mapMatrix M.adjugate :=
    (RingHom.map_adjugate originalMap M).symm
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, hd, ha]
  change (originalMap M.det)⁻¹ * originalMap (M.adjugate i j) = _
  rw [div_eq_mul_inv, mul_comm]

/-- The paper's geometric maximal-component condition supplies every block support bound. -/
theorem originalBlock_span_le_of_components {n : ℕ} (P : Profile n) (N : ℕ)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ N)
    (b : OriginalBlocks P) :
    polynomialSpan ((jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).toSquareBlock (interiorBlock P)
        (interiorBlock P b.val)).det ≤ N := by
  by_cases hi : P.zeta b.val.castSucc < P.xi b.val.succ
  · rw [originalBlock_det_eq_cellSchur P b.val hi,
      polynomialSpan_cellSchur (interiorBlockCells_connected P b.val hi)]
    exact hmax _ ((interior_components_eq_blocks P _).mpr ⟨b.val, hi, rfl⟩)
  · have he : P.xi b.val.succ = P.zeta b.val.castSucc := by
      have := P.zeta_le_xi_succ b.val
      omega
    rw [interior_empty_block_det P b.val he]
    change polynomialSpan (MvPolynomial.C 1) ≤ N
    rw [polynomialSpan_C]
    exact Nat.zero_le _

/-- The full inverse denominator bound uses only the paper's actual component-span hypothesis. -/
theorem originalRemoved_inverse_geometric_denominator {n : ℕ} (P : Profile n) (N : ℕ)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ N)
    (i j : OriginalRemainingIndices (hD := hD) P) :
    ∃ a b : Lambda,
      ((originalRemovedMatrix (hD := hD) P).map originalMap)⁻¹ i j =
        originalMap a / originalMap b ∧ b ≠ 0 ∧ ¬cellSchur D hD.1 ∣ b ∧ polynomialSpan b ≤ N :=
  originalRemoved_inverse_denominator P N (originalBlock_span_le_of_components P N hmax) i j

end SelectedCoordinate
end SkewCornerDescent.Matrix
