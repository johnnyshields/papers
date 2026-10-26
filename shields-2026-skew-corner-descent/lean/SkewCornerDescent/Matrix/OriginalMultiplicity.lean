/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalHessenbergInventory
import SkewCornerDescent.Matrix.PrimeOrder

/-!
# Exact selected multiplicity in the original complementary determinant

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:component-elimination`). The selected occurrence count is the
prime order of the actual complementary determinant. Empty unit blocks contribute zero,
and repeated equal component functions contribute separately. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

attribute [local instance] Classical.propDecidable

/-- The complete original polynomial of one canonical complementary block. -/
noncomputable def originalBlockPolynomial {n : ℕ} (P : Profile n) (b : OriginalBlocks P) : Lambda :=
  ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
    (interiorBlock P) (interiorBlock P b.val)).det

/-- Canonical representatives count every complete original block exactly once. -/
theorem interior_det_eq_original_product {n : ℕ} (P : Profile n) :
    (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      ∏ b : OriginalBlocks P, originalBlockPolynomial P b := by
  rw [interior_det_eq_block_product]
  symm
  apply Finset.prod_bij (fun b _ => interiorBlock P b.val)
  · intro b _
    exact Finset.mem_image.mpr ⟨b.val, Finset.mem_univ _, rfl⟩
  · intro b _ d _ he
    exact originalBlocks_label_injective P he
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨⟨interiorBlockFirst P i, interiorBlockFirst_idem P i⟩, Finset.mem_univ _, ?_⟩
    exact (mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i)
  · intro b _
    rfl

/-- No complete original block vanishes, including literal empty rows. -/
theorem originalBlockPolynomial_ne_zero {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    originalBlockPolynomial P b ≠ 0 := by
  by_cases hi : P.zeta b.val.castSucc < P.xi b.val.succ
  · rw [originalBlockPolynomial, interior_block_det_eq_profile P b.val hi]
    exact (irreducible_schur _ (interiorBlockProfile P b.val hi)).ne_zero
  · have he : P.xi b.val.succ = P.zeta b.val.castSucc := by
      have := P.zeta_le_xi_succ b.val
      omega
    rw [originalBlockPolynomial, interior_empty_block_det P b.val he]
    exact one_ne_zero

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A selected complete block contributes exactly one, and every other original block zero. -/
theorem originalBlock_primeOrder {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    primeOrder (cellSchur D hD.1) (originalBlockPolynomial P b) =
      if originalBlockSelected (hD := hD) P b then 1 else 0 := by
  by_cases hs : originalBlockSelected (hD := hD) P b
  · rw [ite_eq_left hs]
    have hi := originalBlockSelected_nonempty (hD := hD) P b hs
    have he := originalSelectedProfile_schur P ⟨b, hs⟩
    rw [originalBlockPolynomial, interior_block_det_eq_profile P b.val hi, he]
    exact primeOrder_self (irreducible_cellSchur hD).prime
  · rw [ite_eq_right hs]
    exact primeOrder_eq_zero_of_not_dvd hs

/-- The actual complementary determinant's order equals the produced occurrence count. -/
theorem originalSelectedCount_eq_primeOrder {n : ℕ} (P : Profile n) :
    originalSelectedCount (hD := hD) P =
      primeOrder (cellSchur D hD.1)
        (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det := by
  rw [interior_det_eq_original_product]
  have hprod (s : Finset (OriginalBlocks P)) :
      primeOrder (cellSchur D hD.1) (∏ b ∈ s, originalBlockPolynomial P b) =
        ∑ b ∈ s, primeOrder (cellSchur D hD.1) (originalBlockPolynomial P b) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.prod_empty, Finset.sum_empty]
        exact primeOrder_eq_zero_of_not_dvd (irreducible_cellSchur hD).not_dvd_one
    | @insert b s hb ih =>
        rw [Finset.prod_insert hb, Finset.sum_insert hb,
          primeOrder_mul (irreducible_cellSchur hD).prime
            (originalBlockPolynomial_ne_zero P b)
            (Finset.prod_ne_zero_iff.mpr (fun d _ => originalBlockPolynomial_ne_zero P d)), ih]
  rw [hprod, Finset.sum_congr rfl (fun b _ => originalBlock_primeOrder (hD := hD) P b)]
  simp only [originalSelectedCount, OriginalSelectedBlocks, Fintype.card_subtype,
    Finset.sum_boole]
  rfl

/-- Divisibility of the actual complementary determinant produces a selected occurrence. -/
theorem originalSelectedCount_pos_of_dvd {n : ℕ} (P : Profile n)
    (hd : cellSchur D hD.1 ∣
      (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det) :
    0 < originalSelectedCount (hD := hD) P := by
  rw [interior_det_eq_original_product] at hd
  obtain ⟨b, _, hb⟩ := ((irreducible_cellSchur hD).prime.dvd_finsetProd_iff
    (originalBlockPolynomial P)).mp hd
  exact originalSelectedCount_pos P ⟨b, hb⟩

/-- A positive actual selected count produces divisibility of the complete corner core. -/
theorem originalSelectedCorner_dvd_of_pos {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    cellSchur D hD.1 ∣
      (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det := by
  by_contra hn
  have hz := primeOrder_eq_zero_of_not_dvd hn
  have hc := originalSelectedCount_eq_primeOrder (hD := hD) P
  rw [hz] at hc
  omega

/-- The actual corner core is nonempty and singular on the selected chart.
Both facts are supplied by an actual selected occurrence, not by rank assumptions. -/
theorem originalSelectedCorner_residue_singular (c : SelectedCoordinate D hD) {n : ℕ}
    (P : Profile n) (hB : 0 < originalSelectedCount (hD := hD) P) :
    0 < n ∧ ((jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).map c.residueMap).det = 0 := by
  have hb : 0 < Fintype.card (OriginalSelectedBlocks (hD := hD) P) := hB
  obtain ⟨b⟩ := Fintype.card_pos_iff.mp hb
  constructor
  · have hi := b.val.val.isLt
    omega
  · have hd := originalSelectedCorner_dvd_of_pos (hD := hD) P hB
    have hz := (c.residueMap_eq_zero_iff _).mpr hd
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using hz

end SelectedCoordinate
end SkewCornerDescent.Matrix
