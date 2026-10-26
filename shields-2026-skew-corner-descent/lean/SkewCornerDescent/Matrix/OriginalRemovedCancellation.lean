/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalRemovedFactors

/-!
# Full normal cancellation from actual corner inventory

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-words`, `lem:residue-classifier`). Equal powers of actual
corner inventories force equal powers of complete removed determinants as polynomial
identities. Normal substitution therefore retains the cancellation at every order, not only
at residue. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The complementary determinant contains exactly the selected prime occurrences and all
nonselected original blocks, including empty pivots. -/
theorem originalComplementary_det_inventory {n : ℕ} (P : Profile n) :
    (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ originalSelectedCount (hD := hD) P *
        ∏ b ∈ Finset.univ.filter (fun b : OriginalBlocks P =>
          ¬ originalBlockSelected (hD := hD) P b), originalBlockPolynomial P b := by
  rw [interior_det_eq_original_product]
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset (OriginalBlocks P)) (originalBlockSelected (hD := hD) P)]
  congr 1
  have hf : (Finset.univ.filter (originalBlockSelected (hD := hD) P)).card =
      originalSelectedCount (hD := hD) P := by
    simp only [originalSelectedCount, OriginalSelectedBlocks, Fintype.card_subtype]
  rw [← hf]
  calc
    _ = ∏ _b ∈ Finset.univ.filter (originalBlockSelected (hD := hD) P),
        cellSchur D hD.1 := by
      apply Finset.prod_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      have hi := originalBlockSelected_nonempty (hD := hD) P b hs
      rw [originalBlockPolynomial, interior_block_det_eq_profile P b.val hi]
      exact originalSelectedProfile_schur P ⟨b, hs⟩
    _ = _ := Finset.prod_const _

/-- Replacing every selected prime by its actual proper cofactor gives the complete removed
factor identity before normal substitution. -/
theorem originalRemovedMatrix_cross_cofactor {n : ℕ} (P : Profile n) :
    cellSchur D hD.1 ^ originalSelectedCount (hD := hD) P *
        (originalRemovedMatrix (hD := hD) P).det =
      cellSchur (diagramInterior D) hD.1.interior ^ originalSelectedCount (hD := hD) P *
        (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det := by
  rw [originalRemovedMatrix_det_inventory (hD := hD) P,
    originalComplementary_det_inventory (hD := hD) P]
  ring

/-- Equal powers of actual corner inventories cancel the complete removed factors. The
selected multiplicity balance is derived from prime order, not carried as a premise. -/
theorem originalRemovedMatrix_pair_power {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b v : ℕ)
    (hcorner : (jtMatrix (fun j : Fin n => P.xi j.succ)
          (fun j => P.zeta j.castSucc)).det ^ v =
      (jtMatrix (fun j : Fin m => Q.xi j.succ)
          (fun j => Q.zeta j.castSucc)).det ^ b) :
    (originalRemovedMatrix (hD := hD) P).det ^ v =
      (originalRemovedMatrix (hD := hD) Q).det ^ b := by
  let ψ := cellSchur D hD.1
  let a := cellSchur (diagramInterior D) hD.1.interior
  let B := originalSelectedCount (hD := hD) P
  let C := originalSelectedCount (hD := hD) Q
  have hp : Prime ψ := (irreducible_cellSchur hD).prime
  have ht := congrArg (primeOrder ψ) hcorner
  rw [primeOrder_pow hp, primeOrder_pow hp,
    ← originalSelectedCount_eq_primeOrder (hD := hD) P,
    ← originalSelectedCount_eq_primeOrder (hD := hD) Q] at ht
  have hcount : B * v = C * b := by
    simpa only [B, C, mul_comm] using ht
  have hP := congrArg (fun z : Lambda => z ^ v)
    (originalRemovedMatrix_cross_cofactor (hD := hD) P)
  have hQ := congrArg (fun z : Lambda => z ^ b)
    (originalRemovedMatrix_cross_cofactor (hD := hD) Q)
  simp only [mul_pow, ← pow_mul] at hP hQ
  change ψ ^ (B * v) * _ = a ^ (B * v) * _ at hP
  change ψ ^ (C * b) * _ = a ^ (C * b) * _ at hQ
  apply mul_left_cancel₀ (pow_ne_zero (B * v) hp.ne_zero)
  calc
    _ = a ^ (B * v) *
        (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det ^ v := hP
    _ = a ^ (C * b) *
        (jtMatrix (fun j : Fin m => Q.xi j.succ) (fun j => Q.zeta j.castSucc)).det ^ b := by
      rw [hcount, hcorner]
    _ = ψ ^ (B * v) * (originalRemovedMatrix (hD := hD) Q).det ^ b := by
      rw [hcount]
      exact hQ.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
