/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureWordProduct

/-!
# Both true caps and the entire original residue closure determinant

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:residue-classifier`).
Canonical first and last occurrences give the true cap identities, including coincident
caps. The complete original residue determinant retains every source word factor twice.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The true first closure response is the entire actual source left cap. -/
theorem originalHorizontalClosure_true_left_response {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    c.originalHessenbergResponse Q 0 0 = c.originalHessenbergResponse P 0 0 := by
  let i : Fin (originalSelectedCount (hD := hD) P) := ⟨0, hB⟩
  have hq : (originalClosureSelectedIndex P Q v hQ true i).castSucc =
      (0 : Fin (originalSelectedCount (hD := hD) Q + 1)) := by
    apply Fin.ext
    simp only [originalClosureSelectedIndex, ite_true, zero_add, i,
      Fin.val_castSucc, Fin.val_zero]
  have hp : i.castSucc = (0 : Fin (originalSelectedCount (hD := hD) P + 1)) := by
    apply Fin.ext
    simp only [i, Fin.val_castSucc, Fin.val_zero]
  simpa only [hq, hp] using c.originalHorizontalClosure_ordered_left_response P Q v hQ i

/-- The true last closure response is the entire actual source right cap. -/
theorem originalHorizontalClosure_true_right_response {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    c.originalHessenbergResponse Q (Fin.last _) (Fin.last _) =
      c.originalHessenbergResponse P (Fin.last _) (Fin.last _) := by
  let i : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  have hq : (originalClosureSelectedIndex P Q v hQ false i).succ =
      Fin.last (originalSelectedCount (hD := hD) Q) := by
    apply Fin.ext
    change originalSelectedCount (hD := hD) P +
      (originalSelectedCount (hD := hD) P - 1) + 1 = originalSelectedCount (hD := hD) Q
    have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
    omega
  have hp : i.succ = Fin.last (originalSelectedCount (hD := hD) P) := by
    apply Fin.ext
    change originalSelectedCount (hD := hD) P - 1 + 1 = originalSelectedCount (hD := hD) P
    omega
  simpa only [hq, hp] using c.originalHorizontalClosure_ordered_right_response P Q v hQ i

/-- The two actual exterior occurrences are unchanged as a product, not deduplicated as classes. -/
theorem originalHorizontalClosure_true_cap_product {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    c.originalTrueCapProduct Q = c.originalTrueCapProduct P := by
  unfold originalTrueCapProduct
  rw [c.originalHorizontalClosure_true_left_response P Q v hQ hB,
    c.originalHorizontalClosure_true_right_response P Q v hQ hB]

/-- The complete actual closure residue determinant has both full internal source inventories. -/
theorem originalHorizontalClosure_response_residue_det {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    ((c.originalHessenbergResponse Q).map c.regularResidue).det =
      c.originalTrueCapProduct P * (∏ i, c.originalInternalResidue P i) ^ 2 *
        c.regularResidue (c.originalHessenbergResponse Q middle middle) := by
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by
    rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
    omega
  rw [c.originalHessenbergResponse_residue_det,
    c.originalHessenberg_residue_cap_product Q hBQ,
    c.originalHorizontalClosure_true_cap_product P Q v hQ hB,
    c.originalHorizontalClosure_internal_residue_product P Q v hQ hB]
  exact (mul_assoc _ _ _).symm

end SkewCornerDescent.Matrix.SelectedCoordinate
