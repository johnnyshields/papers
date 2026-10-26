/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureResponseWord
import SkewCornerDescent.Matrix.OriginalCapNormalization

/-!
# Positional product of the actual closure's full internal response word

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:residue-classifier`).
The product uses two complete source words and the actual central response. Equal values
are counted at both original positions, before any normal or residue specialization. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both source internal-word lists and the unique actual central position exhaust the closure. -/
noncomputable def originalClosureInternalEquiv {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    (Fin (originalSelectedCount (hD := hD) P - 1) ⊕ Fin 1) ⊕
      Fin (originalSelectedCount (hD := hD) P - 1) ≃
        Fin (originalSelectedCount (hD := hD) Q - 1) :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (by
      have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
      omega))

/-- The full regular-ring product retains both copies and their one literal joining response. -/
theorem originalHorizontalClosure_internal_response_product {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    (∏ i, c.originalInternalResponse Q i) =
      (∏ i, c.originalInternalResponse P i) ^ 2 *
        c.originalHessenbergResponse Q middle middle := by
  classical
  let e := originalClosureInternalEquiv P Q v hQ hB
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by
      rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
  have hup (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
      c.originalInternalResponse Q (e (.inl (.inl i))) = c.originalInternalResponse P i := by
    have hi : e (.inl (.inl i)) = ⟨i.val, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
        have hi := i.isLt
        omega⟩ := rfl
    rw [hi]
    simpa only [ite_true, zero_add] using
      c.originalHorizontalClosure_internal_response_copy P Q v hQ true i
  have hlow (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
      c.originalInternalResponse Q (e (.inr i)) = c.originalInternalResponse P i := by
    have hi : e (.inr i) = ⟨originalSelectedCount (hD := hD) P + i.val, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
        have hi := i.isLt
        omega⟩ := by
      apply Fin.ext
      change (originalSelectedCount (hD := hD) P - 1 + 1) + i.val =
        originalSelectedCount (hD := hD) P + i.val
      omega
    rw [hi]
    simpa only [Bool.false_eq_true, ite_false] using
      c.originalHorizontalClosure_internal_response_copy P Q v hQ false i
  have hmiddle : c.originalInternalResponse Q (e (.inl (.inr 0))) =
      c.originalHessenbergResponse Q middle middle := by
    unfold originalInternalResponse
    congr 1 <;> apply Fin.ext <;>
      change originalSelectedCount (hD := hD) P - 1 + (0 : Fin 1).val + 1 =
        originalSelectedCount (hD := hD) P <;>
      simp only [Fin.val_zero] <;> omega
  rw [Fintype.prod_equiv e.symm (c.originalInternalResponse Q)
    (fun i => c.originalInternalResponse Q (e i))
    (fun i => by rw [Equiv.apply_symm_apply])]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [hup, hlow, Fin.prod_univ_one, hmiddle]
  ring

/-- The complete internal residue product comes from the full regular-ring word identity. -/
theorem originalHorizontalClosure_internal_residue_product {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    (∏ i, c.originalInternalResidue Q i) =
      (∏ i, c.originalInternalResidue P i) ^ 2 *
        c.regularResidue (c.originalHessenbergResponse Q middle middle) := by
  have he := congrArg c.regularResidue
    (c.originalHorizontalClosure_internal_response_product P Q v hQ hB)
  simpa only [map_prod, map_mul, map_pow,
    originalInternalResponse, originalInternalResidue] using he

end SkewCornerDescent.Matrix.SelectedCoordinate
