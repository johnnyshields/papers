/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalBlockField
import SkewCornerDescent.Matrix.Hessenberg
import Mathlib.Data.Finset.Sort

/-!
# Actual original Hessenberg response

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`, `lem:component-elimination`). Canonical ordering
of actual selected occurrences produces the full upper-Hessenberg response, with its exact
selected subdiagonal and its upper-triangular residue. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Number of actual selected component occurrences, with multiplicity. -/
noncomputable def originalSelectedCount {n : ℕ} (P : Profile n) : ℕ :=
  Fintype.card (OriginalSelectedBlocks (hD := hD) P)

/-- Every selected occurrence is enumerated in literal original source order. -/
noncomputable def originalSelectedEnumeration {n : ℕ} (P : Profile n) :
    Fin (originalSelectedCount (hD := hD) P) ≃o OriginalSelectedBlocks (hD := hD) P :=
  Fintype.orderIsoFinOfCardEq _ rfl

/-- The produced enumeration is strictly increasing in actual complementary block labels. -/
theorem originalSelectedEnumeration_label_strictMono {n : ℕ} (P : Profile n) :
    StrictMono (fun i => interiorBlock P
      (originalSelectedEnumeration (hD := hD) P i).val.val) := by
  intro i j hij
  have hs := (originalSelectedEnumeration (hD := hD) P).strictMono hij
  have hp : (originalSelectedEnumeration (hD := hD) P i).val.val <
      (originalSelectedEnumeration (hD := hD) P j).val.val := hs
  apply lt_of_le_of_ne (interiorBlock_mono P hp.le)
  intro he
  have hb := originalBlocks_label_injective P he
  have he' := Subtype.ext hb
  exact (ne_of_lt hij) ((originalSelectedEnumeration (hD := hD) P).injective he')

/-- Rows begin with the global top row, followed by the actual selected first rows. -/
noncomputable def originalHessenbergRows {n : ℕ} (P : Profile n) :
    Fin (originalSelectedCount (hD := hD) P + 1) ≃
      Option (OriginalSelectedBlocks (hD := hD) P) :=
  (finSuccEquiv' 0).trans (Equiv.optionCongr
    (originalSelectedEnumeration (hD := hD) P).toEquiv)

/-- Columns end with the global last column, after the actual selected last columns. -/
noncomputable def originalHessenbergCols {n : ℕ} (P : Profile n) :
    Fin (originalSelectedCount (hD := hD) P + 1) ≃
      Option (OriginalSelectedBlocks (hD := hD) P) :=
  (finSuccEquiv' (Fin.last _)).trans (Equiv.optionCongr
    (originalSelectedEnumeration (hD := hD) P).toEquiv)

/-- Successor rows are the actual selected occurrences in their canonical order. -/
theorem originalHessenbergRows_succ {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    originalHessenbergRows (hD := hD) P i.succ =
      some (originalSelectedEnumeration (hD := hD) P i) := by
  change Option.map _ (finSuccEquiv' 0 i.succ) = _
  rw [← Fin.succAbove_zero_apply, finSuccEquiv'_succAbove]
  rfl

/-- Cast-successor columns are the actual selected occurrences in that same order. -/
theorem originalHessenbergCols_castSucc {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    originalHessenbergCols (hD := hD) P i.castSucc =
      some (originalSelectedEnumeration (hD := hD) P i) := by
  change Option.map _ (finSuccEquiv' (Fin.last _) i.castSucc) = _
  rw [← Fin.succAbove_last_apply, finSuccEquiv'_succAbove]
  rfl

/-- The actual full local response, ordered by its literal retained rows and columns. -/
noncomputable def originalHessenbergResponse {n : ℕ} (P : Profile n) :
    Matrix (Fin (originalSelectedCount (hD := hD) P + 1))
      (Fin (originalSelectedCount (hD := hD) P + 1)) c.RegularRing :=
  (c.originalLocalResponse P).submatrix (originalHessenbergRows (hD := hD) P)
    (originalHessenbergCols (hD := hD) P)

/-- Original geometric support, not a supplied Hessenberg hypothesis, gives the actual shape. -/
theorem originalHessenbergResponse_isUpperHessenberg {n : ℕ} (P : Profile n) :
    IsUpperHessenberg (c.originalHessenbergResponse P) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · intro h
    simp only [Fin.val_zero] at h
    omega
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h
      have hi := i.isLt
      simp only [Fin.val_last, Fin.val_succ] at h
      omega
    · intro h
      change c.originalLocalResponse P (originalHessenbergRows (hD := hD) P i.succ)
        (originalHessenbergCols (hD := hD) P j.castSucc) = 0
      rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
      apply c.originalLocalResponse_selected_zero
      apply originalSelectedEnumeration_label_strictMono
      change j.val < i.val
      simp only [Fin.val_castSucc, Fin.val_succ] at h
      omega

/-- Every actual subdiagonal is exactly the selected prime divided by its actual signed cofactor. -/
theorem originalHessenbergResponse_subdiagonal {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    c.regularEmbedding (c.originalHessenbergResponse P i.succ i.castSucc) =
      originalMap (cellSchur D hD.1) / originalMap c.coefficient := by
  change c.regularEmbedding (c.originalLocalResponse P
    (originalHessenbergRows (hD := hD) P i.succ)
    (originalHessenbergCols (hD := hD) P i.castSucc)) = _
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  exact originalLocalResponse_eq_selected_quotient P _ c

/-- The actual subdiagonal vanishes on the selected residue divisor. -/
theorem originalHessenbergResponse_subdiagonal_residue {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    c.regularResidue (c.originalHessenbergResponse P i.succ i.castSucc) = 0 := by
  change c.regularResidue (c.originalLocalResponse P
    (originalHessenbergRows (hD := hD) P i.succ)
    (originalHessenbergCols (hD := hD) P i.castSucc)) = 0
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  exact originalLocalResponse_diagonal_residue_zero P _ c

/-- The actual residue response is upper triangular, including the zero-occurrence boundary. -/
theorem originalHessenbergResponse_residue_upperTriangular {n : ℕ} (P : Profile n) :
    ((c.originalHessenbergResponse P).map c.regularResidue).IsUpperTriangular := by
  intro i j hij
  change c.regularResidue (c.originalHessenbergResponse P i j) = 0
  have hij' : j.val < i.val := hij
  by_cases hs : j.val + 1 = i.val
  · have hi := i.isLt
    let k : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by omega⟩
    have hj : k.castSucc = j := Fin.ext rfl
    have hk : k.succ = i := Fin.ext hs
    rw [← hj, ← hk]
    exact c.originalHessenbergResponse_subdiagonal_residue P k
  · have he := c.originalHessenbergResponse_isUpperHessenberg P i j (by omega)
    rw [he, map_zero]

/-- The actual residue determinant is the full product of its ordered diagonal responses. -/
theorem originalHessenbergResponse_residue_det {n : ℕ} (P : Profile n) :
    ((c.originalHessenbergResponse P).map c.regularResidue).det =
      ∏ i, c.regularResidue (c.originalHessenbergResponse P i i) :=
  Matrix.det_of_isUpperTriangular (c.originalHessenbergResponse_residue_upperTriangular P)

/-- Ordering retained endpoints keeps its exact orientation sign in the local determinant law. -/
theorem originalHessenbergResponse_local_det {n : ℕ} (P : Profile n) :
    (Equiv.Perm.sign ((originalHessenbergCols (hD := hD) P).symm.trans
      (originalHessenbergRows (hD := hD) P)) : c.RegularRing) *
        algebraMap Lambda c.RegularRing (originalSplitMatrix (hD := hD) P).det =
      algebraMap Lambda c.RegularRing (originalRemovedMatrix (hD := hD) P).det *
        (c.originalHessenbergResponse P).det := by
  have he := Matrix.det_reindex (originalHessenbergRows (hD := hD) P).symm
    (originalHessenbergCols (hD := hD) P).symm (c.originalLocalResponse P)
  change (c.originalHessenbergResponse P).det = _ at he
  simp only [Equiv.symm_symm] at he
  rw [he, c.originalSplitMatrix_local_det]
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
