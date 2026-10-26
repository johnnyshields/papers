/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SelectedCoreLiteralTransport
import SkewCornerDescent.Matrix.OriginalHessenbergTops
import SkewCornerDescent.Matrix.OriginalWindowGapAssembly
import SkewCornerDescent.Matrix.OriginalCapNormalization

/-!
# Complete source-selected proper-core words

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Each word entry is the literal source component's own canonical proper core.
Raw gradients supply common self-products and shifted internal mixed products;
complete literal windows supply the matched proper-core entry. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Proper incoming core polynomial of an actual selected occurrence. -/
noncomputable def originalSelectedCoreLeft {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) : Polynomial (OtherField c.top) :=
  let b := originalSelectedEnumeration (hD := hD) P i
  c.selectedCoreLeftPolynomial
    (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
    (originalSelectedProfile_schur P b).symm

/-- Proper outgoing core polynomial of the same actual selected occurrence. -/
noncomputable def originalSelectedCoreRight {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) : Polynomial (OtherField c.top) :=
  let b := originalSelectedEnumeration (hD := hD) P i
  c.selectedCoreRightPolynomial
    (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
    (originalSelectedProfile_schur P b).symm

/-- Both literal source core entries are normalized, including selected rows. -/
theorem originalSelectedCore_constants {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    (c.originalSelectedCoreLeft P i).coeff 0 = 1 ∧
      (c.originalSelectedCoreRight P i).coeff 0 = 1 := by
  exact ⟨c.selected_core_left_constant _ _, c.selected_core_right_constant _ _⟩

/-- Every source-selected self-product has the same low jet, supplied by the
single selected function's raw gradient. -/
theorem originalSelectedCore_self_products {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) (k : ℕ) (hk : k < (c.top : ℕ)) :
    (c.originalSelectedCoreLeft P i * c.originalSelectedCoreRight P i).coeff k =
      (c.originalSelectedCoreLeft P j * c.originalSelectedCoreRight P j).coeff k := by
  exact c.selected_core_polynomial_product_coeff_eq _ _ _ _ k hk

/-- Equality of actual internal source responses and their tops produces equality
of their own mixed core jets, with the strict twice-span bound supplied by the
selected component geometry. -/
theorem originalSelectedCore_internal_products {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hspan : originalHessenbergDistance (hD := hD) P
        ⟨i.val + 1, by omega⟩ ⟨i.val + 1, by omega⟩ =
      originalHessenbergDistance (hD := hD) P
        ⟨j.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩)
    (hresponse : c.originalInternalResidue P i = c.originalInternalResidue P j)
    (k : ℕ) (hk : k < (c.top : ℕ)) :
    (c.originalSelectedCoreLeft P ⟨i.val, by omega⟩ *
      c.originalSelectedCoreRight P ⟨i.val + 1, by omega⟩).coeff k =
    (c.originalSelectedCoreLeft P ⟨j.val, by omega⟩ *
      c.originalSelectedCoreRight P ⟨j.val + 1, by omega⟩).coeff k := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by omega⟩
  let a' : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by omega⟩
  let b' : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val + 1, by omega⟩
  have hab : a < b := by change i.val < i.val + 1; omega
  have hab' : a' < b' := by change j.val < j.val + 1; omega
  have hK := c.originalHessenbergDistance_selected_gt_twice_top P a b hab
  have hs := hspan
  have hr := hresponse
  change originalHessenbergDistance (hD := hD) P a.succ b.castSucc =
    originalHessenbergDistance (hD := hD) P a'.succ b'.castSucc at hs
  change c.regularResidue (c.originalHessenbergResponse P a.succ b.castSucc) =
    c.regularResidue (c.originalHessenbergResponse P a'.succ b'.castSucc) at hr
  simp only [originalHessenbergDistance, originalHessenbergResponse, Matrix.submatrix_apply,
    originalHessenbergRows_succ, originalHessenbergCols_castSucc] at hs hr hK
  exact c.original_equal_response_core_products P P
    (originalSelectedEnumeration P a) (originalSelectedEnumeration P b)
    (originalSelectedEnumeration P a') (originalSelectedEnumeration P b')
    (originalSelectedEnumeration_label_strictMono P hab).le
    (originalSelectedEnumeration_label_strictMono P hab').le hs hK hr k hk.le

/-- Literal selected-component translation, not function equality, identifies
both complete source core entries. -/
theorem originalSelectedCore_literal_translation {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P
      (originalSelectedEnumeration (hD := hD) P j).val.val) =
      interiorBlockCells P (originalSelectedEnumeration (hD := hD) P i).val.val) :
    c.originalSelectedCoreLeft P j = c.originalSelectedCoreLeft P i ∧
      c.originalSelectedCoreRight P j = c.originalSelectedCoreRight P i := by
  exact c.original_selected_core_polynomials_of_translate P P
    (originalSelectedEnumeration P j) (originalSelectedEnumeration P i) v he

/-- Complete matched windows produce the actual repeated source core entry. -/
theorem originalWindow_selected_core_words {n m : ℕ} (P : Profile n) (W : Profile m)
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (i j : Fin (originalSelectedCount (hD := hD) P))
    (hji : j.val = i.val + (originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W)) :
    c.originalSelectedCoreLeft P j = c.originalSelectedCoreLeft P i ∧
      c.originalSelectedCoreRight P j = c.originalSelectedCoreRight P i := by
  have hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
    rw [hW]
    exact isSkew_translate u W.isConnectedSkew_cells.1
  have h0 := (originalProfile_interior_boundary_gaps P).1
  have hL := (originalProfile_interior_boundary_gaps P).2
  have hq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hq hx
  have hLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hLq hx
  have hcount := originalWindow_selected_count (hD := hD) P W 0 (P.xi 0 - q) u hW h0 hLq'
  exact c.originalSelectedCore_literal_translation P i j v
    (originalWindow_selected_index_translation P q v hv hprefix hwindow h0 hq' hLq' hL i j
      (by rw [hcount]; exact hji))

/-- Equality of one low proper-core jet recovers the normalized literal selected
component, rather than merely its common selected function. -/
theorem originalSelectedCore_literal_of_left_jet {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P))
    (hjet : ∀ k < (c.top : ℕ),
      (c.originalSelectedCoreLeft P i).coeff k = (c.originalSelectedCoreLeft P j).coeff k) :
    (interiorBlockProfile P (originalSelectedEnumeration (hD := hD) P i).val.val
      (originalBlockSelected_nonempty P (originalSelectedEnumeration P i).val
        (originalSelectedEnumeration P i).property)).cells =
    (interiorBlockProfile P (originalSelectedEnumeration (hD := hD) P j).val.val
      (originalBlockSelected_nonempty P (originalSelectedEnumeration P j).val
        (originalSelectedEnumeration P j).property)).cells := by
  exact c.selected_core_literal_of_left_jet _ _ _ _ hjet

end SkewCornerDescent.Matrix.SelectedCoordinate
