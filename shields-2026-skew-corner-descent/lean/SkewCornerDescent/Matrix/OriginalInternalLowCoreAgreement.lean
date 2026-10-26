/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedCoreWords
import SkewCornerDescent.Matrix.OriginalSelectedCoreProfiles
import SkewCornerDescent.Matrix.OriginalInternalSelfJet

/-!
# Actual proper-core jets identify complete incoming prefixes

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
Proper-core polynomials have degree strictly below the selected span.
Their low jets therefore identify the whole two endpoint cores; the
original strip recovery theorem then identifies every complete incoming
coefficient through the selected span, including its boundary degree.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Low proper-core jets suffice to match the full actual incoming prefix
through the selected span. The coefficient at the span is included. -/
theorem originalInternal_incoming_low_coeff_eq_of_core_jets {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hleft : ∀ k, k < (c.top : ℕ) →
      (c.originalSelectedCoreLeft P ⟨i.val, by have := i.isLt; omega⟩).coeff k =
        (c.originalSelectedCoreLeft P ⟨j.val, by have := j.isLt; omega⟩).coeff k)
    (hright : ∀ k, k < (c.top : ℕ) →
      (c.originalSelectedCoreRight P ⟨i.val + 1, by have := i.isLt; omega⟩).coeff k =
        (c.originalSelectedCoreRight P ⟨j.val + 1, by have := j.isLt; omega⟩).coeff k)
    (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    ((c.originalInternalEndpointProfiles P i).1).coeff k =
      ((c.originalInternalEndpointProfiles P j).1).coeff k := by
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let aj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  let bj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val+1, by have := j.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  have hleq : c.originalSelectedCoreLeft P ai = c.originalSelectedCoreLeft P aj := by
    ext l
    by_cases hl : l < (c.top : ℕ)
    · exact hleft l hl
    · exact (c.selected_core_left_coeff_of_top_le _ _ l (by omega)).trans
        (c.selected_core_left_coeff_of_top_le _ _ l (by omega)).symm
  have hreq : c.originalSelectedCoreRight P bi = c.originalSelectedCoreRight P bj := by
    ext l
    by_cases hl : l < (c.top : ℕ)
    · exact hright l hl
    · exact (c.selected_core_right_coeff_of_top_le _ _ l (by omega)).trans
        (c.selected_core_right_coeff_of_top_le _ _ l (by omega)).symm
  by_contra hne
  have hai : ai < bi := by change i.val < i.val+1; omega
  have haj : aj < bj := by change j.val < j.val+1; omega
  have hbound := c.original_profile_discrepancy_gt_top_of_cores P P
    (E ai) (E bi) (E aj) (E bj)
    (originalSelectedEnumeration_label_strictMono P hai).le
    (originalSelectedEnumeration_label_strictMono P haj).le hleq hreq k (Or.inl hne)
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
