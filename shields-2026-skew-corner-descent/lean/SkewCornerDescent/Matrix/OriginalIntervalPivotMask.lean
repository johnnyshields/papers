/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalIntervalRowOrdinals

/-!
# Exact selected-pivot masks in the original retained row frame

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual removed rows and columns differ by one precisely in a selected
proper strip. Between consecutive selected occurrences this flag is
determined by the two physical endpoint strips in the complete row frame.
No matrix pivot or empty unit vertex is omitted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
attribute [local instance] Classical.propDecidable
variable {D : Diagram} {hD : IsConnectedSkew D}

private theorem selectedRowMask_normalize (s e l k R : ℕ)
    (hl : s + k = l) (hs : s ≤ R) (he : s ≤ e) :
    (R ≤ l ∨ e ≤ R) ↔ (R-s ≤ k ∨ e-s ≤ R-s) := by omega

/-- The actual retained row-column rank offset is exactly the selected-strip flag. -/
theorem originalRemoved_row_col_rank_difference {n : ℕ} (P : Profile n)
    (r : OriginalRemainingIndices (hD := hD) P) :
    (originalRemovedRow P r.1 r.2).val = (originalRemovedCol P r.1 r.2).val +
      if originalBlockSelected (hD := hD) P r.1 then 1 else 0 := by
  simp only [originalRemovedRow, originalRemovedCol, interiorSliceIndex]
  rw [originalRemovedRowPosition_val, originalRemovedColPosition_val]
  split_ifs <;> omega

/-- Only the two actual endpoint proper strips are selected in a consecutive interval. -/
theorem original_interval_selected_endpoint_iff {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) (hij : j.val = i.val + 1)
    (r : OriginalResponseInterval P (some (originalSelectedEnumeration P i))
      (some (originalSelectedEnumeration P j))) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P j
    originalBlockSelected (hD := hD) P r.val.val.1 ↔
      originalRemovedRow P r.val.val.1 r.val.val.2 ≤ interiorBlockLast P a.val.val ∨
        b.val.val ≤ originalRemovedRow P r.val.val.1 r.val.val.2 := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P j
  have hlabels : interiorBlock P a.val.val ≤ interiorBlock P r.val.val.1.val ∧
      interiorBlock P r.val.val.1.val ≤ interiorBlock P b.val.val := by
    have hl := r.property
    have hu := r.val.property
    change (interiorBlock P a.val.val : ℤ) - 1 < (interiorBlock P r.val.val.1.val : ℤ) at hl
    change (interiorBlock P r.val.val.1.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1 at hu
    omega
  constructor
  · intro hsel
    let s : OriginalSelectedBlocks (hD := hD) P := ⟨r.val.val.1, hsel⟩
    rcases original_consecutive_selected_between P i j hij s hlabels with hs | hs
    · have he := congrArg (fun s : OriginalSelectedBlocks (hD := hD) P =>
        interiorBlock P s.val.val) hs
      apply Or.inl
      apply (interiorBlock_label_le_iff_le_last P a.val.val _).mp
      rw [originalRemovedRow_block]
      exact he.le
    · have he := congrArg (fun s : OriginalSelectedBlocks (hD := hD) P =>
        interiorBlock P s.val.val) hs
      apply Or.inr
      have hh := (interiorBlock_label_le_iff_first_le P b.val.val
        (originalRemovedRow P r.val.val.1 r.val.val.2)).mp (by
          rw [originalRemovedRow_block]
          exact he.ge)
      simpa only [b.val.property] using hh
  · intro hrow
    rcases hrow with hrow | hrow
    · have hle := (interiorBlock_label_le_iff_le_last P a.val.val _).mpr hrow
      rw [originalRemovedRow_block] at hle
      have hblock : r.val.val.1 = a.val := originalBlocks_label_injective P
        (le_antisymm hle hlabels.1)
      rw [hblock]
      exact a.property
    · have hge := (interiorBlock_label_le_iff_first_le P b.val.val _).mpr
        (by simpa only [b.val.property] using hrow)
      rw [originalRemovedRow_block] at hge
      have hblock : r.val.val.1 = b.val := originalBlocks_label_injective P
        (le_antisymm hlabels.2 hge)
      rw [hblock]
      exact b.property

/-- Exact relative row ordinals determine the actual selected proper-strip mask. -/
theorem originalInternal_selected_row_ordinal_iff {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (r : OriginalInternalInterval P i) :
    originalBlockSelected (hD := hD) P r.val.val.1 ↔
      (originalInternalRowOrdinal P i r).val.val ≤ interiorBlockLength P
        (originalSelectedEnumeration (hD := hD) P ⟨i.val, by have := i.isLt; omega⟩).val.val ∨
      originalInternalRowEnd P i - originalInternalRowStart P i ≤
        (originalInternalRowOrdinal P i r).val.val := by
  let a := originalSelectedEnumeration (hD := hD) P ⟨i.val, by have := i.isLt; omega⟩
  have hm := original_interval_selected_endpoint_iff (hD := hD) P
    ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val+1, by have := i.isLt; omega⟩ rfl r
  change originalBlockSelected (hD := hD) P r.val.val.1 ↔
    (originalRemovedRow P r.val.val.1 r.val.val.2).val ≤ (interiorBlockLast P a.val.val).val ∨
      originalInternalRowEnd P i ≤ (originalRemovedRow P r.val.val.1 r.val.val.2).val at hm
  have hfirst := Fin.le_def.mp (interiorBlockFirst_le_last P a.val.val)
  rw [a.val.property] at hfirst
  have hlen : originalInternalRowStart P i + interiorBlockLength P a.val.val =
      (interiorBlockLast P a.val.val).val := by
    unfold interiorBlockLength
    rw [a.val.property]
    change a.val.val.val + ((interiorBlockLast P a.val.val).val - a.val.val.val) = _
    omega
  have hb := originalInternal_interval_row_bounds P i r
  have hf := originalInternal_row_frame_bounds P i
  change originalBlockSelected (hD := hD) P r.val.val.1 ↔
    (originalRemovedRow P r.val.val.1 r.val.val.2).val - originalInternalRowStart P i ≤
        interiorBlockLength P a.val.val ∨
      originalInternalRowEnd P i - originalInternalRowStart P i ≤
        (originalRemovedRow P r.val.val.1 r.val.val.2).val - originalInternalRowStart P i
  exact hm.trans (selectedRowMask_normalize _ _ _ _ _ hlen hb.1 hf.1.le)

end SkewCornerDescent.Matrix.SelectedCoordinate
