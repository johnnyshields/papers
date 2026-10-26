/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalIntervalRowCoverage

/-!
# Exact physical row ordinals of a complete retained interval

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every actual retained interval is bijective with its complete source-row
range after removing exactly the two selected pivots. The ordinal inverse
is supplied by the original global row partition, including zero-length
proper selected strips and the empty two-pivot boundary. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The original removed source rows occur exactly once. -/
theorem originalRemovedRow_injective {n : ℕ} (P : Profile n) :
    Function.Injective (fun r : OriginalRemainingIndices (hD := hD) P =>
      originalRemovedRow P r.1 r.2) := by
  intro r s he
  have h : originalRowSplitEquiv (hD := hD) P (.inr r) =
      originalRowSplitEquiv (hD := hD) P (.inr s) := by
    rw [originalRowSplitEquiv_removed, originalRowSplitEquiv_removed]
    exact congrArg Fin.succ he
  exact Sum.inr.inj ((originalRowSplitEquiv (hD := hD) P).injective h)

/-- A removed source row is never one of the retained selected pivots. -/
theorem originalRemovedRow_ne_selected {n : ℕ} (P : Profile n)
    (r : OriginalRemainingIndices (hD := hD) P) (s : OriginalSelectedBlocks (hD := hD) P) :
    originalRemovedRow P r.1 r.2 ≠ s.val.val := by
  intro he
  have h : originalRowSplitEquiv (hD := hD) P (.inr r) =
      originalRowSplitEquiv (hD := hD) P (.inl (some s)) := by
    rw [originalRowSplitEquiv_removed, originalRowSplitEquiv_selected, he]
  have hbad := (originalRowSplitEquiv (hD := hD) P).injective h
  cases hbad

/-- Physical source-row rank of the initial selected pivot. -/
noncomputable def originalInternalRowStart {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) : ℕ :=
  (originalSelectedEnumeration (hD := hD) P ⟨i.val, by have := i.isLt; omega⟩).val.val.val

/-- Physical source-row rank of the terminal selected pivot. -/
noncomputable def originalInternalRowEnd {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) : ℕ :=
  (originalSelectedEnumeration (hD := hD) P ⟨i.val+1, by have := i.isLt; omega⟩).val.val.val

/-- Last physical source row of the terminal selected component. -/
noncomputable def originalInternalRowLast {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) : ℕ :=
  (interiorBlockLast P (originalSelectedEnumeration (hD := hD) P
    ⟨i.val+1, by have := i.isLt; omega⟩).val.val).val

/-- The actual consecutive selected row frame is ordered and lies in the source. -/
theorem originalInternal_row_frame_bounds {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    originalInternalRowStart P i < originalInternalRowEnd P i ∧
      originalInternalRowEnd P i ≤ originalInternalRowLast P i ∧
        originalInternalRowLast P i < n := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  have hab : (E a).val.val.val < (E b).val.val.val :=
    E.strictMono (by change i.val < i.val+1; omega)
  have hb := Fin.le_def.mp (interiorBlockFirst_le_last P (E b).val.val)
  rw [(E b).val.property] at hb
  exact ⟨hab, hb, (interiorBlockLast P (E b).val.val).isLt⟩

/-- Every retained interval row lies in the complete actual source-row frame. -/
theorem originalInternal_interval_row_bounds {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (r : OriginalInternalInterval P i) :
    originalInternalRowStart P i ≤ (originalRemovedRow P r.val.val.1 r.val.val.2).val ∧
      (originalRemovedRow P r.val.val.1 r.val.val.2).val ≤ originalInternalRowLast P i := by
  exact (original_interval_row_rank_iff P _ _ r.val.val).mp ⟨r.property, r.val.property⟩

/-- Local physical row positions after deleting exactly the two selected pivots. -/
abbrev OriginalInternalRowOrdinal {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :=
  {k : Fin (originalInternalRowLast P i + 1 - originalInternalRowStart P i) //
    k.val ≠ 0 ∧ k.val ≠ originalInternalRowEnd P i - originalInternalRowStart P i}

/-- The actual removed-row position in the full two-pivot local row frame. -/
noncomputable def originalInternalRowOrdinal {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (r : OriginalInternalInterval P i) : OriginalInternalRowOrdinal P i := by
  have hb := originalInternal_interval_row_bounds P i r
  have hf := originalInternal_row_frame_bounds P i
  have ha : (originalRemovedRow P r.val.val.1 r.val.val.2).val ≠ originalInternalRowStart P i := by
    intro h
    apply originalRemovedRow_ne_selected P r.val.val
      (originalSelectedEnumeration P ⟨i.val, by have := i.isLt; omega⟩)
    exact Fin.ext h
  have he : (originalRemovedRow P r.val.val.1 r.val.val.2).val ≠ originalInternalRowEnd P i := by
    intro h
    apply originalRemovedRow_ne_selected P r.val.val
      (originalSelectedEnumeration P ⟨i.val+1, by have := i.isLt; omega⟩)
    exact Fin.ext h
  refine ⟨⟨(originalRemovedRow P r.val.val.1 r.val.val.2).val - originalInternalRowStart P i,
    by omega⟩, ?_⟩
  change (originalRemovedRow P r.val.val.1 r.val.val.2).val - originalInternalRowStart P i ≠ 0 ∧
    (originalRemovedRow P r.val.val.1 r.val.val.2).val - originalInternalRowStart P i ≠
      originalInternalRowEnd P i - originalInternalRowStart P i
  constructor <;> omega

/-- Distinct retained interval points have distinct physical row ordinals. -/
theorem originalInternalRowOrdinal_injective {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    Function.Injective (originalInternalRowOrdinal (hD := hD) P i) := by
  intro r s he
  have hv := congrArg (fun k => k.val.val) he
  change (originalRemovedRow P r.val.val.1 r.val.val.2).val - originalInternalRowStart P i =
    (originalRemovedRow P s.val.val.1 s.val.val.2).val - originalInternalRowStart P i at hv
  have hr := originalInternal_interval_row_bounds P i r
  have hs := originalInternal_interval_row_bounds P i s
  have heRow : originalRemovedRow P r.val.val.1 r.val.val.2 =
      originalRemovedRow P s.val.val.1 s.val.val.2 := Fin.ext (by omega)
  apply Subtype.ext
  apply Subtype.ext
  exact originalRemovedRow_injective P heRow

/-- Every local nonpivot row is supplied by the original retained interval. -/
theorem originalInternalRowOrdinal_surjective {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    Function.Surjective (originalInternalRowOrdinal (hD := hD) P i) := by
  intro k
  have hf := originalInternal_row_frame_bounds P i
  have hk := k.val.isLt
  have hk0 := k.property.1
  have hkgap := k.property.2
  let t : Fin n := ⟨originalInternalRowStart P i + k.val.val, by omega⟩
  have hc := (original_consecutive_row_coverage (hD := hD) P
    ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val+1, by have := i.isLt; omega⟩ rfl t).mp
      (show originalInternalRowStart P i ≤ t.val ∧ t.val ≤ originalInternalRowLast P i by
        dsimp only [t]; omega)
  rcases hc with ha | hb | ⟨r, hr⟩
  · have hv := congrArg Fin.val ha
    change originalInternalRowStart P i + k.val.val = originalInternalRowStart P i at hv
    omega
  · have hv := congrArg Fin.val hb
    change originalInternalRowStart P i + k.val.val = originalInternalRowEnd P i at hv
    omega
  · refine ⟨r, Subtype.ext (Fin.ext ?_)⟩
    change (originalRemovedRow P r.val.val.1 r.val.val.2).val -
      originalInternalRowStart P i = k.val.val
    rw [hr]
    dsimp only [t]
    omega

/-- The complete original retained interval has precisely the two-pivot physical row frame. -/
noncomputable def originalInternalRowOrdinalEquiv {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    OriginalInternalInterval P i ≃ OriginalInternalRowOrdinal P i :=
  Equiv.ofBijective (originalInternalRowOrdinal P i)
    ⟨originalInternalRowOrdinal_injective P i, originalInternalRowOrdinal_surjective P i⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
