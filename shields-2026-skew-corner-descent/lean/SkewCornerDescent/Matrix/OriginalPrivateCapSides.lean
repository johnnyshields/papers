/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivateWindowMembership
import SkewCornerDescent.Matrix.OriginalWindowCapIntervals

/-!
# Exact clipped-cap presentations of both private interval sides

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Strict original endpoint bounds identify each private half interval with its
complete whole-window cap. Normalized outer boundary facts are produced from
the profile. The underlying remaining occurrences are unchanged. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

private theorem remaining_col_positive {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) : 0 < originalResponseCols P j := by
  have h := P.zeta_strictAnti (Fin.castSucc_lt_last (originalRemovedCol (hD := hD) P j.1 j.2))
  rw [P.zeta_last] at h
  exact h

private theorem remaining_row_below_top {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) : originalResponseRows P j < P.xi 0 := by
  exact P.xi_strictAnti (show (0 : Fin (n + 1)) <
    (originalRemovedRow (hD := hD) P j.1 j.2).succ by
      change 0 < (originalRemovedRow (hD := hD) P j.1 j.2).val + 1
      omega)

private theorem lower_private_window_iff {n : ℕ} (P : Profile n) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (j : OriginalRemainingIndices (hD := hD) P) :
    originalBlockInWindow P 0 k j.1 ↔ originalResponseRows P j < k := by
  have hnorm := profile_normalized_lower_private_boundaries P
  rw [originalRemaining_private_window_iff_bounds P 0 k hnorm.1
    (by simpa only [zero_sub] using hnorm.2) hk hp j]
  exact ⟨fun h => h.2, fun h => ⟨remaining_col_positive P j, h⟩⟩

private theorem upper_private_window_iff {n : ℕ} (P : Profile n) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (j : OriginalRemainingIndices (hD := hD) P) :
    originalBlockInWindow P k (P.xi 0) j.1 ↔ k < originalResponseCols P j := by
  have hnorm := profile_normalized_upper_private_boundaries P
  rw [originalRemaining_private_window_iff_bounds P k (P.xi 0) hk hp hnorm.1 hnorm.2 j]
  exact ⟨fun h => h.1, fun h => ⟨h, remaining_row_below_top P j⟩⟩

private theorem lower_cap_side_of_upper_cut {n : ℕ} (P : Profile n)
    (d : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hu : (interiorBlock P j.1.val : ℤ) < originalResponseUpperCut P (some d)) :
    originalCapBlockSide true d j.1 := by
  apply (originalCapInterval_block_bounds P true d j.1).mp
  exact ⟨by change (-1 : ℤ) < _; omega, hu⟩

private theorem upper_cap_side_of_lower_cut {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hl : originalResponseLowerCut P (some b) < (interiorBlock P j.1.val : ℤ)) :
    originalCapBlockSide false b j.1 := by
  have hle : (interiorBlock P b.val.val : ℤ) ≤ (interiorBlock P j.1.val : ℤ) := by
    change (interiorBlock P b.val.val : ℤ) - 1 < _ at hl
    omega
  have hn : interiorBlock P b.val.val ≤ interiorBlock P j.1.val := by exact_mod_cast hle
  change b.val ≤ j.1
  exact (originalBlocks_label_strictMono P).le_iff_le.mp hn

/-- The below-cut part of a complete retained interval is exactly its clipped
upper cap, with every remaining original row and column carried unchanged. -/
noncomputable def originalLowerPrivateCapEquiv {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hb : k < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))) :
    {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
      originalResponseRows P i.1.1 < k} ≃
      {i : OriginalWholeWindowRemaining (hD := hD) P 0 k //
        originalCapBlockSide true d i.1.val} where
  toFun i := by
    let j := i.val.1.1
    have hwin := (lower_private_window_iff P k hk hp j).mpr i.property
    have hside := lower_cap_side_of_upper_cut P d j i.val.1.property
    exact ⟨⟨⟨j.1, hwin⟩, j.2⟩, hside⟩
  invFun i := by
    let j : OriginalRemainingIndices (hD := hD) P := ⟨i.val.1.val, i.val.2⟩
    have hrow := (lower_private_window_iff P k hk hp j).mp i.val.1.property
    have hu := ((originalCapInterval_block_bounds P true d j.1).mpr i.property).2
    have hl := ((originalRemaining_interval_iff_endpoints P b d j).mpr
      ⟨hrow.trans hb, originalResponse_col_gt P (some d) j hu⟩).1
    exact ⟨⟨⟨j, hu⟩, hl⟩, hrow⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

/-- The above-cut part is exactly its clipped lower cap. The source supplies
normalized upper boundary exclusions instead of carrying them as hypotheses. -/
noncomputable def originalUpperPrivateCapEquiv {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) < k) :
    {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
      k < originalResponseCols P i.1.1} ≃
      {i : OriginalWholeWindowRemaining (hD := hD) P k (P.xi 0) //
        originalCapBlockSide false b i.1.val} where
  toFun i := by
    let j := i.val.1.1
    have hwin := (upper_private_window_iff P k hk hp j).mpr i.property
    have hside := upper_cap_side_of_lower_cut P b j i.val.property
    exact ⟨⟨⟨j.1, hwin⟩, j.2⟩, hside⟩
  invFun i := by
    let j : OriginalRemainingIndices (hD := hD) P := ⟨i.val.1.val, i.val.2⟩
    have hcol := (upper_private_window_iff P k hk hp j).mp i.val.1.property
    have hl := ((originalCapInterval_block_bounds P false b j.1).mpr i.property).1
    have hu := ((originalRemaining_interval_iff_endpoints P b d j).mpr
      ⟨originalResponse_row_lt P (some b) j hl, hd.trans hcol⟩).2
    exact ⟨⟨⟨j, hu⟩, hl⟩, hcol⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

/-- The complete original occurrence survives the lower-side presentation. -/
theorem originalLowerPrivateCapEquiv_remaining {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hb : k < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))
    (i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
      originalResponseRows P i.1.1 < k}) :
    let q := originalLowerPrivateCapEquiv P b d k hk hp hb i
    (⟨q.val.1.val, q.val.2⟩ : OriginalRemainingIndices (hD := hD) P) = i.val.1.1 := rfl

/-- The complete original occurrence survives the upper-side presentation. -/
theorem originalUpperPrivateCapEquiv_remaining {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) < k)
    (i : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
      k < originalResponseCols P i.1.1}) :
    let q := originalUpperPrivateCapEquiv P b d k hk hp hd i
    (⟨q.val.1.val, q.val.2⟩ : OriginalRemainingIndices (hD := hD) P) = i.val.1.1 := rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
