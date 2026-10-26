/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivateUnitVertex
import SkewCornerDescent.Matrix.OriginalHessianProjection
import SkewCornerDescent.Matrix.OriginalEndpointInjection

/-!
# Actual remaining endpoints on the two sides of a private cut

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The original row and column maps stay in their common produced block. Two
singleton diagonals therefore separate every complete remaining position;
only the literal zero-index unit pair can lie at the cut. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The actual retained endpoints, including selected proper strips and full
nonrow unit blocks, have the produced strict side or literal-unit alternative. -/
theorem originalRemaining_private_cut_trichotomy {n : ℕ} (P : Profile n) (k : ℤ)
    (hcur : diagLo P.cells k = diagHi P.cells k)
    (hprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (j : OriginalRemainingIndices (hD := hD) P) :
    (originalResponseRows P j < k ∧ originalResponseCols P j < k) ∨
      (k < originalResponseRows P j ∧ k < originalResponseCols P j) ∨
      (originalResponseRows P j = k ∧ originalResponseCols P j = k) := by
  apply profile_private_same_block_endpoints_trichotomy P k hcur hprev
    (originalRemovedCol (hD := hD) P j.1 j.2)
    (originalRemovedRow (hD := hD) P j.1 j.2)
  rw [originalRemovedRow_block, originalRemovedCol_block]

/-- Removing the actual cut unit supplies strict no-feedback geometry for every
remaining original position. No separation hypothesis is added to the source. -/
theorem originalRemaining_private_cut_without_unit {n : ℕ} (P : Profile n) (k : ℤ)
    (hcur : diagLo P.cells k = diagHi P.cells k)
    (hprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (j : {j : OriginalRemainingIndices (hD := hD) P //
      ¬ (originalResponseRows P j = k ∧ originalResponseCols P j = k)}) :
    (originalResponseRows P j.val < k ∧ originalResponseCols P j.val < k) ∨
      (k < originalResponseRows P j.val ∧ k < originalResponseCols P j.val) := by
  rcases originalRemaining_private_cut_trichotomy P k hcur hprev j.val with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (j.property h)

/-- Every actual retained interval inherits the same private-cut classification. -/
theorem originalInterval_private_cut_trichotomy {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℤ)
    (hcur : diagLo P.cells k = diagHi P.cells k)
    (hprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (j : OriginalResponseInterval (hD := hD) P b d) :
    (originalResponseRows P j.1.1 < k ∧ originalResponseCols P j.1.1 < k) ∨
      (k < originalResponseRows P j.1.1 ∧ k < originalResponseCols P j.1.1) ∨
      (originalResponseRows P j.1.1 = k ∧ originalResponseCols P j.1.1 = k) :=
  originalRemaining_private_cut_trichotomy P k hcur hprev j.1.1

/-- A literal original zero-index pivot cannot be selected for removal and
survives as one genuine remaining row/column pair at its original coordinate. -/
theorem originalRemaining_of_beta_unit {n : ℕ} (P : Profile n) (i : Fin n)
    (hunit : P.xi i.succ = P.zeta i.castSucc) :
    ∃ j : OriginalRemainingIndices (hD := hD) P,
      originalResponseRows P j = P.xi i.succ ∧
        originalResponseCols P j = P.zeta i.castSucc := by
  classical
  have hfirst : interiorBlockFirst P i = i :=
    interior_empty_row_isolated P i hunit _ ((mem_interiorBlockFiber P i _).mp
      (interiorBlockFirst_mem P i))
  have hlast : interiorBlockLast P i = i :=
    interior_empty_row_isolated P i hunit _ ((mem_interiorBlockFiber P i _).mp
      (interiorBlockLast_mem P i))
  have hlength : interiorBlockLength P i = 0 := by
    simp only [interiorBlockLength, hfirst, hlast, Nat.sub_self]
  let b : OriginalBlocks P := ⟨i, hfirst⟩
  have hnonselected : ¬ originalBlockSelected (hD := hD) P b := by
    intro h
    have hpos := originalBlockSelected_nonempty P b h
    change P.zeta i.castSucc < P.xi i.succ at hpos
    omega
  let j : Fin (originalRemovedSize (hD := hD) P b) := ⟨0, by
    simp only [originalRemovedSize, ite_eq_right hnonselected]
    change 0 < interiorBlockLength P i + 1
    rw [hlength]
    decide⟩
  have hr : originalRemovedRow (hD := hD) P b j = i := by
    apply Fin.ext
    simp only [originalRemovedRow, originalRemovedRowPosition, dite_eq_right hnonselected]
    change (interiorBlockFirst P i).val + 0 = i.val
    rw [hfirst, Nat.add_zero]
  have hc : originalRemovedCol (hD := hD) P b j = i := by
    apply Fin.ext
    change (interiorBlockFirst P i).val + 0 = i.val
    rw [hfirst, Nat.add_zero]
  refine ⟨⟨b, j⟩, ?_, ?_⟩
  · change P.xi (originalRemovedRow (hD := hD) P b j).succ = _
    rw [hr]
  · change P.zeta (originalRemovedCol (hD := hD) P b j).castSucc = _
    rw [hc]

/-- The actual surviving unit at a private cut is exactly the original beta
unit; selecting all occurrences does not create or remove that vertex. -/
theorem originalRemaining_private_unit_iff_beta {n : ℕ} (P : Profile n) (k : ℤ)
    (hcur : diagLo P.cells k = diagHi P.cells k)
    (hprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1)) :
    (∃ j : OriginalRemainingIndices (hD := hD) P,
      originalResponseRows P j = k ∧ originalResponseCols P j = k) ↔
      ∃ i : Fin n, P.xi i.succ = k ∧ P.zeta i.castSucc = k := by
  constructor
  · rintro ⟨j, _, hc⟩
    let i := originalRemovedCol (hD := hD) P j.1 j.2
    have hc' : P.zeta i.castSucc = k := hc
    have ht := profile_private_beta_pair_trichotomy P k hcur hprev i
    refine ⟨i, ?_, hc'⟩
    omega
  · rintro ⟨i, hr, hc⟩
    obtain ⟨j, hjr, hjc⟩ := originalRemaining_of_beta_unit (hD := hD) P i (hr.trans hc.symm)
    exact ⟨j, hjr.trans hr, hjc.trans hc⟩

/-- The full original remaining matrix contains a unit at a private edge
exactly in its vertical case. Both existence and survival are produced. -/
theorem originalRemaining_private_unit_iff_vertical {n : ℕ} (P : Profile n) (k : ℤ)
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = k) (hp : content prev = k - 1)
    (hsingle : diagLo P.cells k = diagHi P.cells k)
    (hprevsingle : diagLo P.cells (k - 1) = diagHi P.cells (k - 1)) :
    (∃ j : OriginalRemainingIndices (hD := hD) P,
      originalResponseRows P j = k ∧ originalResponseCols P j = k) ↔ cur.2 = prev.2 := by
  rw [originalRemaining_private_unit_iff_beta P k hsingle hprevsingle]
  exact profile_private_unit_vertex_iff_vertical P k cur prev hcur hprev hc hp hsingle hprevsingle

/-- Actual column injection makes the surviving private unit unique, including
all repeated selected components and all complete nonrow unit blocks. -/
theorem originalRemaining_private_unit_unique {n : ℕ} (P : Profile n) (k : ℤ)
    (i j : OriginalRemainingIndices (hD := hD) P)
    (hi : originalResponseRows P i = k ∧ originalResponseCols P i = k)
    (hj : originalResponseRows P j = k ∧ originalResponseCols P j = k) : i = j :=
  originalResponseCols_injective P (hi.2.trans hj.2.symm)

/-- The whole block fiber of an actual private unit is its single retained
position. Thus deleting that unit is a complete-block deletion. -/
theorem originalRemaining_private_unit_block_singleton {n : ℕ} (P : Profile n) (k : ℤ)
    (hcur : diagLo P.cells k = diagHi P.cells k)
    (hprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (j : OriginalRemainingIndices (hD := hD) P)
    (hunit : originalResponseRows P j = k ∧ originalResponseCols P j = k)
    (i : OriginalRemainingIndices (hD := hD) P)
    (hlabel : interiorBlock P i.1.val = interiorBlock P j.1.val) : i = j := by
  let q := originalRemovedCol (hD := hD) P j.1 j.2
  have hc : P.zeta q.castSucc = k := hunit.2
  have ht := profile_private_beta_pair_trichotomy P k hcur hprev q
  have hr : P.xi q.succ = k := by omega
  have hraw : P.xi q.succ = P.zeta q.castSucc := hr.trans hc.symm
  have hi := interior_empty_row_isolated P q hraw
    (originalRemovedCol (hD := hD) P i.1 i.2) (by
      rw [originalRemovedCol_block, originalRemovedCol_block]
      exact hlabel)
  apply originalResponseCols_injective P
  change P.zeta (originalRemovedCol (hD := hD) P i.1 i.2).castSucc = P.zeta q.castSucc
  rw [hi]

/-- The genuine block interval is exactly the strict actual endpoint interval.
The reverse implication is produced from the source's beta ordering. -/
theorem originalRemaining_interval_iff_endpoints {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (j : OriginalRemainingIndices (hD := hD) P) :
    (originalResponseLowerCut P (some b) < (interiorBlock P j.1.val : ℤ) ∧
      (interiorBlock P j.1.val : ℤ) < originalResponseUpperCut P (some d)) ↔
    (originalResponseRows P j <
        P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) ∧
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) <
        originalResponseCols P j) := by
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨originalResponse_row_lt P (some b) j hl, originalResponse_col_gt P (some d) j hu⟩
  · rintro ⟨hr, hc⟩
    change P.xi (originalRemovedRow (hD := hD) P j.1 j.2).succ <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) at hr
    rw [originalRowSplitEquiv_selected] at hr
    have hridx := (show StrictAnti P.xi from P.xi_strictAnti).lt_iff_gt.mp hr
    have hrnat := Fin.lt_def.mp hridx
    simp only [Fin.val_succ] at hrnat
    have hl := interiorBlock_mono P (show b.val.val ≤
        originalRemovedRow (hD := hD) P j.1 j.2 by
      apply Fin.le_def.mpr
      omega)
    rw [originalRemovedRow_block] at hl
    change P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) <
      P.zeta (originalRemovedCol (hD := hD) P j.1 j.2).castSucc at hc
    rw [originalColSplitEquiv_selected] at hc
    have hcidx := (show StrictAnti P.zeta from P.zeta_strictAnti).lt_iff_gt.mp hc
    have hcnat := Fin.lt_def.mp hcidx
    simp only [Fin.val_castSucc] at hcnat
    have hu := interiorBlock_mono P (show originalRemovedCol (hD := hD) P j.1 j.2 ≤
        interiorBlockLast P d.val.val by
      apply Fin.le_def.mpr
      omega)
    rw [originalRemovedCol_block, interiorBlockLast_label] at hu
    have hl' : (interiorBlock P b.val.val : ℤ) ≤ (interiorBlock P j.1.val : ℤ) := by
      exact_mod_cast hl
    have hu' : (interiorBlock P j.1.val : ℤ) ≤ (interiorBlock P d.val.val : ℤ) := by
      exact_mod_cast hu
    change (interiorBlock P b.val.val : ℤ) - 1 < (interiorBlock P j.1.val : ℤ) ∧
      (interiorBlock P j.1.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1
    omega

/-- A surviving actual unit strictly between the retained endpoints belongs to
the complete original interval; no block-membership premise is assumed. -/
theorem originalInterval_of_remaining_unit {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (j : OriginalRemainingIndices (hD := hD) P)
    (hunit : originalResponseRows P j = k ∧ originalResponseCols P j = k)
    (hx : k < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))
    (hy : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) < k) :
    ∃ i : OriginalResponseInterval (hD := hD) P (some b) (some d),
      i.1.1 = j ∧ originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k := by
  have hb := (originalRemaining_interval_iff_endpoints P b d j).mpr
    ⟨hunit.1 ▸ hx, hunit.2 ▸ hy⟩
  exact ⟨⟨⟨j, hb.2⟩, hb.1⟩, rfl, hunit⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
