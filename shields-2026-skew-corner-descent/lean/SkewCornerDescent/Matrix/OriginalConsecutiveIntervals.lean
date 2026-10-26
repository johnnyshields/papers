/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIntervalProtectedTops

/-!
# Complete block inventory between consecutive original selected occurrences

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Every retained original block is one endpoint's proper selected strip or a
complete nonselected block. Actual source enumeration supplies the exclusion
of any further selected component, including repeated equal functions.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Consecutive actual selected ranks contain no other selected original block. -/
theorem original_consecutive_selected_block_cases {n : ℕ} (P : Profile n)
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + 1)
    (u : OriginalBlocks P)
    (hu : (originalSelectedEnumeration P i).val ≤ u ∧
      u ≤ (originalSelectedEnumeration P t).val) :
    u = (originalSelectedEnumeration P i).val ∨
      u = (originalSelectedEnumeration P t).val ∨
      ¬ originalBlockSelected (hD := hD) P u := by
  classical
  by_cases hs : originalBlockSelected (hD := hD) P u
  · let a : OriginalSelectedBlocks (hD := hD) P := ⟨u, hs⟩
    let k := (originalSelectedEnumeration P).symm a
    have hleft : i ≤ k := by
      apply (originalSelectedEnumeration P).le_iff_le.mp
      rw [OrderIso.apply_symm_apply]
      exact hu.1
    have hright : k ≤ t := by
      apply (originalSelectedEnumeration P).le_iff_le.mp
      rw [OrderIso.apply_symm_apply]
      exact hu.2
    have hcases : k = i ∨ k = t := by
      have hl : i.val ≤ k.val := hleft
      have hr : k.val ≤ t.val := hright
      rcases (show k.val = i.val ∨ k.val = t.val by omega) with he | he
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (Fin.ext he)
    have hk : (originalSelectedEnumeration P k).val = u := by
      rw [OrderIso.apply_symm_apply]
    rcases hcases with he | he
    · exact Or.inl (he ▸ hk.symm)
    · exact Or.inr (Or.inl (he ▸ hk.symm))
  · exact Or.inr (Or.inr hs)

/-- Every retained index of an actual consecutive response belongs to an endpoint
proper strip or a full nonselected component; no selected inventory is assumed. -/
theorem original_consecutive_interval_block_cases {n : ℕ} (P : Profile n)
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + 1)
    (j : OriginalResponseInterval (hD := hD) P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t))) :
    j.1.1.1 = (originalSelectedEnumeration P i).val ∨
      j.1.1.1 = (originalSelectedEnumeration P t).val ∨
      ¬ originalBlockSelected (hD := hD) P j.1.1.1 := by
  apply original_consecutive_selected_block_cases P i t ht
  exact (originalResponseInterval_block_bounds P _ _ _).mp ⟨j.2, j.1.2⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
