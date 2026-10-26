/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalIntervalRowCoverage

/-!
# Complete actual source-column coverage between selected cores

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The original complementary column bijection covers the entire physical
source interval after restoring the two actual last-column selected pivots.
Both full endpoint components and every intervening unit vertex remain.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
attribute [local instance] Classical.propDecidable
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Actual block-cut membership is exactly the full physical source-column interval. -/
theorem original_interval_col_rank_iff {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (r : OriginalRemainingIndices (hD := hD) P) :
    (originalResponseLowerCut P (some a) < (interiorBlock P r.1.val : ℤ) ∧
      (interiorBlock P r.1.val : ℤ) < originalResponseUpperCut P (some b)) ↔
      a.val.val ≤ originalRemovedCol P r.1 r.2 ∧
        originalRemovedCol P r.1 r.2 ≤ interiorBlockLast P b.val.val := by
  have ha := interiorBlock_label_le_iff_first_le P a.val.val (originalRemovedCol P r.1 r.2)
  have hb := interiorBlock_label_le_iff_le_last P b.val.val (originalRemovedCol P r.1 r.2)
  rw [originalRemovedCol_block, a.val.property] at ha
  rw [originalRemovedCol_block] at hb
  change ((interiorBlock P a.val.val : ℤ) - 1 < (interiorBlock P r.1.val : ℤ) ∧
    (interiorBlock P r.1.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1) ↔ _
  omega

set_option maxHeartbeats 800000 in
-- The canonical column partition retains the nested dependent block fibers.
/-- Every original column between consecutive selected cores is a pivot or is retained. -/
theorem original_consecutive_col_coverage {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) (hij : j.val = i.val + 1)
    (t : Fin n) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P j
    (a.val.val ≤ t ∧ t ≤ interiorBlockLast P b.val.val) ↔
      t = interiorBlockLast P a.val.val ∨ t = interiorBlockLast P b.val.val ∨
        ∃ r : OriginalResponseInterval P (some a) (some b),
          originalRemovedCol P r.val.val.1 r.val.val.2 = t := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P j
  have ha := interiorBlockFirst_le_last P a.val.val
  rw [a.val.property] at ha
  have hb := interiorBlockFirst_le_last P b.val.val
  rw [b.val.property] at hb
  have hlabels := originalSelectedEnumeration_label_strictMono (hD := hD) P (show i < j by omega)
  have hab : interiorBlockLast P a.val.val < b.val.val := by
    apply interiorBlock_index_lt P
    rw [interiorBlockLast_label]
    exact hlabels
  constructor
  · intro ht
    obtain ⟨x, hx⟩ := (complementaryColEquiv (hD := hD) P).surjective t
    rcases x with s | r
    · change originalBlockIndex P ⟨s.val, Fin.last _⟩ = t at hx
      have hlast : originalBlockIndex P ⟨s.val, Fin.last _⟩ = interiorBlockLast P s.val.val := by
        apply Fin.ext
        simp only [originalBlockIndex, interiorSliceIndex, Fin.val_last]
        have hf := Fin.le_def.mp (interiorBlockFirst_le_last P s.val.val)
        unfold interiorBlockLength
        omega
      rw [hlast] at hx
      have hlow : interiorBlockFirst P a.val.val ≤ interiorBlockLast P s.val.val := by
        rw [a.val.property, hx]
        exact ht.1
      have hu : interiorBlockLast P s.val.val ≤ interiorBlockLast P b.val.val := by
        rw [hx]
        exact ht.2
      have hs := And.intro
        ((interiorBlock_label_le_iff_first_le P a.val.val _).mpr hlow)
        ((interiorBlock_label_le_iff_le_last P b.val.val _).mpr hu)
      rw [interiorBlockLast_label] at hs
      rcases original_consecutive_selected_between P i j hij s hs with he | he
      · have heLast := congrArg
          (fun s : OriginalSelectedBlocks (hD := hD) P => interiorBlockLast P s.val.val) he
        exact Or.inl (hx.symm.trans heLast)
      · have heLast := congrArg
          (fun s : OriginalSelectedBlocks (hD := hD) P => interiorBlockLast P s.val.val) he
        exact Or.inr (Or.inl (hx.symm.trans heLast))
    · change originalRemovedCol P r.1 r.2 = t at hx
      have hr := (original_interval_col_rank_iff P a b r).mpr (by simpa only [hx] using ht)
      exact Or.inr (Or.inr ⟨⟨⟨r, hr.2⟩, hr.1⟩, hx⟩)
  · rintro (rfl | rfl | ⟨r, rfl⟩)
    · exact ⟨ha, hab.le.trans hb⟩
    · exact ⟨ha.trans (hab.le.trans hb), le_rfl⟩
    · exact (original_interval_col_rank_iff P a b r.val.val).mp ⟨r.property, r.val.property⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
