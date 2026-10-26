/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalConsecutiveIntervalCard

/-!
# Complete actual source-row coverage between consecutive selected cores

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The retained interval contains every complementary row between its actual
selected endpoint components except exactly the two retained selected pivots.
The original global source partition supplies every row, including unit
vertices and both selected proper strips. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
attribute [local instance] Classical.propDecidable
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Actual block-cut membership is exactly the full physical source-row interval. -/
theorem original_interval_row_rank_iff {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (r : OriginalRemainingIndices (hD := hD) P) :
    (originalResponseLowerCut P (some a) < (interiorBlock P r.1.val : ℤ) ∧
      (interiorBlock P r.1.val : ℤ) < originalResponseUpperCut P (some b)) ↔
      a.val.val ≤ originalRemovedRow P r.1 r.2 ∧
        originalRemovedRow P r.1 r.2 ≤ interiorBlockLast P b.val.val := by
  have ha := interiorBlock_label_le_iff_first_le P a.val.val (originalRemovedRow P r.1 r.2)
  have hb := interiorBlock_label_le_iff_le_last P b.val.val (originalRemovedRow P r.1 r.2)
  rw [originalRemovedRow_block, a.val.property] at ha
  rw [originalRemovedRow_block] at hb
  change ((interiorBlock P a.val.val : ℤ) - 1 < (interiorBlock P r.1.val : ℤ) ∧
    (interiorBlock P r.1.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1) ↔ _
  omega

/-- A selected occurrence between consecutive selected endpoints is one endpoint. -/
theorem original_consecutive_selected_between {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) (hij : j.val = i.val + 1)
    (s : OriginalSelectedBlocks (hD := hD) P)
    (hs : interiorBlock P (originalSelectedEnumeration P i).val.val ≤ interiorBlock P s.val.val ∧
      interiorBlock P s.val.val ≤ interiorBlock P (originalSelectedEnumeration P j).val.val) :
    s = originalSelectedEnumeration P i ∨ s = originalSelectedEnumeration P j := by
  classical
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P j
  let S := Finset.univ.filter fun t : OriginalSelectedBlocks (hD := hD) P =>
    interiorBlock P a.val.val ≤ interiorBlock P t.val.val ∧
      interiorBlock P t.val.val ≤ interiorBlock P b.val.val
  have hab : i < j := by omega
  have hl := (originalSelectedEnumeration_label_strictMono P hab).le
  have hne : a ≠ b := fun he => (ne_of_lt hab) ((originalSelectedEnumeration P).injective he)
  have hsub : ({a,b} : Finset _) ⊆ S := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_rfl, hl⟩
    · have he := Finset.mem_singleton.mp ht
      subst t
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hl, le_rfl⟩
  have hcard : S.card = 2 := by
    simpa only [Fintype.card_subtype] using original_consecutive_selected_card P i j hij
  have heq : ({a,b} : Finset _) = S := Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_pair hne]; exact hcard.le)
  have hm : s ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
  rw [← heq] at hm
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

/-- Every actual source row in a consecutive component interval is a pivot or is retained. -/
theorem original_consecutive_row_coverage {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) (hij : j.val = i.val + 1)
    (t : Fin n) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P j
    (a.val.val ≤ t ∧ t ≤ interiorBlockLast P b.val.val) ↔
      t = a.val.val ∨ t = b.val.val ∨
        ∃ r : OriginalResponseInterval P (some a) (some b),
          originalRemovedRow P r.val.val.1 r.val.val.2 = t := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P j
  have hab : a.val.val < b.val.val := (originalSelectedEnumeration (hD := hD) P).strictMono
    (show i < j by omega)
  have hb := interiorBlockFirst_le_last P b.val.val
  rw [b.val.property] at hb
  constructor
  · intro ht
    obtain ⟨x, hx⟩ := (complementaryRowEquiv (hD := hD) P).surjective t
    rcases x with s | r
    · have hst : s.val.val = t := by
        change originalBlockIndex P ⟨s.val, 0⟩ = t at hx
        apply Fin.ext
        have hv := congrArg Fin.val hx
        simpa only [originalBlockIndex, interiorSliceIndex, Fin.val_zero, add_zero,
          s.val.property] using hv
      have hs : interiorBlock P a.val.val ≤ interiorBlock P s.val.val ∧
          interiorBlock P s.val.val ≤ interiorBlock P b.val.val := by
        rw [interiorBlock_label_le_iff_first_le, interiorBlock_label_le_iff_le_last,
          a.val.property, hst]
        exact ht
      rcases original_consecutive_selected_between P i j hij s hs with he | he
      · exact Or.inl (hst.symm.trans (congrArg (fun s => s.val.val) he))
      · exact Or.inr (Or.inl (hst.symm.trans (congrArg (fun s => s.val.val) he)))
    · change originalRemovedRow P r.1 r.2 = t at hx
      have hr := (original_interval_row_rank_iff P a b r).mpr (by simpa only [hx] using ht)
      exact Or.inr (Or.inr ⟨⟨⟨r, hr.2⟩, hr.1⟩, hx⟩)
  · rintro (rfl | rfl | ⟨r, rfl⟩)
    · exact ⟨le_rfl, hab.le.trans hb⟩
    · exact ⟨hab.le, hb⟩
    · exact (original_interval_row_rank_iff P a b r.val.val).mp ⟨r.property, r.val.property⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
