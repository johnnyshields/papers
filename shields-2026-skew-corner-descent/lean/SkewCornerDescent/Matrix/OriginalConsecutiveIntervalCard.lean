/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalIntervalCardinality

/-!
# Actual consecutive interval row counts

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Consecutive selected occurrences contribute exactly two omitted pivots.
Every other source row is counted by the complete retained interval.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
attribute [local instance] Classical.propDecidable
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Exactly the two adjacent selected occurrences lie between their labels. -/
theorem original_consecutive_selected_card {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) (hij : j.val = i.val + 1) :
    Fintype.card {s : OriginalSelectedBlocks (hD := hD) P //
      interiorBlock P (originalSelectedEnumeration P i).val.val ≤ interiorBlock P s.val.val ∧
      interiorBlock P s.val.val ≤
        interiorBlock P (originalSelectedEnumeration P j).val.val} = 2 := by
  classical
  let E := originalSelectedEnumeration (hD := hD) P
  have hne : E i ≠ E j := by
    intro he
    have he' := E.injective he
    have hv := congrArg Fin.val he'
    omega
  have hbetween (s : OriginalSelectedBlocks (hD := hD) P) :
      (interiorBlock P (E i).val.val ≤ interiorBlock P s.val.val ∧
        interiorBlock P s.val.val ≤ interiorBlock P (E j).val.val) ↔ s = E i ∨ s = E j := by
    have hs : E (E.symm s) = s := E.apply_symm_apply s
    have hm : StrictMono (fun k => interiorBlock P (E k).val.val) :=
      originalSelectedEnumeration_label_strictMono (hD := hD) P
    constructor
    · intro h
      have hlo : i ≤ E.symm s := hm.le_iff_le.mp (by simpa only [hs] using h.1)
      have hhi : E.symm s ≤ j := hm.le_iff_le.mp (by simpa only [hs] using h.2)
      have he : E.symm s = i ∨ E.symm s = j := by
        have hi := i.isLt
        have hj := j.isLt
        have hs' := (E.symm s).isLt
        rcases (show (E.symm s).val = i.val ∨ (E.symm s).val = j.val by omega) with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases he with he | he
      · exact Or.inl (by rw [← hs, he])
      · exact Or.inr (by rw [← hs, he])
    · rintro (rfl | rfl)
      · exact ⟨le_rfl, (hm (show i < j by omega)).le⟩
      · exact ⟨(hm (show i < j by omega)).le, le_rfl⟩
  rw [Fintype.card_subtype]
  have heq : (Finset.univ.filter fun s : OriginalSelectedBlocks (hD := hD) P =>
      interiorBlock P (E i).val.val ≤ interiorBlock P s.val.val ∧
        interiorBlock P s.val.val ≤ interiorBlock P (E j).val.val) = {E i, E j} := by
    ext s
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] using hbetween s
  change (Finset.univ.filter fun s : OriginalSelectedBlocks (hD := hD) P =>
      interiorBlock P (E i).val.val ≤ interiorBlock P s.val.val ∧
        interiorBlock P s.val.val ≤ interiorBlock P (E j).val.val).card = 2
  rw [heq, Finset.card_pair hne]

/-- The complete internal interval plus its two pivots counts every source row. -/
theorem original_internal_interval_card {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    let a := originalSelectedEnumeration (hD := hD) P ⟨i.val, by have := i.isLt; omega⟩
    let b := originalSelectedEnumeration (hD := hD) P ⟨i.val+1, by have := i.isLt; omega⟩
    Fintype.card (OriginalInternalInterval P i) + 2 =
      (interiorBlockLast P b.val.val).val + 1 - a.val.val.val := by
  dsimp only
  have h := original_interval_card_balance (hD := hD) P
    (originalSelectedEnumeration P ⟨i.val, by have := i.isLt; omega⟩)
    (originalSelectedEnumeration P ⟨i.val+1, by have := i.isLt; omega⟩)
  rw [original_consecutive_selected_card P _ _ rfl] at h
  exact h

end SkewCornerDescent.Matrix.SelectedCoordinate
