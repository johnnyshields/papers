/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowRemainingOccurrences

/-!
# Complete original window block equivalence

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The full window
inventory includes unselected components, selected proper minors, and empty unit blocks.
Its order equivalence and every remaining fiber are produced from literal equal windows.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The actual whole-block inventory, including the window's internal empty pivots. -/
abbrev OriginalWholeWindowBlocks {n : ℕ} (P : Profile n) (lo hi : ℤ) :=
  {b : OriginalBlocks P // originalBlockInWindow P lo hi b}

/-- Complete equal windows give an ordered block bijection and all remaining fiber maps.
No inverse, matching mask, or independent endpoint identity is carried as a premise. -/
theorem originalWindow_remaining_orderIso {n : ℕ} (P : Profile n)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi - q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi) :
    ∃ e : OriginalWholeWindowBlocks P lo (hi - q) ≃o
        OriginalWholeWindowBlocks P (lo + q) hi,
      ∀ b, ((e b).val.val : ℤ) = (b.val.val : ℤ) + v.1 ∧
        ∃ t : Fin (originalRemovedSize (hD := hD) P b.val) ≃
            Fin (originalRemovedSize (hD := hD) P (e b).val),
          ∀ k, originalResponseRows P ⟨(e b).val, t k⟩ =
              originalResponseRows P ⟨b.val, k⟩ + q ∧
            originalResponseCols P ⟨(e b).val, t k⟩ =
              originalResponseCols P ⟨b.val, k⟩ + q := by
  classical
  let hp := fun b : OriginalWholeWindowBlocks P lo (hi - q) =>
    (originalWindow_remaining_occurrence (hD := hD) P lo hi q v hv hwindow
      hlo hloq hhiq hhi b.val b.property).exists
  let f : OriginalWholeWindowBlocks P lo (hi - q) →
      OriginalWholeWindowBlocks P (lo + q) hi := fun b =>
    ⟨(hp b).choose, (hp b).choose_spec.1⟩
  have hf : ∀ b, ((f b).val.val : ℤ) = (b.val.val : ℤ) + v.1 ∧
      ∃ t : Fin (originalRemovedSize (hD := hD) P b.val) ≃
          Fin (originalRemovedSize (hD := hD) P (f b).val),
        ∀ k, originalResponseRows P ⟨(f b).val, t k⟩ =
            originalResponseRows P ⟨b.val, k⟩ + q ∧
          originalResponseCols P ⟨(f b).val, t k⟩ =
            originalResponseCols P ⟨b.val, k⟩ + q := fun b => (hp b).choose_spec.2
  have hmono : StrictMono f := by
    intro a b hab
    have ha := (hf a).1
    have hb := (hf b).1
    change a.val.val.val < b.val.val.val at hab
    change (f a).val.val.val < (f b).val.val.val
    omega
  have hrev : P.cells.filter (fun x => lo ≤ content x ∧ content x < hi - q) =
      translate (-v) (P.cells.filter fun x => lo + q ≤ content x ∧ content x < hi) := by
    rw [hwindow, translate_translate, neg_add_cancel, translate_zero]
  have hrev' : P.cells.filter (fun x => lo + q + -q ≤ content x ∧ content x < hi - q) =
      translate (-v) (P.cells.filter fun x => lo + q ≤ content x ∧
        content x < hi - q - -q) := by
    simpa only [add_neg_cancel_right, sub_neg_eq_add, sub_add_cancel] using hrev
  have hv' : content (-v) = -q := by
    dsimp only [content, Prod.fst_neg, Prod.snd_neg] at hv ⊢
    omega
  have hlo' : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q + -q := by
    simpa only [add_neg_cancel_right] using hlo
  have hhi' : ∀ x ∈ diagramInterior P.cells, content x ≠ hi - q - -q := by
    simpa only [sub_neg_eq_add, sub_add_cancel] using hhi
  have hsurj : Function.Surjective f := by
    intro b
    have hb : originalBlockInWindow P (lo + q) (hi - q - -q) b.val := by
      simpa only [sub_neg_eq_add, sub_add_cancel] using b.property
    obtain ⟨a, ha, _⟩ := originalWindow_remaining_occurrence (hD := hD)
      P (lo + q) (hi - q) (-q) (-v) hv' hrev' hloq hlo' hhi' hhiq b.val hb
    have ha' : originalBlockInWindow P lo (hi - q) a := by
      simpa only [add_neg_cancel_right] using ha.1
    let a' : OriginalWholeWindowBlocks P lo (hi - q) := ⟨a, ha'⟩
    refine ⟨a', ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    have hr := (hf a').1
    have hr' := ha.2.1
    change ((f a').val.val : ℤ) = (a.val : ℤ) + v.1 at hr
    change (a.val : ℤ) = (b.val.val : ℤ) + -v.1 at hr'
    omega
  refine ⟨{ toEquiv := Equiv.ofBijective f ⟨hmono.injective, hsurj⟩
            map_rel_iff' := fun {a b} => hmono.le_iff_le }, ?_⟩
  exact hf

end SkewCornerDescent.Matrix.SelectedCoordinate
