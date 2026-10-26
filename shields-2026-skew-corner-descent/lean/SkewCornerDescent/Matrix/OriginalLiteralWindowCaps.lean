/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowIntervals
import SkewCornerDescent.Matrix.OriginalWindowCapIntervals

/-!
# Entire actual cap intervals between literal end windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Complete
literal windows identify every remaining cap position once the actual whole cap is
contained in the window. The selected boundary's proper minor is retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Literal whole-window copying preserves the one-sided part inside that
window, without requiring the source's entire exterior cap to lie in it. -/
theorem originalLiteralWindow_filtered_cap_equiv {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhi : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P)
    (b' : OriginalSelectedBlocks (hD := hD) Q)
    (hb : originalBlockInWindow P lo hi b.val)
    (hb' : originalBlockInWindow Q (lo + q) (hi + q) b'.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val) :
    ∃ e : {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
        originalCapBlockSide upper b i.1.val} ≃
      {i : OriginalWholeWindowRemaining (hD := hD) Q (lo + q) (hi + q) //
        originalCapBlockSide upper b' i.1.val},
      ∀ i, originalResponseRows Q ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseRows P ⟨i.val.1.val, i.val.2⟩ + q ∧
        originalResponseCols Q ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseCols P ⟨i.val.1.val, i.val.2⟩ + q := by
  classical
  obtain ⟨o, ho⟩ := originalLiteralWindow_remaining_orderIso (hD := hD) P Q lo hi q v hv
    hwindow hlo hloq hhiq hhi
  let b0 : OriginalWholeWindowBlocks P lo hi := ⟨b.val, hb⟩
  let b1 : OriginalWholeWindowBlocks Q (lo + q) (hi + q) := ⟨b'.val, hb'⟩
  have hbmap : o b0 = b1 := by
    have hr := (ho b0).1
    have hs := (interiorBlockCells_translated_row_extremes P Q b.val.val b'.val.val
      (originalBlockSelected_nonempty P b.val b.property)
      (originalBlockSelected_nonempty Q b'.val b'.property) v he).1
    rw [b.val.property, b'.val.property] at hs
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    change ((o b0).val.val : ℤ) = (b.val.val : ℤ) + v.1 at hr
    change (b'.val.val : ℤ) = (b.val.val : ℤ) + v.1 at hs
    change (o b0).val.val.val = b'.val.val.val
    omega
  let t := fun a => (ho a).2.choose
  let f := (Equiv.sigmaCongrRight t).trans
    (Equiv.sigmaCongrLeft (β := fun a : OriginalWholeWindowBlocks Q (lo + q) (hi + q) =>
      Fin (originalRemovedSize (hD := hD) Q a.val)) o.toEquiv)
  have hpred (i : OriginalWholeWindowRemaining (hD := hD) P lo hi) :
      originalCapBlockSide upper b i.1.val ↔ originalCapBlockSide upper b' (f i).1.val := by
    cases upper
    · change b0 ≤ i.1 ↔ b1 ≤ o i.1
      rw [← hbmap, o.le_iff_le]
    · change i.1 ≤ b0 ↔ o i.1 ≤ b1
      rw [← hbmap, o.le_iff_le]
  exact ⟨f.subtypeEquiv hpred, fun i => (ho i.val.1).2.choose_spec i.val.2⟩

/-- Literal window correspondence preserves the entire one-sided remaining cap interval. -/
theorem originalLiteralWindow_cap_interval_equiv {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhi : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P)
    (b' : OriginalSelectedBlocks (hD := hD) Q)
    (hcontained : ∀ a, originalCapBlockSide upper b a → originalBlockInWindow P lo hi a)
    (hcontained' : ∀ a, originalCapBlockSide upper b' a →
      originalBlockInWindow Q (lo + q) (hi + q) a)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val) :
    ∃ e : OriginalResponseInterval (hD := hD) P
        (originalClosureCapLeft upper b) (originalClosureCapRight upper b) ≃
      OriginalResponseInterval (hD := hD) Q
        (originalClosureCapLeft upper b') (originalClosureCapRight upper b'),
      ∀ i, originalResponseRows Q (e i).1.1 = originalResponseRows P i.1.1 + q ∧
        originalResponseCols Q (e i).1.1 = originalResponseCols P i.1.1 + q := by
  classical
  have hb := hcontained b.val (by cases upper <;> exact le_rfl)
  have hb' := hcontained' b'.val (by cases upper <;> exact le_rfl)
  obtain ⟨f, hf⟩ := originalLiteralWindow_filtered_cap_equiv (hD := hD) P Q lo hi q v hv
    hwindow hlo hloq hhiq hhi upper b b' hb hb' he
  let s := originalWindowCapIntervalEquiv P lo hi upper b hcontained
  let u := originalWindowCapIntervalEquiv Q (lo + q) (hi + q) upper b' hcontained'
  let e := (s.trans f).trans u.symm
  exact ⟨e, fun i => hf (s i)⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
