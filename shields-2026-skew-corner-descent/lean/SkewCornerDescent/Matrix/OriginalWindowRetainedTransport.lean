/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowResponseIntervals

/-!
# Complete literal transport of actual retained response intervals

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Two chosen
translated selected occurrences identify their complete source response intervals.
Every intermediate block, both boundary proper minors, and every empty unit pivot
are transported, with full original endpoints. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Matching selected endpoints in complete equal windows gives an equivalence of the
entire actual retained intervals, not only their diagonal component determinants. -/
theorem originalWindow_retained_interval_equiv {n : ℕ} (P : Profile n)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi - q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (b d b' d' : OriginalSelectedBlocks (hD := hD) P)
    (hb : originalBlockInWindow P lo (hi - q) b.val)
    (hd : originalBlockInWindow P lo (hi - q) d.val)
    (hb' : originalBlockInWindow P (lo + q) hi b'.val)
    (hd' : originalBlockInWindow P (lo + q) hi d'.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells P b'.val.val)
    (he' : translate v (interiorBlockCells P d.val.val) = interiorBlockCells P d'.val.val) :
    ∃ e : OriginalResponseInterval (hD := hD) P (some b) (some d) ≃
        OriginalResponseInterval (hD := hD) P (some b') (some d'),
      ∀ i, originalResponseRows P (e i).1.1 = originalResponseRows P i.1.1 + q ∧
        originalResponseCols P (e i).1.1 = originalResponseCols P i.1.1 + q := by
  classical
  obtain ⟨o, ho⟩ := originalWindow_remaining_orderIso (hD := hD) P lo hi q v hv
    hwindow hlo hloq hhiq hhi
  let b0 : OriginalWholeWindowBlocks P lo (hi - q) := ⟨b.val, hb⟩
  let d0 : OriginalWholeWindowBlocks P lo (hi - q) := ⟨d.val, hd⟩
  let b1 : OriginalWholeWindowBlocks P (lo + q) hi := ⟨b'.val, hb'⟩
  let d1 : OriginalWholeWindowBlocks P (lo + q) hi := ⟨d'.val, hd'⟩
  have himage (a : OriginalSelectedBlocks (hD := hD) P)
      (a' : OriginalSelectedBlocks (hD := hD) P)
      (ha : originalBlockInWindow P lo (hi - q) a.val)
      (ha' : originalBlockInWindow P (lo + q) hi a'.val)
      (he : translate v (interiorBlockCells P a.val.val) = interiorBlockCells P a'.val.val) :
      o ⟨a.val, ha⟩ = ⟨a'.val, ha'⟩ := by
    have hr := (ho ⟨a.val, ha⟩).1
    have hs := (interiorBlockCells_translated_row_extremes P P a.val.val a'.val.val
      (originalBlockSelected_nonempty P a.val a.property)
      (originalBlockSelected_nonempty P a'.val a'.property) v he).1
    rw [a.val.property, a'.val.property] at hs
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    change ((o ⟨a.val, ha⟩).val.val : ℤ) = (a.val.val : ℤ) + v.1 at hr
    change (a'.val.val : ℤ) = (a.val.val : ℤ) + v.1 at hs
    change (o ⟨a.val, ha⟩).val.val.val = a'.val.val.val
    omega
  have hbmap : o b0 = b1 := himage b b' hb hb' he
  have hdmap : o d0 = d1 := himage d d' hd hd' he'
  let t := fun a => (ho a).2.choose
  let f := (Equiv.sigmaCongrRight t).trans
    (Equiv.sigmaCongrLeft (β := fun a : OriginalWholeWindowBlocks P (lo + q) hi =>
      Fin (originalRemovedSize (hD := hD) P a.val)) o.toEquiv)
  have hpred (i : OriginalWholeWindowRemaining (hD := hD) P lo (hi - q)) :
      (b.val ≤ i.1.val ∧ i.1.val ≤ d.val) ↔
        (b'.val ≤ (f i).1.val ∧ (f i).1.val ≤ d'.val) := by
    change (b0 ≤ i.1 ∧ i.1 ≤ d0) ↔ (b1 ≤ o i.1 ∧ o i.1 ≤ d1)
    rw [← hbmap, ← hdmap, o.le_iff_le, o.le_iff_le]
  let s := originalWindowResponseIntervalEquiv P lo (hi - q) b d hb hd
  let u := originalWindowResponseIntervalEquiv P (lo + q) hi b' d' hb' hd'
  let e := (s.trans (f.subtypeEquiv hpred)).trans u.symm
  refine ⟨e, fun i => ?_⟩
  exact (ho (s i).val.1).2.choose_spec (s i).val.2

end SkewCornerDescent.Matrix.SelectedCoordinate
