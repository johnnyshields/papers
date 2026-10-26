/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowOrder
import SkewCornerDescent.Matrix.OriginalWindowResponseIntervals

/-!
# Complete retained intervals between literal profile windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Complete
literal windows transport the entire actual response interval between matched selected
occurrences, including both boundary proper minors and intermediate unit blocks. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Matching selected endpoints in complete equal windows gives an equivalence of the
entire actual retained intervals, not only their diagonal component determinants. -/
theorem originalLiteralWindow_retained_interval_equiv {n m : ℕ} (P : Profile n)
    (Q : Profile m)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhi : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (b' d' : OriginalSelectedBlocks (hD := hD) Q)
    (hb : originalBlockInWindow P lo (hi) b.val)
    (hd : originalBlockInWindow P lo (hi) d.val)
    (hb' : originalBlockInWindow Q (lo + q) (hi + q) b'.val)
    (hd' : originalBlockInWindow Q (lo + q) (hi + q) d'.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val)
    (he' : translate v (interiorBlockCells P d.val.val) = interiorBlockCells Q d'.val.val) :
    ∃ e : OriginalResponseInterval (hD := hD) P (some b) (some d) ≃
        OriginalResponseInterval (hD := hD) Q (some b') (some d'),
      ∀ i, originalResponseRows Q (e i).1.1 = originalResponseRows P i.1.1 + q ∧
        originalResponseCols Q (e i).1.1 = originalResponseCols P i.1.1 + q := by
  classical
  obtain ⟨o, ho⟩ := originalLiteralWindow_remaining_orderIso (hD := hD) P Q lo hi q v hv
    hwindow hlo hloq hhiq hhi
  let b0 : OriginalWholeWindowBlocks P lo (hi) := ⟨b.val, hb⟩
  let d0 : OriginalWholeWindowBlocks P lo (hi) := ⟨d.val, hd⟩
  let b1 : OriginalWholeWindowBlocks Q (lo + q) (hi + q) := ⟨b'.val, hb'⟩
  let d1 : OriginalWholeWindowBlocks Q (lo + q) (hi + q) := ⟨d'.val, hd'⟩
  have himage (a : OriginalSelectedBlocks (hD := hD) P)
      (a' : OriginalSelectedBlocks (hD := hD) Q)
      (ha : originalBlockInWindow P lo (hi) a.val)
      (ha' : originalBlockInWindow Q (lo + q) (hi + q) a'.val)
      (he : translate v (interiorBlockCells P a.val.val) = interiorBlockCells Q a'.val.val) :
      o ⟨a.val, ha⟩ = ⟨a'.val, ha'⟩ := by
    have hr := (ho ⟨a.val, ha⟩).1
    have hs := (interiorBlockCells_translated_row_extremes P Q a.val.val a'.val.val
      (originalBlockSelected_nonempty P a.val a.property)
      (originalBlockSelected_nonempty Q a'.val a'.property) v he).1
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
    (Equiv.sigmaCongrLeft (β := fun a : OriginalWholeWindowBlocks Q (lo + q) (hi + q) =>
      Fin (originalRemovedSize (hD := hD) Q a.val)) o.toEquiv)
  have hpred (i : OriginalWholeWindowRemaining (hD := hD) P lo (hi)) :
      (b.val ≤ i.1.val ∧ i.1.val ≤ d.val) ↔
        (b'.val ≤ (f i).1.val ∧ (f i).1.val ≤ d'.val) := by
    change (b0 ≤ i.1 ∧ i.1 ≤ d0) ↔ (b1 ≤ o i.1 ∧ o i.1 ≤ d1)
    rw [← hbmap, ← hdmap, o.le_iff_le, o.le_iff_le]
  let s := originalWindowResponseIntervalEquiv P lo (hi) b d hb hd
  let u := originalWindowResponseIntervalEquiv Q (lo + q) (hi + q) b' d' hb' hd'
  let e := (s.trans (f.subtypeEquiv hpred)).trans u.symm
  refine ⟨e, fun i => ?_⟩
  exact (ho (s i).val.1).2.choose_spec (s i).val.2

end SkewCornerDescent.Matrix.SelectedCoordinate
