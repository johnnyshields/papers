/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowRemaining
import SkewCornerDescent.Matrix.OriginalWindowRemainingEquiv

/-!
# Ordered complete remaining inventories of two literal profile windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The actual
source order and every remaining fiber map are produced from complete parent-cell windows.
The reverse literal translation proves surjectivity, including unit pivots. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Complete literal profile windows produce their ordered whole-block bijection. -/
theorem originalLiteralWindow_remaining_orderIso {n m : ℕ} (P : Profile n)
    (Q : Profile m)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhi : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q) :
    ∃ e : OriginalWholeWindowBlocks P lo (hi) ≃o
        OriginalWholeWindowBlocks Q (lo + q) (hi + q),
      ∀ b, ((e b).val.val : ℤ) = (b.val.val : ℤ) + v.1 ∧
        ∃ t : Fin (originalRemovedSize (hD := hD) P b.val) ≃
            Fin (originalRemovedSize (hD := hD) Q (e b).val),
          ∀ k, originalResponseRows Q ⟨(e b).val, t k⟩ =
              originalResponseRows P ⟨b.val, k⟩ + q ∧
            originalResponseCols Q ⟨(e b).val, t k⟩ =
              originalResponseCols P ⟨b.val, k⟩ + q := by
  classical
  let hp := fun b : OriginalWholeWindowBlocks P lo (hi) =>
    (originalLiteralWindow_remaining_occurrence (hD := hD) P Q lo hi q v hv hwindow
      hlo hloq hhiq hhi b.val b.property).exists
  let f : OriginalWholeWindowBlocks P lo (hi) →
      OriginalWholeWindowBlocks Q (lo + q) (hi + q) := fun b =>
    ⟨(hp b).choose, (hp b).choose_spec.1⟩
  have hf : ∀ b, ((f b).val.val : ℤ) = (b.val.val : ℤ) + v.1 ∧
      ∃ t : Fin (originalRemovedSize (hD := hD) P b.val) ≃
          Fin (originalRemovedSize (hD := hD) Q (f b).val),
        ∀ k, originalResponseRows Q ⟨(f b).val, t k⟩ =
            originalResponseRows P ⟨b.val, k⟩ + q ∧
          originalResponseCols Q ⟨(f b).val, t k⟩ =
            originalResponseCols P ⟨b.val, k⟩ + q := fun b => (hp b).choose_spec.2
  have hmono : StrictMono f := by
    intro a b hab
    have ha := (hf a).1
    have hb := (hf b).1
    change a.val.val.val < b.val.val.val at hab
    change (f a).val.val.val < (f b).val.val.val
    omega
  have hrev : P.cells.filter (fun x => lo ≤ content x ∧ content x < hi) =
      translate (-v) (Q.cells.filter fun x => lo + q ≤ content x ∧ content x < hi + q) := by
    rw [hwindow, translate_translate, neg_add_cancel, translate_zero]
  have hrev' : P.cells.filter (fun x => lo + q + -q ≤ content x ∧
      content x < hi + q + -q) =
      translate (-v) (Q.cells.filter fun x => lo + q ≤ content x ∧ content x < hi + q) := by
    simpa only [add_neg_cancel_right] using hrev
  have hv' : content (-v) = -q := by
    dsimp only [content, Prod.fst_neg, Prod.snd_neg] at hv ⊢
    omega
  have hlo' : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q + -q := by
    simpa only [add_neg_cancel_right] using hlo
  have hhi' : ∀ x ∈ diagramInterior P.cells, content x ≠ hi + q + -q := by
    simpa only [add_neg_cancel_right] using hhiq
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a, ha, _⟩ := originalLiteralWindow_remaining_occurrence (hD := hD)
      Q P (lo + q) (hi + q) (-q) (-v) hv' hrev' hloq hlo' hhi hhi' b.val b.property
    have ha' : originalBlockInWindow P lo hi a := by
      simpa only [add_neg_cancel_right] using ha.1
    let a' : OriginalWholeWindowBlocks P lo hi := ⟨a, ha'⟩
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
