/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClasses
import SkewCornerDescent.Matrix.OriginalWindowResponsePeriod
import SkewCornerDescent.Matrix.OriginalWindowRestrictionWord
import SkewCornerDescent.PhaseInventory

/-!
# Actual cyclic class words and complete original occurrence counts

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`, `lem:peeling`).
Literal end windows supply the complete source period projection and the full
window prefix. Class masks therefore count the same original response occurrences,
without quotienting positions or assuming an abstract word correspondence.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete literal windows identify both whole internal words with the same
actual cyclic class word. The window translation and period size are produced. -/
theorem originalWindow_responseClass_projection {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (j : ℕ) [NeZero j]
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W) :
    ∃ hperiod : j ≤ originalSelectedCount (hD := hD) P - 1,
      (∀ i : Fin (originalSelectedCount (hD := hD) P - 1),
        c.originalInternalResidue P i = (c.originalResponseClassWord P j hperiod
          (i.val : ZMod j)).val) ∧
      (∀ i : Fin (originalSelectedCount (hD := hD) W - 1),
        c.originalInternalResidue W i = (c.originalResponseClassWord P j hperiod
          (i.val : ZMod j)).val) := by
  have hj : 0 < j := Nat.pos_of_ne_zero (NeZero.ne j)
  have hperiod : j ≤ originalSelectedCount (hD := hD) P - 1 := by omega
  have hp (i k : Fin (originalSelectedCount (hD := hD) P - 1)) (hki : k.val = i.val + j) :
      c.originalInternalResidue P i = c.originalInternalResidue P k := by
    have he := c.originalWindow_response_period_from_profile P W q u v hv hW hwindow
      hcutq hcutLq i k (by rw [← hjlen]; exact hki)
    exact congrArg c.regularResidue he
  have hsource (i : Fin (originalSelectedCount (hD := hD) P - 1)) :=
    finiteWordCycle_eq (c.originalInternalResidue P) hperiod hp i
  have hclass (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
      c.originalInternalResidue P i = (c.originalResponseClassWord P j hperiod
        (i.val : ZMod j)).val := by
    have hc := congrFun (c.originalResponseClassWord_val P j hperiod) (i.val : ZMod j)
    exact (hsource i).trans hc.symm
  have hupper : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate (v + u) W.cells := by
    rw [hwindow, hW, translate_translate]
  have hWupper : W.cells = translate (-(v + u))
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0) := by
    rw [hupper, translate_translate, neg_add_cancel, translate_zero]
  have hq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hcutq hx
  obtain ⟨hcount, hw⟩ := c.originalWindow_restriction_internal_word P W q (-(v + u))
    hWupper hq' (originalProfile_interior_boundary_gaps P).2
  refine ⟨hperiod, hclass, ?_⟩
  intro i
  change c.regularResidue (c.originalInternalResponse W i) = _
  rw [hw i]
  exact hclass ⟨i.val, by have := i.isLt; omega⟩

private theorem occurrence_count_eq_mask_window {L j : ℕ} {α F : Type*}
    [NeZero j] [DecidableEq α] [DecidableEq F]
    (f : Fin L → F) (word : ZMod j → α) (value : α → F)
    (hinj : Function.Injective value) (hf : ∀ i, f i = value (word (i.val : ZMod j)))
    (a : α) :
    (Finset.univ.filter fun i => f i = value a).card =
      windowSum (classMask word a) 1 L 0 := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  unfold windowSum
  simp only [zero_add, nsmul_eq_mul, mul_one]
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => classMask word a (i : ZMod j)) L]
  apply Finset.sum_congr rfl
  intro i _
  have he : f i = value a ↔ word (i.val : ZMod j) = a := by
    rw [hf i]
    exact hinj.eq_iff
  simp only [he, classMask]

/-- The actual source and window class counts are their exact finite mask
windows, including every repeated occurrence and the empty internal-window case. -/
theorem originalWindow_responseClass_counts {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (j : ℕ) [NeZero j]
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W) :
    ∃ hperiod : j ≤ originalSelectedCount (hD := hD) P - 1,
      ∀ a : c.OriginalResponseClass P,
      (Finset.univ.filter fun i => c.originalInternalResidue P i = a.val).card =
        windowSum (classMask (c.originalResponseClassWord P j hperiod) a) 1
          (originalSelectedCount (hD := hD) P - 1) 0 ∧
      (Finset.univ.filter fun i => c.originalInternalResidue W i = a.val).card =
        windowSum (classMask (c.originalResponseClassWord P j hperiod) a) 1
          (originalSelectedCount (hD := hD) W - 1) 0 := by
  classical
  obtain ⟨hperiod, hP, hW'⟩ := c.originalWindow_responseClass_projection P W q u v hv hW
    hwindow hcutq hcutLq hC j hjlen
  refine ⟨hperiod, fun a => ?_⟩
  exact ⟨occurrence_count_eq_mask_window _ _ Subtype.val Subtype.val_injective hP a,
    occurrence_count_eq_mask_window _ _ Subtype.val Subtype.val_injective hW' a⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
