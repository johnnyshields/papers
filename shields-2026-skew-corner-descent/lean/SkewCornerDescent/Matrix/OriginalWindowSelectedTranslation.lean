/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowSelectedRanks
import SkewCornerDescent.Matrix.OriginalCompletedGaps

/-!
# Literal selected-window translations and overlapping source gaps

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
The complete original occurrence inventories produce the indexed translation; the rank
shift is the source count minus the complete window count. Their actual endpoint differences
then give period equality on every overlapping internal gap. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Complete equal end windows match the original selected ranks with no missing occurrence
or identification of repeated function classes. All hypotheses concern literal source cells. -/
theorem originalWindow_selected_index_translation {n : ℕ} (P : Profile n)
    (q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (h0 : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0) :
    ∀ i j : Fin (originalSelectedCount (hD := hD) P),
      j.val = i.val + (originalSelectedCount (hD := hD) P -
        Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q))) →
      translate v (interiorBlockCells P
        (originalSelectedEnumeration (hD := hD) P j).val.val) =
      interiorBlockCells P (originalSelectedEnumeration (hD := hD) P i).val.val := by
  have hex := originalWindow_selected_orderIso (hD := hD) P 0 (P.xi 0) q v hv hprefix
    (by simpa only [zero_add] using hwindow) h0
    (by simpa only [zero_add] using hq) hLq hL
  rw [zero_add] at hex
  obtain ⟨e, he⟩ := hex
  intro i j hji
  let E := originalSelectedEnumeration (hD := hD) P
  have hj : ∀ x ∈ interiorBlockCells P (E j).val.val,
      0 ≤ content x ∧ content x < P.xi 0 - q :=
    (originalWindow_prefix_iff_rank P q j).mpr (by omega)
  let b : OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q) := ⟨E j, hj⟩
  have hr := originalWindow_selected_rank_shift P q e b
  have hb : E.symm b.val = j := E.symm_apply_apply j
  have hi : E.symm (e b).val = i := by
    apply Fin.ext
    change (E.symm (e b).val).val + _ = (E.symm b.val).val at hr
    rw [hb] at hr
    omega
  have heu : (e b).val = E i := by
    rw [← hi, E.apply_symm_apply]
  have hmatch := he b
  rw [heu] at hmatch
  exact hmatch.symm

/-- Consecutive translated whole occurrences give the actual selected gap period on the
entire overlapping internal range. The true closing cap-splice gap is not silently included. -/
theorem originalWindow_internal_gap_period {n : ℕ} (P : Profile n)
    (c : SelectedCoordinate D hD) (q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (h0 : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0)
    (i j : Fin (originalSelectedCount (hD := hD) P))
    (hji : j.val = i.val + (originalSelectedCount (hD := hD) P -
      Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q))))
    (hj : j.val + 1 < originalSelectedCount (hD := hD) P) :
    c.originalCompletedGap P i = c.originalCompletedGap P j := by
  have hi : i.val + 1 < originalSelectedCount (hD := hD) P := by omega
  let i' : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, hi⟩
  let j' : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val + 1, hj⟩
  have hmatch := originalWindow_selected_index_translation (hD := hD) P q v hv hprefix hwindow
    h0 hq hLq hL
  have ha := congrArg minContent (hmatch i j hji)
  have hb := congrArg minContent (hmatch i' j' (by dsimp only [i', j']; omega))
  let E := originalSelectedEnumeration (hD := hD) P
  have hmin (k : Fin (originalSelectedCount (hD := hD) P)) :=
    interiorBlockCells_minContent P (E k).val.val
      (originalBlockSelected_nonempty P (E k).val (E k).property)
  have hne (k : Fin (originalSelectedCount (hD := hD) P)) :=
    (interiorBlockCells_connected P (E k).val.val
      (originalBlockSelected_nonempty P (E k).val (E k).property)).2.1
  rw [minContent_translate (hne j), hmin i, hmin j, hv] at ha
  rw [minContent_translate (hne j'), hmin i', hmin j', hv] at hb
  dsimp only [E] at ha hb
  rw [originalCompletedGap, ite_eq_right (by omega), originalCompletedGap,
    ite_eq_right (by omega),
    c.originalHessenbergDistance_between P i i' rfl,
    c.originalHessenbergDistance_between P j j' rfl]
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
