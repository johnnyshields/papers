/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowRetainedResponses
import SkewCornerDescent.Matrix.OriginalWindowGapAssembly
import SkewCornerDescent.Matrix.OriginalClosureResponseWord

/-!
# Actual internal response period from complete literal windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The complete
selected occurrence order supplies the endpoint matching and the full retained inverse
supplies equality of actual regular-ring responses on every overlapping internal interval.
The true cyclic cap-splice interval is not included. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Literal translation of a whole selected occurrence transports its complete content band. -/
theorem originalSelected_window_translate {n : ℕ} (P : Profile n) (lo hi q : ℤ)
    (v : ℤ × ℤ) (hv : content v = q)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (hb : ∀ x ∈ interiorBlockCells P b.val.val, lo ≤ content x ∧ content x < hi)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells P d.val.val) :
    originalBlockInWindow P (lo + q) (hi + q) d.val := by
  refine Or.inl ⟨originalBlockSelected_nonempty P d.val d.property, ?_⟩
  intro x hx
  rw [← he] at hx
  have h := hb (x - v) (mem_translate.mp hx)
  have hc : content (x - v) = content x - q := by
    simp only [content, Prod.fst_sub, Prod.snd_sub] at hv ⊢
    omega
  rw [hc] at h
  omega

/-- Complete equal end windows produce equality of the actual full retained response at
consecutive selected ranks. The shift is the source count minus the complete window count. -/
theorem originalWindow_internal_local_response_period {n : ℕ} (P : Profile n)
    (q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
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
    c.originalLocalResponse P (some (originalSelectedEnumeration (hD := hD) P i))
      (some (originalSelectedEnumeration (hD := hD) P ⟨i.val + 1, by omega⟩)) =
    c.originalLocalResponse P (some (originalSelectedEnumeration (hD := hD) P j))
      (some (originalSelectedEnumeration (hD := hD) P ⟨j.val + 1, hj⟩)) := by
  let E := originalSelectedEnumeration (hD := hD) P
  let i' : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by omega⟩
  let j' : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val + 1, hj⟩
  have hmatch := originalWindow_selected_index_translation (hD := hD) P q v hv hprefix
    hwindow h0 hq hLq hL
  have he := hmatch i j hji
  have he' := hmatch i' j' (by dsimp only [i', j']; omega)
  have hband (k : Fin (originalSelectedCount (hD := hD) P))
      (hk : originalSelectedCount (hD := hD) P -
        Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) ≤ k.val) :=
    (originalWindow_prefix_iff_rank P q k).mpr hk
  have hb := hband j (by omega)
  have hd := hband j' (by dsimp only [j']; omega)
  have hb' := originalSelected_window_translate P 0 (P.xi 0 - q) q v hv (E j) (E i) hb he
  have hd' := originalSelected_window_translate P 0 (P.xi 0 - q) q v hv (E j') (E i') hd he'
  apply c.originalLocalResponse_window_translate P 0 (P.xi 0) q v hv
    (by simpa only [zero_add] using hwindow) h0
    (by simpa only [zero_add] using hq) hLq hL (E j) (E j') (E i) (E i')
    (Or.inl ⟨originalBlockSelected_nonempty P (E j).val (E j).property, hb⟩)
    (Or.inl ⟨originalBlockSelected_nonempty P (E j').val (E j').property, hd⟩)
    (by simpa only [sub_add_cancel] using hb')
    (by simpa only [sub_add_cancel] using hd') he he'

/-- The full normal-dependent internal response word has the actual overlap period. -/
theorem originalWindow_internal_response_period {n : ℕ} (P : Profile n)
    (q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (h0 : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hji : j.val = i.val + (originalSelectedCount (hD := hD) P -
      Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)))) :
    c.originalInternalResponse P i = c.originalInternalResponse P j := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have hi := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have hj := j.isLt; omega⟩
  have he := c.originalWindow_internal_local_response_period P q v hv hprefix hwindow
    h0 hq hLq hL a b hji (by have hj := j.isLt; dsimp only [b]; omega)
  unfold originalInternalResponse originalHessenbergResponse Matrix.submatrix
  change c.originalLocalResponse P (originalHessenbergRows P a.succ)
    (originalHessenbergCols P (⟨i.val + 1, by have hi := i.isLt; omega⟩ :
      Fin (originalSelectedCount (hD := hD) P)).castSucc) =
    c.originalLocalResponse P (originalHessenbergRows P b.succ)
    (originalHessenbergCols P (⟨j.val + 1, by have hj := j.isLt; omega⟩ :
      Fin (originalSelectedCount (hD := hD) P)).castSucc)
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc,
    originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  exact he

/-- A literal complete window profile and the two actual private cuts produce the overlap
period of the full source response word. No response or inverse identity is assumed. -/
theorem originalWindow_response_period_from_profile {n m : ℕ} (P : Profile n) (W : Profile m)
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hji : j.val = i.val + (originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W)) :
    c.originalInternalResponse P i = c.originalInternalResponse P j := by
  have hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
    rw [hW]
    exact isSkew_translate u W.isConnectedSkew_cells.1
  have h0 := (originalProfile_interior_boundary_gaps P).1
  have hL := (originalProfile_interior_boundary_gaps P).2
  have hq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hq hx
  have hLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hLq hx
  have hcount := originalWindow_selected_count (hD := hD) P W 0 (P.xi 0 - q) u hW h0 hLq'
  exact c.originalWindow_internal_response_period P q v hv hprefix hwindow h0 hq' hLq' hL
    i j (by rw [hcount]; exact hji)

end SkewCornerDescent.Matrix.SelectedCoordinate
