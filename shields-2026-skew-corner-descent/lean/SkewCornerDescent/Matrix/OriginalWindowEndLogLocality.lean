/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalEndLogLocality
import SkewCornerDescent.Matrix.OriginalWindowOrderedLowerResponses

/-!
# Complete endpoint logarithmic jets in literal full windows

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete window geometry supplies the full ordered response neighborhoods.
Exact cap locality preserves every original normal jet below the window's
selected count. Both profiles retain their genuine maximal-component domain.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Full original left cap neighborhoods are unchanged by a complete upper window.
The selected-count embedding and every response match are source-produced. -/
theorem originalWindow_normal_left_neighborhood {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0)
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) Q)
    (i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) :
    c.originalNormalExtension Q i j = c.originalNormalExtension P i j := by
  obtain ⟨hc, hbetween⟩ := c.originalWindow_upper_ordered_responses P Q q v hwindow hq hL
  obtain ⟨_, hleft⟩ := c.originalWindow_upper_ordered_left_responses P Q q v hwindow hq hL
  let ip : Fin (originalSelectedCount (hD := hD) P + 1) := ⟨i, by omega⟩
  let jp : Fin (originalSelectedCount (hD := hD) P + 1) := ⟨j, by omega⟩
  let iq : Fin (originalSelectedCount (hD := hD) Q + 1) := ⟨i, by omega⟩
  let jq : Fin (originalSelectedCount (hD := hD) Q + 1) := ⟨j, by omega⟩
  let t : Fin (originalSelectedCount (hD := hD) Q) := ⟨j, by omega⟩
  have htq : t.castSucc = jq := by apply Fin.ext; rfl
  have heq : c.originalHessenbergResponse Q iq jq = c.originalHessenbergResponse P ip jp := by
    by_cases hz : i = 0
    · have hip : ip = 0 := Fin.ext hz
      have hiq : iq = 0 := Fin.ext hz
      rw [hip, hiq, ← htq]
      exact hleft t
    · let s : Fin (originalSelectedCount (hD := hD) Q) := ⟨i - 1, by omega⟩
      let ps : Fin (originalSelectedCount (hD := hD) P) := ⟨s.val, by have := s.isLt; omega⟩
      let pt : Fin (originalSelectedCount (hD := hD) P) := ⟨t.val, by have := t.isLt; omega⟩
      have hsQ : s.succ = iq := by apply Fin.ext; change i - 1 + 1 = i; omega
      have hsP : ps.succ = ip := by apply Fin.ext; change i - 1 + 1 = i; omega
      have htP : pt.castSucc = jp := by apply Fin.ext; rfl
      have he := hbetween s t
      change c.originalHessenbergResponse Q s.succ t.castSucc =
        c.originalHessenbergResponse P ps.succ pt.castSucc at he
      rw [hsQ, htq, hsP, htP] at he
      exact he
  have hip := c.originalNormalExtension_inside P ip jp
  have hiq := c.originalNormalExtension_inside Q iq jq
  change c.originalNormalExtension P i j = _ at hip
  change c.originalNormalExtension Q i j = _ at hiq
  rw [hiq, hip, heq]

/-- Full original right cap neighborhoods are unchanged under the exact final-rank offset
of a complete lower window, including its global end column. -/
theorem originalWindow_normal_right_neighborhood {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) Q)
    (i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) :
    c.originalNormalExtension Q (originalSelectedCount (hD := hD) Q - k + i)
        (originalSelectedCount (hD := hD) Q - k + j) =
      c.originalNormalExtension P (originalSelectedCount (hD := hD) P - k + i)
        (originalSelectedCount (hD := hD) P - k + j) := by
  obtain ⟨hc, hbetween⟩ := c.originalWindow_lower_ordered_responses P Q q v hwindow hq hL
  obtain ⟨_, hright⟩ := c.originalWindow_lower_ordered_right_responses P Q q v hwindow hq hL
  let B := originalSelectedCount (hD := hD) P
  let C := originalSelectedCount (hD := hD) Q
  let ip : Fin (B + 1) := ⟨B - k + i, by dsimp only [B] at *; omega⟩
  let jp : Fin (B + 1) := ⟨B - k + j, by dsimp only [B] at *; omega⟩
  let iq : Fin (C + 1) := ⟨C - k + i, by dsimp only [C] at *; omega⟩
  let jq : Fin (C + 1) := ⟨C - k + j, by dsimp only [C] at *; omega⟩
  let s : Fin C := ⟨C - k + i - 1, by dsimp only [C] at *; omega⟩
  let ps : Fin B := ⟨s.val + (B - C), by have := s.isLt; dsimp only [B, C] at *; omega⟩
  have hsQ : s.succ = iq := by
    apply Fin.ext
    change C - k + i - 1 + 1 = C - k + i
    dsimp only [C] at *
    omega
  have hsP : ps.succ = ip := by
    apply Fin.ext
    change C - k + i - 1 + (B - C) + 1 = B - k + i
    dsimp only [B, C] at *
    omega
  have heq : c.originalHessenbergResponse Q iq jq = c.originalHessenbergResponse P ip jp := by
    by_cases hz : C - k + j = C
    · have hjQ : jq = Fin.last C := Fin.ext hz
      have hjP : jp = Fin.last B := by
        apply Fin.ext
        change B - k + j = B
        dsimp only [B, C] at *
        omega
      have he := hright s
      change c.originalHessenbergResponse Q s.succ (Fin.last _) =
        c.originalHessenbergResponse P ps.succ (Fin.last _) at he
      rw [hsQ, hsP] at he
      rw [hjQ, hjP]
      exact he
    · let t : Fin C := ⟨C - k + j, by dsimp only [C] at *; omega⟩
      let pt : Fin B := ⟨t.val + (B - C), by have := t.isLt; dsimp only [B, C] at *; omega⟩
      have htQ : t.castSucc = jq := by apply Fin.ext; rfl
      have htP : pt.castSucc = jp := by
        apply Fin.ext
        change C - k + j + (B - C) = B - k + j
        dsimp only [B, C] at *
        omega
      have he := hbetween s t
      change c.originalHessenbergResponse Q s.succ t.castSucc =
        c.originalHessenbergResponse P ps.succ pt.castSucc at he
      rw [hsQ, htQ, hsP, htP] at he
      exact he
  have hip := c.originalNormalExtension_inside P ip jp
  have hiq := c.originalNormalExtension_inside Q iq jq
  change c.originalNormalExtension P (B - k + i) (B - k + j) = _ at hip
  change c.originalNormalExtension Q (C - k + i) (C - k + j) = _ at hiq
  rw [hiq, hip, heq]

/-- Every complete left-cap logarithmic jet below the selected count survives
restriction to a literal upper end window on the genuine maximal-component domain. -/
theorem originalWindow_left_log_coeff {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0)
    (hmaxP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ))
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) Q) :
    PowerSeries.coeff k (leftCap (c.originalNormalExtension Q)
      (originalSelectedCount (hD := hD) Q)) =
    PowerSeries.coeff k (leftCap (c.originalNormalExtension P)
      (originalSelectedCount (hD := hD) P)) := by
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q q (P.xi 0) v
    hwindow hq hL
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  have hBP : 0 < originalSelectedCount (hD := hD) P := by omega
  rw [c.original_left_log_prefix_locality Q hBQ hmaxQ k hk.le,
    c.original_left_log_prefix_locality P hBP hmaxP k (by omega)]
  rw [leftCap_congr (c.originalNormalExtension Q) (c.originalNormalExtension P) k
    (fun i j hi hj => c.originalWindow_normal_left_neighborhood P Q q v
      hwindow hq hL k hk i j hi hj)]

/-- The complete right-cap logarithmic jets survive restriction to a literal lower
end window, using its exact source-produced suffix offset. -/
theorem originalWindow_right_log_coeff {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hmaxP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ))
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) Q) :
    PowerSeries.coeff k (rightCap (c.originalNormalExtension Q) 0
      (originalSelectedCount (hD := hD) Q)) =
    PowerSeries.coeff k (rightCap (c.originalNormalExtension P) 0
      (originalSelectedCount (hD := hD) P)) := by
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q 0 (P.xi 0 - q) v
    hwindow hq hL
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  have hBP : 0 < originalSelectedCount (hD := hD) P := by omega
  rw [c.original_right_log_suffix_locality Q hBQ hmaxQ k
      (originalSelectedCount (hD := hD) Q - k) (by omega),
    c.original_right_log_suffix_locality P hBP hmaxP k
      (originalSelectedCount (hD := hD) P - k) (by omega)]
  rw [rightCap_offsets_congr (c.originalNormalExtension Q) (c.originalNormalExtension P)
    (originalSelectedCount (hD := hD) Q - k) (originalSelectedCount (hD := hD) P - k) k
    (fun i j hi hj => c.originalWindow_normal_right_neighborhood P Q q v
      hwindow hq hL k hk i j hi hj)]

end SkewCornerDescent.Matrix.SelectedCoordinate
