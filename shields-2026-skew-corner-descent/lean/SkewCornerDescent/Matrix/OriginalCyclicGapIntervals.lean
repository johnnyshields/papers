/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalCyclicGapBounds

/-!
# Exactly which original intervals reach the periodic protected top

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
All internal endpoint windows reach the completed cyclic sum; neither true-cap
boundary reaches it. This is literal endpoint geometry, not a response-class count.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At a positive cost shorter than the complete state span, equality with the
completed cyclic top is equivalent to having neither original exterior endpoint. -/
theorem originalHessenbergDistance_eq_cyclic_top_iff {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (m : ℕ) (hm : 0 < m) (hmB : m < originalSelectedCount (hD := hD) P) (H : ℤ)
    (hwindow : ∀ s : ZMod (originalSelectedCount (hD := hD) P),
      CyclicWindows.windowSum
        (fun z => c.originalCompletedGap P
          ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z))
        1 (m + 1) s = H)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1))
    (hij : i ≤ j) (hlen : j.val - i.val = m) :
    originalHessenbergDistance (hD := hD) P i j = (c.top : ℤ) + H ↔
      0 < i.val ∧ j.val < originalSelectedCount (hD := hD) P := by
  let B := originalSelectedCount (hD := hD) P
  have hi := i.isLt
  have hj := j.isLt
  change i.val ≤ j.val at hij
  by_cases hi0 : i.val = 0
  · have hi' : i = 0 := Fin.ext hi0
    have hjpos : 0 < j.val := by omega
    have hjB : j.val < B := by dsimp [B]; omega
    let jp : Fin B := ⟨j.val - 1, by omega⟩
    have hj' : jp.succ = j := by apply Fin.ext; dsimp [jp]; omega
    have hjp : jp.val + 1 < B := by dsimp [jp]; omega
    have hw := c.originalCompletedGap_cyclic_left_window_lt P hB jp hjp
    dsimp only at hw
    have he : jp.val + 2 = m + 1 := by dsimp [jp]; omega
    rw [hj', he, hwindow _] at hw
    rw [hi']
    constructor
    · intro h
      exact (ne_of_lt hw h).elim
    · intro h
      have := h.1
      change 0 < 0 at this
      omega
  · have hipos : 0 < i.val := by omega
    let ip : Fin B := ⟨i.val - 1, by dsimp [B]; omega⟩
    have hi' : ip.succ = i := by apply Fin.ext; dsimp [ip]; omega
    by_cases hjlast : j.val = B
    · have hj' : j = Fin.last (originalSelectedCount (hD := hD) P) := by
        apply Fin.ext
        exact hjlast
      have hw := c.originalCompletedGap_cyclic_right_window_lt P hB ip
      have he : originalSelectedCount (hD := hD) P - ip.val = m + 1 := by
        dsimp [ip, B] at hjlast ⊢
        omega
      rw [hi', he, hwindow _] at hw
      constructor
      · intro h
        rw [hj'] at h
        exact (ne_of_lt hw h).elim
      · intro h
        have := h.2
        dsimp [B] at hjlast
        omega
    · have hjpos : 0 < j.val := by omega
      have hjB : j.val < B := by omega
      let jp : Fin B := ⟨j.val - 1, by omega⟩
      have hj' : jp.succ = j := by apply Fin.ext; dsimp [jp]; omega
      have hij' : ip ≤ jp := by change ip.val ≤ jp.val; dsimp [ip, jp]; omega
      have hjp : jp.val + 1 < B := by dsimp [jp]; omega
      have he : jp.val - ip.val + 1 = m + 1 := by dsimp [ip, jp]; omega
      have hw := c.originalCompletedGap_cyclic_internal_window P ip jp hij' hjp
      rw [hi', hj', he, hwindow _] at hw
      exact ⟨fun _ => ⟨hipos, hjB⟩, fun _ => hw⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
