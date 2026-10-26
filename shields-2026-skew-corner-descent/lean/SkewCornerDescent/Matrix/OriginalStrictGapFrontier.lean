/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowPeriodDistance

/-!
# Excluding the literal source from a strict maximal span bin

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Full
internal-period intervals have the literal displacement span. Each true-cap
boundary is strictly below its complete cyclic bound. Hence the original source
has no retained interval in a strictly larger bin. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A true-cap boundary remains strictly below a complete cyclic gap bound. -/
theorem originalHessenbergDistance_boundary_lt_gap_bound {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (m : ℕ) (hm : 0 < m) (hmB : m < originalSelectedCount (hD := hD) P) (M : ℤ)
    (hbound : ∀ s : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 (m + 1) s ≤ M)
    (i k : Fin (originalSelectedCount (hD := hD) P + 1))
    (hik : i ≤ k) (hlen : k.val - i.val = m)
    (hend : i.val = 0 ∨ k.val = originalSelectedCount (hD := hD) P) :
    originalHessenbergDistance (hD := hD) P i k < (c.top : ℤ) + M := by
  have hi := i.isLt
  have hk := k.isLt
  change i.val ≤ k.val at hik
  rcases hend with hi0 | hklast
  · have hi' : i = 0 := Fin.ext hi0
    let kp : Fin (originalSelectedCount (hD := hD) P) := ⟨k.val - 1, by omega⟩
    have hk' : kp.succ = k := by
      apply Fin.ext
      change k.val - 1 + 1 = k.val
      omega
    have hkp : kp.val + 1 < originalSelectedCount (hD := hD) P := by dsimp only [kp]; omega
    have hw := c.originalCompletedGap_cyclic_left_window_lt P hB kp hkp
    dsimp only at hw
    have he : kp.val + 2 = m + 1 := by dsimp only [kp]; omega
    rw [hk', he] at hw
    rw [hi']
    exact hw.trans_le (add_le_add_right (hbound _) _)
  · have hk' : k = Fin.last (originalSelectedCount (hD := hD) P) := Fin.ext hklast
    let ip : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val - 1, by omega⟩
    have hi' : ip.succ = i := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    have hw := c.originalCompletedGap_cyclic_right_window_lt P hB ip
    have he : originalSelectedCount (hD := hD) P - ip.val = m + 1 := by
      dsimp only [ip]; omega
    rw [hi', he] at hw
    rw [hk']
    exact hw.trans_le (add_le_add_right (hbound _) _)

/-- A strict bin above the full internal-period span contains no source interval.
The source period distance and both true-cap exclusions are derived from geometry. -/
theorem originalWindow_strict_filtered_inventory_zero {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (j : ℕ) (hj : 2 ≤ j) (hjB : j ≤ originalSelectedCount (hD := hD) P)
    (hlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)
    (M : ℤ) (hstrict : q < M)
    (hbound : ∀ s : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 j s ≤ M)
    (K : ℕ+) (hKeq : (K : ℤ) = (c.top : ℤ) + M) :
    c.originalFilteredIntervalInventory P j K = 0 := by
  classical
  unfold originalFilteredIntervalInventory
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hret
  · obtain ⟨hik, hcost, hdist⟩ := hret
    have hbound' : ∀ s : ZMod (originalSelectedCount (hD := hD) P),
        windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
          1 (j - 1 + 1) s ≤ M := by
      intro s
      have h : j - 1 + 1 = j := by omega
      simpa only [h] using hbound s
    by_cases hend : i.val = 0 ∨ k.val = originalSelectedCount (hD := hD) P
    · have hlt := c.originalHessenbergDistance_boundary_lt_gap_bound P hB
        (j - 1) (by omega) (by omega) M hbound' i k hik hcost hend
      rw [hdist, hKeq] at hlt
      exact (lt_irrefl _ hlt).elim
    · have hi := i.isLt
      have hk := k.isLt
      have hipos : 0 < i.val := by omega
      have hklt : k.val < originalSelectedCount (hD := hD) P := by omega
      let ip : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val - 1, by omega⟩
      let kp : Fin (originalSelectedCount (hD := hD) P) := ⟨k.val, hklt⟩
      have hi' : ip.succ = i := by
        apply Fin.ext
        change i.val - 1 + 1 = i.val
        omega
      have hk' : kp.castSucc = k := Fin.ext rfl
      have hd := c.originalWindow_selected_period_distance P W q u v hv hW hwindow hq hLq
        ip kp (by dsimp only [ip, kp]; omega)
      rw [hi', hk', hdist, hKeq] at hd
      omega
  · rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
