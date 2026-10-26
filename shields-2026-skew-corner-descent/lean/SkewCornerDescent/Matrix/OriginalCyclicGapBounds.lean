/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalCompletedGaps
import SkewCornerDescent.CyclicGapPeriod

/-!
# Actual interval bounds from completed cyclic gaps

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Every ordered interval is treated, including the two true-cap boundary regimes.
The cyclic gap bound is separate from the inherited-period construction.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A uniform completed cyclic gap-window bound gives the literal distance bound
for every actual interval of the corresponding positive contraction cost. Boundary
intervals satisfy a strict bound because their other true cap is positive. -/
theorem originalHessenbergDistance_bound_of_cyclic_gaps {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (m : ℕ) (hm : 0 < m) (hmB : m < originalSelectedCount (hD := hD) P) (H : ℤ)
    (hwindow : ∀ s : ZMod (originalSelectedCount (hD := hD) P),
      CyclicWindows.windowSum
        (fun z => c.originalCompletedGap P
          ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z))
        1 (m + 1) s ≤ H)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1))
    (hij : i ≤ j) (hlen : j.val - i.val = m) :
    originalHessenbergDistance (hD := hD) P i j ≤ (c.top : ℤ) + H := by
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
    rw [hj', he] at hw
    rw [hi']
    exact hw.le.trans (add_le_add_right (hwindow _) _)
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
      rw [hi', he] at hw
      rw [hj']
      exact hw.le.trans (add_le_add_right (hwindow _) _)
    · have hjpos : 0 < j.val := by omega
      have hjB : j.val < B := by omega
      let jp : Fin B := ⟨j.val - 1, by omega⟩
      have hj' : jp.succ = j := by apply Fin.ext; dsimp [jp]; omega
      have hij' : ip ≤ jp := by change ip.val ≤ jp.val; dsimp [ip, jp]; omega
      have hjp : jp.val + 1 < B := by dsimp [jp]; omega
      have he : jp.val - ip.val + 1 = m + 1 := by dsimp [ip, jp]; omega
      have hw := c.originalCompletedGap_cyclic_internal_window P ip jp hij' hjp
      rw [hi', hj', he] at hw
      rw [hw]
      exact add_le_add_right (hwindow _) _

/-- An inherited period of the actual completed gap word produces every literal
fixed-cost distance bound. The period is an input here; its construction from the
complete equal-window family is not replaced by a bound hypothesis. -/
theorem originalHessenbergDistance_bound_of_periodic_gaps {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (r k m : ℕ) (hm : 0 < m) (hmB : m < originalSelectedCount (hD := hD) P)
    (hlen : m + 1 = k * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P
        ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (i j : Fin (originalSelectedCount (hD := hD) P + 1))
    (hij : i ≤ j) (hcost : j.val - i.val = m) :
    originalHessenbergDistance (hD := hD) P i j ≤ (c.top : ℤ) +
      k • CyclicWindows.windowSum
        (fun z => c.originalCompletedGap P
          ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z)) 1 r 0 := by
  apply c.originalHessenbergDistance_bound_of_cyclic_gaps P hB m hm hmB
    _ _ i j hij hcost
  intro s
  rw [hlen, CyclicWindows.windowSum_of_zmod_period_multiple _ r hp]

/-- The period sum is the paper's span increment, produced from the literal parent
span and selected count rather than assumed as a cyclic inventory identity. -/
theorem originalCompletedGap_period_sum {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (r b : ℕ) (hb : 0 < b) (δ : ℤ)
    (hcount : originalSelectedCount (hD := hD) P = b * r)
    (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * δ)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P
        ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    CyclicWindows.windowSum
      (fun z => c.originalCompletedGap P
        ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z)) 1 r 0 = δ := by
  classical
  let f := fun z => c.originalCompletedGap P
    ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z)
  have hsum : ∑ z, f z = (b : ℤ) * δ := by
    have he := (ZMod.finEquiv (originalSelectedCount (hD := hD) P)).toEquiv.sum_comp f
    change (∑ x, c.originalCompletedGap P
      ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm
        ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)) x))) = ∑ z, f z at he
    simp only [RingEquiv.symm_apply_apply] at he
    rw [← he, c.originalCompletedGap_sum P hB, hspan]
  have hw := CyclicWindows.zmod_windowSum_cycle f 0
  have hn := congrArg (fun length => CyclicWindows.windowSum f 1 length 0) hcount
  rw [hn, CyclicWindows.windowSum_of_zmod_period_multiple f r hp b 0,
    hsum, nsmul_eq_mul] at hw
  exact mul_left_cancel₀ (show (b : ℤ) ≠ 0 by omega) hw

end SkewCornerDescent.Matrix.SelectedCoordinate
