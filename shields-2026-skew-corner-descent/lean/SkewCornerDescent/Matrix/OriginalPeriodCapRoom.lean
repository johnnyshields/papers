/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalCyclicGapBounds

/-!
# Actual ordinary caps leave a complete root-period margin

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact completed gap period sums to the root span. Every actual gap
is positive and exceeds the selected span, so the true cap-splice gap
is at most one root span. With at least three outer copies, both genuine
cap widths plus one root period fit strictly inside the source span.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual completed period supplies root-span positivity and strict
room beyond both true caps and one whole period. -/
theorem originalCompleted_true_cap_room {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (b r : ℕ) (hb : 3 ≤ b) (δ : ℤ)
    (hcount : originalSelectedCount (hD := hD) P = b * r)
    (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * δ)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    (c.top : ℤ) < δ ∧
      originalHessenbergDistance (hD := hD) P 0 0 < δ ∧
      originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) < δ ∧
      originalHessenbergDistance (hD := hD) P 0 0 +
          originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) + δ <
        P.xi 0 - P.zeta (Fin.last n) := by
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hr : 0 < r := by
    by_contra hn
    have hz : r = 0 := by omega
    rw [hz, mul_zero] at hcount
    omega
  let f := fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)
  let last : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  let i := ZMod.finEquiv (originalSelectedCount (hD := hD) P) last
  have hN : 0 < (c.top : ℤ) := by exact_mod_cast c.top.pos
  have hnonneg (z) : 0 ≤ f z := by
    have hh := c.originalCompletedGap_gt_top P ((ZMod.finEquiv _).symm z)
    change (c.top : ℤ) < f z at hh
    omega
  have hsum := c.originalCompletedGap_period_sum P hB r b (by omega) δ hcount hspan hp
  change windowSum f 1 r 0 = δ at hsum
  have hat : windowSum f 1 r i = δ := (windowSum_of_zmod_period f r hp i).trans hsum
  have hsingle : f i ≤ windowSum f 1 r i := by
    unfold windowSum
    have h0 : (0 : ℕ) ∈ Finset.range r := by simpa only [Finset.mem_range] using hr
    have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.range r) => hnonneg (i+k•1)) h0
    simpa only [zero_nsmul, add_zero] using hh
  have hfi : f i = c.originalCompletedGap P last := by
    simp only [f, i, RingEquiv.symm_apply_apply]
  have hlast : c.originalCompletedGap P last ≤ δ := by rw [← hfi, ← hat]; exact hsingle
  have hgt := c.originalCompletedGap_gt_top P last
  have hdelta : (c.top : ℤ) < δ := hgt.trans_le hlast
  have hδpos : 0 < δ := by omega
  have hcap : c.originalCompletedGap P last =
      originalHessenbergDistance (hD := hD) P 0 0 +
        originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) - (c.top : ℤ) := by
    rw [originalCompletedGap, ite_eq_left (by dsimp only [last]; omega)]
  have hleft := c.originalHessenbergDistance_gt_top P hB 0 0 le_rfl
  have hright := c.originalHessenbergDistance_gt_top P hB (Fin.last _) (Fin.last _) le_rfl
  have hbInt : (3 : ℤ) ≤ b := by exact_mod_cast hb
  have hm := mul_le_mul_of_nonneg_right hbInt hδpos.le
  refine ⟨hdelta, by omega, by omega, ?_⟩
  rw [hspan]
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
