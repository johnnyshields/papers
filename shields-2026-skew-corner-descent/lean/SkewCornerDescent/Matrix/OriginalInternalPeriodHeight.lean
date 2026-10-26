/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalNormalFrontiers

/-!
# Exact original endpoint heights of complete internal period windows

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual selected endpoints and every positional gap give the full response span.
Periodic window summation supplies its precise period multiple, including the
selected-span offset. No endpoint-height or numeric gap floor is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A complete open-source period multiple has its exact original selected-to-selected
endpoint span. The selected-span offset is retained, not silently dropped. -/
theorem originalInternal_period_endpoint_height {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + d * r) :
    P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P i)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t)))) =
      (c.top : ℤ) + d • windowSum
        (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 := by
  have hdr : 0 < d * r := Nat.mul_pos hd hr
  let j : Fin (originalSelectedCount (hD := hD) P) := ⟨t.val - 1, by have := t.isLt; omega⟩
  have hij : i ≤ j := by change i.val ≤ t.val - 1; omega
  have hj : j.val + 1 < originalSelectedCount (hD := hD) P := by
    change t.val - 1 + 1 < originalSelectedCount (hD := hD) P
    have := t.isLt
    omega
  have hs := windowSum_finite_interval (c.originalCompletedGap P) i j hij
  have hlen : j.val - i.val + 1 = d * r := by change t.val - 1 - i.val + 1 = d * r; omega
  have hsum : (∑ k ∈ Finset.Icc i j, c.originalCompletedGap P k) =
      d • windowSum (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 := by
    rw [← hs, hlen]
    exact windowSum_of_zmod_period_multiple _ r hp d _
  have h := c.originalCompletedGap_internal_window P i j hij hj
  rw [hsum] at h
  have hjt : j.succ = t.castSucc := by
    apply Fin.ext
    change t.val - 1 + 1 = t.val
    omega
  rw [hjt] at h
  simpa only [originalHessenbergDistance, originalHessenbergRows_succ,
    originalHessenbergCols_castSucc] using h

/-- Every positive complete period multiple strictly exceeds the selected span.
The source supplies each actual gap's strict floor, including the splice position. -/
theorem originalInternal_period_total_gt_top {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    (c.top : ℤ) < d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 := by
  have h := windowSum_short_period_lt
    (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
    (c.top : ℕ) r d 0 hp (fun x => c.originalCompletedGap_gt_top P _)
    (Nat.mul_pos hd hr) 0
  simpa only [windowSum, Finset.range_zero, Finset.sum_empty, add_zero] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
