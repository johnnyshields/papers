/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalOrdinaryMiddleBand
import SkewCornerDescent.Matrix.OriginalPeriodCapRoom
import SkewCornerDescent.Matrix.OriginalContentPeriodForward
import SkewCornerDescent.Matrix.OriginalContentPeriodBackward
import SkewCornerDescent.MiddleBandWindowTransfer

/-!
# Complete original source windows from the actual ordinary strip period

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual cap-period bound supplies a full period of room in the genuine
doubled closure. Every complete source cell is lifted into one of its two
literal ordinary copies, translated inside the actual middle band, and
projected back through that same complete copy. Both ordinary directions
and every original row and column remain. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual ordinary middle-band period and produced true-cap room
identify the complete original translated source windows. -/
theorem originalOrdinaryClosure_full_windows_of_strip_period {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) Q)]
    (b r : ℕ) (hb : 3 ≤ b) [NeZero r]
    (hcount : originalSelectedCount (hD := hD) P = b * r)
    (δ : ℤ) (hδ : 0 < δ) (hspan : P.xi 0 = (b : ℤ) * δ)
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (v : ℤ × ℤ) (hv : content v = -δ)
    (hstrips : ∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1), j.val = i.val+r →
      translate v (originalInternalParentStrip Q i) = originalInternalParentStrip Q j)
    (hselected : ∀ a b : Fin (originalSelectedCount (hD := hD) Q), b.val = a.val+r →
      originalSelectedSourceBeta Q b - originalSelectedSourceBeta Q a = content v) :
    P.cells.filter (fun x => δ ≤ content x ∧ content x < P.xi 0) =
      translate (-v) (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0-δ) := by
  have hP := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hCQ := originalOrdinaryClosure_selected_count (hD := hD) P Q z hQ
  have hQtwo : 2 ≤ originalSelectedCount (hD := hD) Q := by omega
  have hb1 : 1 ≤ b := by omega
  have hm := Nat.mul_le_mul_right r hb1
  simp only [one_mul] at hm
  have hrQ : r < originalSelectedCount (hD := hD) Q := by omega
  have hcoords := originalOrdinaryClosure_middle_betas (hD := hD) P Q z hQ
  have hcaps := c.originalCompleted_true_cap_room P b r hb δ hcount
    (by simpa only [P.zeta_last, sub_zero] using hspan) hgap
  have hleft := c.originalHessenbergDistance_gt_top P hP 0 0 le_rfl
  have hright := c.originalHessenbergDistance_gt_top P hP (Fin.last _) (Fin.last _) le_rfl
  have hN : 0 < (c.top : ℤ) := by exact_mod_cast c.top.pos
  let lo := originalSelectedMiddleLowerBeta (hD := hD) Q
  let hi := originalSelectedMiddleUpperBeta (hD := hD) Q
  have hnonneg : 0 ≤ lo := by
    dsimp only [lo]
    rw [hcoords.1]
    omega
  have hsmall : lo+δ < P.xi 0 := by
    dsimp only [lo]
    rw [hcoords.1]
    have hh := hcaps.2.2.2
    rw [P.zeta_last, sub_zero] at hh
    omega
  have hroom : P.xi 0+lo+δ < hi := by
    dsimp only [lo,hi]
    rw [hcoords.1, hcoords.2]
    have hh := hcaps.2.2.2
    rw [P.zeta_last, sub_zero] at hh
    omega
  obtain ⟨a,t,ha,ht,hlower,hupper⟩ : ∃ a t : ℤ × ℤ, content a = 0 ∧ content t = P.xi 0 ∧
      Q.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0) = translate a P.cells ∧
      Q.cells.filter (fun x => P.xi 0 ≤ content x ∧ content x < 2*P.xi 0) =
        translate t P.cells := by
    rcases hQ with hH | hV
    · refine ⟨((pn : ℤ),(pn : ℤ)), (0,P.xi 0), ?_, ?_,
        originalHorizontalClosure_lower_window P Q z hH,
        originalHorizontalClosure_upper_window P Q z hH⟩
      · dsimp only [content]; omega
      · dsimp only [content]; omega
    · have hz := originalVerticalClosure_profile_content P Q z hV
      refine ⟨-z, vH P.cells-eCell-z, ?_, ?_,
        originalVerticalClosure_lower_window P Q z hV,
        originalVerticalClosure_upper_window P Q z hV⟩
      · change -z.2 - -z.1 = 0
        change z.2-z.1 = 0 at hz
        omega
      · rw [MarkedInner.content_sub, originalVerticalDisplacement_content, hz, sub_zero]
  apply twoCopy_middle_period_full_windows P.cells Q.cells (P.xi 0) δ lo hi a t v
    hδ hnonneg hsmall hroom ha ht hv hlower hupper
  · intro x hx hlow hhigh
    exact originalMiddleBand_forward_period Q hQtwo r hrQ δ hδ v hv
      hstrips hselected x hx hlow hhigh
  · intro x hx hlow hhigh
    exact originalMiddleBand_backward_period Q hQtwo r hrQ δ hδ v hv
      hstrips hselected x hx hlow hhigh

end SkewCornerDescent.Matrix.SelectedCoordinate
