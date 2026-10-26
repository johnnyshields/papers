/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowEndpointProfiles
import SkewCornerDescent.Matrix.OriginalClosureHalfWindows
import SkewCornerDescent.Matrix.OriginalClosureOrderedResponses
import SkewCornerDescent.Matrix.OriginalVerticalOrderedResponses

/-!
# Both full endpoint polynomials in the actual closure copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`,
`lem:early-recovery`). Both actual ordinary closure directions have complete
literal source windows. Their full endpoint polynomials are transported
separately, with no deletion of the true crossing join.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both actual ordinary closures preserve each complete source endpoint
polynomial at its actual upper or lower selected ranks. -/
theorem originalClosure_endpoint_polynomials {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells) :
    ∃ hc : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      ∀ (upper : Bool) (i j : Fin (originalSelectedCount (hD := hD) P)),
      let s := if upper then 0 else originalSelectedCount (hD := hD) P
      let a := originalSelectedEnumeration (hD := hD) Q
        ⟨s + i.val, by have := i.isLt; dsimp only [s]; split <;> omega⟩
      let b := originalSelectedEnumeration (hD := hD) Q
        ⟨s + j.val, by have := j.isLt; dsimp only [s]; split <;> omega⟩
      c.originalResidueLeftEndpointPolynomial Q (some a) (some b) =
        c.originalResidueLeftEndpointPolynomial P
          (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P j)) ∧
      c.originalResidueRightEndpointPolynomial Q (some a) (some b) =
        c.originalResidueRightEndpointPolynomial P
          (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P j)) := by
  have hc : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P := by
    rcases hQ with hQ | hQ
    · exact originalHorizontalClosure_profile_selected_count P Q z hQ
    · exact originalVerticalClosure_profile_selected_count P Q z hQ
  have hdata : Q.xi 0 = 2 * P.xi 0 ∧
      (∀ x ∈ diagramInterior Q.cells, content x ≠ P.xi 0) ∧
      ∃ l u : ℤ × ℤ,
        P.cells = translate l (Q.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0) ∧
        P.cells = translate u
          (Q.cells.filter fun x => P.xi 0 ≤ content x ∧ content x < 2 * P.xi 0) := by
    rcases hQ with hQ | hQ
    · have htop := originalHorizontalClosure_xi_upper P Q z hQ 0
      have hzero : originalClosureUpperRow P Q z hQ 0 = 0 := Fin.ext rfl
      rw [hzero] at htop
      have hjoin : ∀ x ∈ diagramInterior Q.cells, content x ≠ P.xi 0 := by
        intro x hx he
        have hz := (originalHorizontalClosure_profile_rows P Q z hQ).2
        have hz0 : content z = 0 := by simp only [hz, content]; ring
        have hlift : x + z ∈ diagramInterior (originalHorizontalClosure P) := by
          rw [hQ, interior_translate]
          apply mem_translate.mpr
          simpa only [add_sub_cancel_right] using hx
        apply (originalHorizontalClosure_join_no_interior P).1 _ hlift
        rw [content_add, hz0, add_zero, he]
      refine ⟨by omega, hjoin, -((n : ℤ), (n : ℤ)), -(0, P.xi 0), ?_, ?_⟩
      · rw [originalHorizontalClosure_lower_window P Q z hQ,
          translate_translate, neg_add_cancel, translate_zero]
      · rw [originalHorizontalClosure_upper_window P Q z hQ,
          translate_translate, neg_add_cancel, translate_zero]
    · refine ⟨originalVerticalClosure_profile_top P Q z hQ,
        originalVerticalClosure_profile_join_no_interior P Q z hQ,
        z, z - (vH P.cells - eCell), ?_, ?_⟩
      · rw [originalVerticalClosure_lower_window P Q z hQ,
          translate_translate, add_neg_cancel, translate_zero]
      · rw [originalVerticalClosure_upper_window P Q z hQ, translate_translate,
          show z - (vH P.cells - eCell) + (vH P.cells - eCell - z) = 0 by abel,
          translate_zero]
  rcases hdata with ⟨htop, hjoin, l, u, hl, hu⟩
  have hmid : ∀ x ∈ diagramInterior Q.cells, content x ≠ Q.xi 0 - P.xi 0 := by
    rw [htop, show 2 * P.xi 0 - P.xi 0 = P.xi 0 by ring]
    exact hjoin
  have hlower : P.cells = translate l
      (Q.cells.filter fun x => 0 ≤ content x ∧ content x < Q.xi 0 - P.xi 0) := by
    rw [htop, show 2 * P.xi 0 - P.xi 0 = P.xi 0 by ring]
    exact hl
  have hupper : P.cells = translate u
      (Q.cells.filter fun x => P.xi 0 ≤ content x ∧ content x < Q.xi 0) := by
    rw [htop]
    exact hu
  obtain ⟨_, heL⟩ := c.originalWindow_lower_endpoint_polynomials Q P (P.xi 0) l hlower
    (originalProfile_interior_boundary_gaps Q).1 hmid
  obtain ⟨_, heU⟩ := c.originalWindow_upper_endpoint_polynomials Q P (P.xi 0) u hupper
    hjoin (originalProfile_interior_boundary_gaps Q).2
  have hshift : originalSelectedCount (hD := hD) Q - originalSelectedCount (hD := hD) P =
      originalSelectedCount (hD := hD) P := by omega
  refine ⟨hc, fun upper i j => ?_⟩
  cases upper with
  | false =>
    simpa only [Bool.false_eq_true, ite_false, hshift, Nat.add_comm] using
      And.intro (heL i j).1.symm (heL i j).2.symm
  | true =>
    simpa only [ite_true, zero_add] using
      And.intro (heU i j).1.symm (heU i j).2.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
