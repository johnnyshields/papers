/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowEndpointProfiles
import SkewCornerDescent.Matrix.OriginalAmalgamationWindows

/-!
# Full endpoint polynomials in both actual amalgamation copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`,
`lem:early-recovery`). Complete literal windows transport both individual
endpoint polynomials at every ordered selected pair, with the actual rank shift.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Each whole source copy in the actual amalgamation preserves its two full
endpoint polynomials separately, not merely the resulting scalar response. -/
theorem originalAmalgamation_endpoint_polynomials {n m : ℕ}
    (P : Profile n) (A : Profile m) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hc : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
      ∀ (upper : Bool) (i j : Fin (originalSelectedCount (hD := hD) P)),
      let s := if upper then 0 else originalSelectedCount (hD := hD) A -
        originalSelectedCount (hD := hD) P
      let a := originalSelectedEnumeration (hD := hD) A
        ⟨s + i.val, by have := i.isLt; dsimp only [s]; split <;> omega⟩
      let b := originalSelectedEnumeration (hD := hD) A
        ⟨s + j.val, by have := j.isLt; dsimp only [s]; split <;> omega⟩
      c.originalResidueLeftEndpointPolynomial A (some a) (some b) =
        c.originalResidueLeftEndpointPolynomial P
          (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P j)) ∧
      c.originalResidueRightEndpointPolynomial A (some a) (some b) =
        c.originalResidueRightEndpointPolynomial P
          (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P j)) := by
  have hcuts := originalAmalgamation_private_end_cuts P A q v u hq hv hwindow hA hcutq hcutLq
  obtain ⟨hleft, hright⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  have hupper : P.cells = translate (u - v)
      (A.cells.filter fun x => q ≤ content x ∧ content x < A.xi 0) := by
    apply translate_injective v
    rw [translate_translate, show v + (u - v) = u by abel]
    exact hright.symm
  obtain ⟨hc, heL⟩ := c.originalWindow_lower_endpoint_polynomials A P q u hleft.symm
    (fun x hx => (hcuts x hx).1) (fun x hx => (hcuts x hx).2.2.1)
  obtain ⟨_, heU⟩ := c.originalWindow_upper_endpoint_polynomials A P q (u - v) hupper
    (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.2)
  refine ⟨hc, fun upper i j => ?_⟩
  cases upper with
  | false =>
    simpa only [Bool.false_eq_true, ite_false, Nat.add_comm] using
      And.intro (heL i j).1.symm (heL i j).2.symm
  | true =>
    simpa only [ite_true, zero_add] using
      And.intro (heU i j).1.symm (heU i j).2.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
