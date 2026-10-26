/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationEndpointProfiles
import SkewCornerDescent.Matrix.OriginalInternalLongEntryGradient
import SkewCornerDescent.Matrix.OriginalTranslatedGaps

/-!
# Actual amalgamation prefix gradients are complete self-profile products

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Each long prefix entry starts in the upper literal source copy and ends in the
lower copy at the same source rank. Both full endpoint polynomials are copied.
The completed gap period is supplied by
`originalCompleted_amalgamation_gap_period_data`; the rank offset follows from
the actual selected inventory and original corner powers.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A genuine long prefix response in the actual amalgamation has the source
self-profile gradient, with the full source local height and Laurent convention.
Only the completed-gap period and its count-derived rank offset are intermediate
premises; no endpoint profile, entry gradient, or inverse match is assumed. -/
theorem originalAmalgamation_prefix_long_self_gradient {n m : ℕ}
    (P : Profile n) (A : Profile m) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    [NeZero (originalSelectedCount (hD := hD) A)]
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap A ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) A)))
    (hshift : originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P = d * r)
    (hshort : d * r < originalSelectedCount (hD := hD) P)
    (i : Fin (d * r)) (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap A ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex A r d hn hp J H hH
    ∃ hAP : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
      let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
      let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by have := i.isLt; omega⟩
      let E := originalSelectedEnumeration (hD := hD) P
      residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
        (c.regularResidue (c.originalInternalResponseMatrix A
          ⟨i.val, by have := i.isLt; omega⟩
          ⟨i.val + d * r, by have := i.isLt; omega⟩)) =
        ((c.originalResidueLeftEndpointPolynomial P (some (E a)) (some (E b)) *
          c.originalResidueRightEndpointPolynomial P (some (E a)) (some (E b))).toLaurent).coeff
          (originalHessenbergDistance (hD := hD) P a.succ a.succ - (J : ℤ)) := by
  obtain ⟨hAP, he⟩ := c.originalAmalgamation_endpoint_polynomials P A q v u hq hv
    hwindow hA hcutq hcutLq
  refine ⟨hAP, ?_⟩
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by have := i.isLt; omega⟩
  let x : Fin (originalSelectedCount (hD := hD) A - 1) := ⟨i.val, by have := i.isLt; omega⟩
  let y : Fin (originalSelectedCount (hD := hD) A - 1) :=
    ⟨i.val + d * r, by have := i.isLt; omega⟩
  have hleft := (he true a b).1
  have hright := (he false a b).2
  simp only [ite_true, zero_add] at hleft
  simp only [Bool.false_eq_true, ite_false, hshift] at hright
  have hg := c.originalInternal_long_entry_local_gradient A r d hn hp x y
    (by rfl) J H hH
  dsimp only at hg ⊢
  change residueGeneratorDeriv c.top _
    (c.regularResidue (c.originalInternalResponseMatrix A x y)) = _
  rw [hg]
  have hcopyleft : c.originalResidueLeftEndpointPolynomial A
      (some (originalSelectedEnumeration A ⟨x.val, by have := x.isLt; omega⟩))
      (some (originalSelectedEnumeration A ⟨x.val + 1, by have := x.isLt; omega⟩)) =
      c.originalResidueLeftEndpointPolynomial P
        (some (originalSelectedEnumeration P a)) (some (originalSelectedEnumeration P b)) := hleft
  have hcopyright : c.originalResidueRightEndpointPolynomial A
      (some (originalSelectedEnumeration A ⟨y.val, by have := y.isLt; omega⟩))
      (some (originalSelectedEnumeration A ⟨y.val + 1, by have := y.isLt; omega⟩)) =
      c.originalResidueRightEndpointPolynomial P
        (some (originalSelectedEnumeration P a)) (some (originalSelectedEnumeration P b)) := by
    simpa only [a, b, y, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hright
  rw [hcopyleft, hcopyright]
  have hcuts := originalAmalgamation_private_end_cuts P A q v u hq hv hwindow hA hcutq hcutLq
  have hwin := (originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA).2
  have hupper : P.cells = translate (u - v)
      (A.cells.filter fun z => q ≤ content z ∧ content z < A.xi 0) := by
    apply translate_injective v
    rw [translate_translate, show v + (u - v) = u by abel]
    exact hwin.symm
  obtain ⟨j, hj, hdist⟩ := c.originalWindow_upper_internal_distance A P q (u - v) hupper
    (fun z hz => (hcuts z hz).2.1) (fun z hz => (hcuts z hz).2.2.2)
    ⟨i.val, by have := i.isLt; omega⟩
  have hjx : j = ⟨x.val, by have := x.isLt; omega⟩ := Fin.ext hj
  rw [hjx] at hdist
  have hcol : (⟨x.val, by have := x.isLt; omega⟩ :
      Fin (originalSelectedCount (hD := hD) A)).succ =
      (⟨x.val + 1, by have := x.isLt; omega⟩ :
        Fin (originalSelectedCount (hD := hD) A)).castSucc := Fin.ext rfl
  have hheight : A.xi (originalRowSplitEquiv A (.inl
      (some (originalSelectedEnumeration A ⟨x.val, by have := x.isLt; omega⟩)))) -
      A.zeta (originalColSplitEquiv A (.inl
      (some (originalSelectedEnumeration A ⟨x.val + 1, by have := x.isLt; omega⟩)))) =
      originalHessenbergDistance (hD := hD) P a.succ a.succ := by
    rw [hdist]
    unfold originalHessenbergDistance
    rw [originalHessenbergRows_succ, hcol, originalHessenbergCols_castSucc]
  rw [hheight]

end SkewCornerDescent.Matrix.SelectedCoordinate
