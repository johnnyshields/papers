/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.CopiedMatrixWordPeriods
import SkewCornerDescent.Matrix.OriginalAmalgamationEndpointProfiles
import SkewCornerDescent.Matrix.OriginalClosureEndpointProfiles

/-!
# Complete residue endpoint-polynomial words from literal copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`,
`lem:early-recovery`). Both endpoint polynomials retain all powers of their
profile variable and every original residue inverse coupling. Their adjacent
selected-pair words use the canonical finite overlap periods, retaining the
actual central closure profile rather than a wrapped column-zero substitute.
These are residue profile polynomials, not substituted normal germs.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The two full residue endpoint polynomials at consecutive actual selected
occurrences have their genuine amalgamation-overlap word period. -/
theorem originalAmalgamation_profile_word_period {n m : ℕ}
    (P : Profile n) (A : Profile m) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    (originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A) ∧
      let T := originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P
      let N := originalSelectedCount (hD := hD) A - 1
      let E := originalSelectedEnumeration (hD := hD) A
      let profileWord := fun i : Fin N =>
        let a : Fin (originalSelectedCount (hD := hD) A) := ⟨i.val, by have := i.isLt; omega⟩
        let b : Fin (originalSelectedCount (hD := hD) A) := ⟨i.val + 1, by have := i.isLt; omega⟩
        (c.originalResidueLeftEndpointPolynomial A (some (E a)) (some (E b)),
          c.originalResidueRightEndpointPolynomial A (some (E a)) (some (E b)))
      ∀ i j : Fin N, j.val = i.val + T → profileWord i = profileWord j := by
  obtain ⟨hc, he⟩ := c.originalAmalgamation_endpoint_polynomials
    P A q v u hq hv hwindow hA hcutq hcutLq
  let T := originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P
  let MA : Matrix (Fin (originalSelectedCount (hD := hD) A))
      (Fin (originalSelectedCount (hD := hD) A))
      (Polynomial (OtherField c.top) × Polynomial (OtherField c.top)) := fun i j =>
    (c.originalResidueLeftEndpointPolynomial A
      (some (originalSelectedEnumeration A i)) (some (originalSelectedEnumeration A j)),
      c.originalResidueRightEndpointPolynomial A
      (some (originalSelectedEnumeration A i)) (some (originalSelectedEnumeration A j)))
  let MP : Matrix (Fin (originalSelectedCount (hD := hD) P))
      (Fin (originalSelectedCount (hD := hD) P))
      (Polynomial (OtherField c.top) × Polynomial (OtherField c.top)) := fun i j =>
    (c.originalResidueLeftEndpointPolynomial P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P j)),
      c.originalResidueRightEndpointPolynomial P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P j)))
  have hu : ∀ i j : Fin (originalSelectedCount (hD := hD) P),
      MA ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ = MP i j := by
    intro i j
    apply Prod.ext
    · simpa only [MA, MP, ite_true, zero_add] using (he true i j).1
    · simpa only [MA, MP, ite_true, zero_add] using (he true i j).2
  have hl : ∀ i j : Fin (originalSelectedCount (hD := hD) P),
      MA ⟨T + i.val, by have := i.isLt; omega⟩
        ⟨T + j.val, by have := j.isLt; omega⟩ = MP i j := by
    intro i j
    apply Prod.ext
    · simpa only [MA, MP, T, Bool.false_eq_true, ite_false] using (he false i j).1
    · simpa only [MA, MP, T, Bool.false_eq_true, ite_false] using (he false i j).2
  have hp := (copied_matrix_word_periods
    (N := originalSelectedCount (hD := hD) A) (B := originalSelectedCount (hD := hD) P)
    (T := T) (by omega) MA MP hu hl).2
  exact ⟨hc, hp⟩

/-- The two full residue endpoint polynomials at consecutive actual selected
occurrences have their genuine complete-source word period. -/
theorem originalClosure_profile_word_period {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells) :
    (originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P) ∧
      let T := originalSelectedCount (hD := hD) P
      let N := originalSelectedCount (hD := hD) Q - 1
      let E := originalSelectedEnumeration (hD := hD) Q
      let profileWord := fun i : Fin N =>
        let a : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val, by have := i.isLt; omega⟩
        let b : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val + 1, by have := i.isLt; omega⟩
        (c.originalResidueLeftEndpointPolynomial Q (some (E a)) (some (E b)),
          c.originalResidueRightEndpointPolynomial Q (some (E a)) (some (E b)))
      ∀ i j : Fin N, j.val = i.val + T → profileWord i = profileWord j := by
  obtain ⟨hc, he⟩ := c.originalClosure_endpoint_polynomials P Q z hQ
  let MQ : Matrix (Fin (originalSelectedCount (hD := hD) Q))
      (Fin (originalSelectedCount (hD := hD) Q))
      (Polynomial (OtherField c.top) × Polynomial (OtherField c.top)) := fun i j =>
    (c.originalResidueLeftEndpointPolynomial Q
      (some (originalSelectedEnumeration Q i)) (some (originalSelectedEnumeration Q j)),
      c.originalResidueRightEndpointPolynomial Q
      (some (originalSelectedEnumeration Q i)) (some (originalSelectedEnumeration Q j)))
  let MP : Matrix (Fin (originalSelectedCount (hD := hD) P))
      (Fin (originalSelectedCount (hD := hD) P))
      (Polynomial (OtherField c.top) × Polynomial (OtherField c.top)) := fun i j =>
    (c.originalResidueLeftEndpointPolynomial P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P j)),
      c.originalResidueRightEndpointPolynomial P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P j)))
  have hu : ∀ i j : Fin (originalSelectedCount (hD := hD) P),
      MQ ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ = MP i j := by
    intro i j
    apply Prod.ext
    · simpa only [MQ, MP, ite_true, zero_add] using (he true i j).1
    · simpa only [MQ, MP, ite_true, zero_add] using (he true i j).2
  have hl : ∀ i j : Fin (originalSelectedCount (hD := hD) P),
      MQ ⟨(originalSelectedCount (hD := hD) P) + i.val, by have := i.isLt; omega⟩
        ⟨(originalSelectedCount (hD := hD) P) + j.val, by have := j.isLt; omega⟩ = MP i j := by
    intro i j
    apply Prod.ext
    · simpa only [MQ, MP, Bool.false_eq_true, ite_false] using (he false i j).1
    · simpa only [MQ, MP, Bool.false_eq_true, ite_false] using (he false i j).2
  have hp := (copied_matrix_word_periods
    (N := originalSelectedCount (hD := hD) Q) (B := originalSelectedCount (hD := hD) P)
    (T := originalSelectedCount (hD := hD) P) (by omega) MQ MP hu hl).2
  exact ⟨hc, hp⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
