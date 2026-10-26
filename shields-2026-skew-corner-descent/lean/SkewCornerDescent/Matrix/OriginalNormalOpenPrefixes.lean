/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalOpenPrefixTail
import SkewCornerDescent.Matrix.OriginalAmalgamationInternalMatrices
import SkewCornerDescent.Matrix.OriginalClosureInternalMatrices

/-!
# Actual three-word normal open charges reduce to genuine prefixes

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal full matrix copies cancel all five local charge tails in both actual
ordinary closure directions. No copied entry, inverse jet, or local charge
matching is assumed. These are the finite prefixes before cyclic simplification.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete actual weighted open charge comparison has only its two
finite prefix charges left. Both exterior overlapping-pair contributions survive. -/
theorem originalComparison_normal_open_prefixes {n m k qn : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (Q : Profile qn)
    (q : ℤ) (v u z w : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells ∨
      originalVerticalClosure P = translate w Q.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hsize : ℓ + 2 ≤ originalSelectedCount (hD := hD) P) :
    ∃ hAP : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      ∀ (δ : PowerSeries (OtherField c.top) → PowerSeries (OtherField c.top))
        (b γ : OtherField c.top) (a d : ℕ),
      let MA := (c.originalInternalResponseMatrix A).map c.normalSeries
      let MP := (c.originalInternalResponseMatrix P).map c.normalSeries
      let MQ := (c.originalInternalResponseMatrix Q).map c.normalSeries
      (a + d) • normalOpenOverlapCharge MA δ b γ (ℓ + 1) -
        a • normalOpenOverlapCharge MP δ b γ (ℓ + 1) -
        d • normalOpenOverlapCharge MQ δ b γ (ℓ + 1) =
      (a + d) • normalOpenOverlapPrefixCharge MA δ b γ ℓ
        (originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P) (by omega) -
        d • normalOpenOverlapPrefixCharge MQ δ b γ ℓ
          (originalSelectedCount (hD := hD) P) (by omega) := by
  obtain ⟨hAP, _, hcopyA⟩ := c.originalAmalgamation_lower_internal_matrix
    P W A q v u z hq hv hwindow hW hA hcutq hcutLq
  obtain ⟨hCQ, hcopyQ⟩ := c.originalClosure_lower_internal_matrix P Q w hQ
  refine ⟨hAP, hCQ, fun δ b γ a d => ?_⟩
  dsimp only
  have hAcharge := normalOpenOverlapCharge_copy_tail hℓ
    (N := originalSelectedCount (hD := hD) A - 1)
    (B := originalSelectedCount (hD := hD) P - 1)
    (T := originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P)
    (by omega) (by omega)
    ((c.originalInternalResponseMatrix A).map c.normalSeries)
    ((c.originalInternalResponseMatrix P).map c.normalSeries) hcopyA δ b γ
  have hQcharge := normalOpenOverlapCharge_copy_tail hℓ
    (N := originalSelectedCount (hD := hD) Q - 1)
    (B := originalSelectedCount (hD := hD) P - 1)
    (T := originalSelectedCount (hD := hD) P)
    (by omega) (by omega)
    ((c.originalInternalResponseMatrix Q).map c.normalSeries)
    ((c.originalInternalResponseMatrix P).map c.normalSeries) hcopyQ δ b γ
  rw [hAcharge, hQcharge]
  simp only [nsmul_add, add_nsmul]
  abel

end SkewCornerDescent.Matrix.SelectedCoordinate
