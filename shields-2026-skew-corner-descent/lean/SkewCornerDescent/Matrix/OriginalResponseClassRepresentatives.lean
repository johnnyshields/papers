/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClasses
import SkewCornerDescent.Matrix.RealResponseChart

/-!
# Faithful rational representatives of the actual finite response classes

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:dual-identities`).
Each representative comes from the full original response matrix at its literal
protected top. Equal-value classes are already merged; denominators and real
polynomial supports are supplied by original elimination. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The entire actual class family has monic rational representatives at its
produced original tops, with every lower denominator nonzero before specialization. -/
theorem originalResponseClasses_real_representatives {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ p q : c.OriginalResponseClass P → OtherPolynomial c.top,
      (∀ a j, j ∈ (realResiduePolynomial c.top (p a)).vars →
        j < (c.originalResponseClassTop P hB a : ℕ)) ∧
      (∀ a j, j ∈ (realResiduePolynomial c.top (q a)).vars → j < (c.top : ℕ)) ∧
      (∀ a, q a ≠ 0) ∧ (∀ a, realResiduePolynomial c.top (q a) ≠ 0) ∧
      ∀ a, a.val =
        residueGenerator c.top ⟨c.originalResponseClassTop P hB a,
          ne_of_gt (c.originalResponseClassTop_gt P hB a)⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (p a) /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) (q a) := by
  let idx := c.originalResponseClassIndex P
  let top := c.originalResponseClassTop P hB
  have htop : ∀ a, c.top < top a := c.originalResponseClassTop_gt P hB
  have hindices : ∀ a,
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (originalHessenbergRows P (idx a)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (originalHessenbergCols P (idx a)))) =
        (top a : ℤ) := fun a => (c.originalHessenbergTop_coe P hB (idx a) (idx a) le_rfl).symm
  obtain ⟨p, q, hp, hq, hq0, hqreal, he⟩ := c.originalResponses_real_representatives
    (fun _ => n) (fun _ => P) (fun a => originalHessenbergRows P (idx a))
    (fun a => originalHessenbergCols P (idx a)) top htop hindices (fun _ => hmax)
  refine ⟨p, q, hp, hq, hq0, hqreal, ?_⟩
  intro a
  have h := he a
  change c.regularResidue (c.originalHessenbergResponse P (idx a) (idx a)) = _ at h
  rw [c.originalResponseClassIndex_spec P a] at h
  exact h

end SkewCornerDescent.Matrix.SelectedCoordinate
