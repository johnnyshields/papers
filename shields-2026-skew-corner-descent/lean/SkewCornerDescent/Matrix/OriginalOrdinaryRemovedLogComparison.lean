/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRemovedLogComparison
import SkewCornerDescent.Matrix.OriginalOrdinaryRemovedBalance
import SkewCornerDescent.Matrix.OriginalAmalgamationInternalMatrices
import SkewCornerDescent.Matrix.OriginalClosureInternalMatrices
import SkewCornerDescent.Matrix.OriginalAmalgamationSpan

/-!
# Closed complete original Schur logarithm comparison in both ordinary directions

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal whole diagrams and original corner powers produce the exact removed
power balance and every normal determinant unit. All removed logarithms cancel
at every normal order, including the full first jet; no removed-factor match
is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Original corner powers and actual ordinary closure geometry transfer the
whole weighted original Schur logarithm to the whole retained logarithm. Every
removed-factor balance and regularity supplier is invoked inside the proof. -/
theorem originalOrdinary_normal_log_comparison {n m k qn : ℕ}
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
    (Λ : Lambda) (b a d : ℕ) (hab : a ≤ b) (hd : d + a = b)
    (hKP : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin k => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (hP : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let logNorm := fun p : PowerSeries (OtherField c.top) =>
      PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)
    b • logNorm (c.normalPolynomialSeries A.schur) -
      a • logNorm (c.normalPolynomialSeries P.schur) -
      d • logNorm (c.normalPolynomialSeries Q.schur) =
    b • logNorm (c.normalSeries (c.originalHessenbergResponse A).det) -
      a • logNorm (c.normalSeries (c.originalHessenbergResponse P).det) -
      d • logNorm (c.normalSeries (c.originalHessenbergResponse Q).det) := by
  obtain ⟨hAP, _, _⟩ := c.originalAmalgamation_lower_internal_matrix
    P W A q v u z hq hv hwindow hW hA hcutq hcutLq
  obtain ⟨hCQ, _⟩ := c.originalClosure_lower_internal_matrix P Q w hQ
  have hmaxA : ∀ C ∈ edgeComponents (diagramInterior A.cells), span C ≤ (c.top : ℕ) :=
    originalAmalgamation_component_span P W A q v u z hv hwindow hW hA _ hmax
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_profile_component_span P Q w hQ hmax
    · exact c.originalVerticalClosure_profile_component_span P Q w hQ hmax
  have hremoved := originalOrdinary_removed_power_balance (hD := hD)
    P W A Q q v u z w hv hwindow hW hA hQ Λ b a d hab hd hKP hKW
  exact c.original_normal_log_comparison_of_removed_balance P A Q b a d
    hP (by omega) (by omega) hmax hmaxA hmaxQ hremoved

end SkewCornerDescent.Matrix.SelectedCoordinate
