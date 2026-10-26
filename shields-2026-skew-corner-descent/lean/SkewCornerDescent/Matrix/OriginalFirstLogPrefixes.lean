/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalOpenPrefixComparison
import SkewCornerDescent.Matrix.OriginalComparisonMatrixWindows
import SkewCornerDescent.Matrix.OriginalInternalFirstLogWindows
import SkewCornerDescent.Matrix.NormalFirstPrefixCharge

/-!
# Complete actual first logarithm reduces to its two prefix charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Both the onsite and adjacent-pair parts of the whole first normal coefficient
are transported by actual literal matrix copies, in both closure directions.
No partition-only first coefficient replaces the full first logarithm.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Full first-normal matrix jets and pair entries cancel on the literal copied
tails. The remaining two actual prefixes retain both parts of the first coefficient. -/
theorem originalComparison_first_log_prefixes {n m k qn : ℕ}
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
    (hP2 : 2 ≤ originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ hAP : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      ∀ a d : ℕ,
      let wordLog : {k : ℕ} → Profile k → PowerSeries (OtherField c.top) := fun X =>
        let M := (c.originalInternalResponseMatrix X).map c.normalSeries
        PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det)
      PowerSeries.coeff 1 ((a + d) • wordLog A - a • wordLog P - d • wordLog Q) =
        (a + d) • normalFirstPrefixCharge
          ((c.originalInternalResponseMatrix A).map c.normalSeries) c.normalCoefficient⁻¹
          (originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P) (by omega) -
        d • normalFirstPrefixCharge
          ((c.originalInternalResponseMatrix Q).map c.normalSeries) c.normalCoefficient⁻¹
          (originalSelectedCount (hD := hD) P) (by omega) := by
  obtain ⟨hAP, hCQ, hall⟩ := c.originalComparison_matrix_window_cancellation
    P W A Q q v u z w hq hv hwindow hW hA hQ hcutq hcutLq (by omega)
  refine ⟨hAP, hCQ, fun a d => ?_⟩
  let onsite := fun V : Matrix (Fin 1) (Fin 1) (PowerSeries (OtherField c.top)) =>
    PowerSeries.coeff 1 (V 0 0) * (PowerSeries.constantCoeff (V 0 0))⁻¹
  let pair := fun V : Matrix (Fin 2) (Fin 2) (PowerSeries (OtherField c.top)) =>
    PowerSeries.constantCoeff (V 0 (Fin.last 1)) *
      ∏ k, (PowerSeries.constantCoeff (V k k))⁻¹
  let wordLog : {k : ℕ} → Profile k → PowerSeries (OtherField c.top) := fun X =>
    let M := (c.originalInternalResponseMatrix X).map c.normalSeries
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det)
  have hon := hall 1 (by omega) (OtherField c.top) onsite a d
  have hpair := hall 2 (by omega) (OtherField c.top) pair a d
  have hmaxA : ∀ C ∈ edgeComponents (diagramInterior A.cells), span C ≤ (c.top : ℕ) :=
    originalAmalgamation_component_span P W A q v u z hv hwindow hW hA _ hmax
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_profile_component_span P Q w hQ hmax
    · exact c.originalVerticalClosure_profile_component_span P Q w hQ hmax
  have hlA := c.originalInternal_first_log_windows A (by omega) hmaxA
  have hlP := c.originalInternal_first_log_windows P hP2 hmax
  have hlQ := c.originalInternal_first_log_windows Q (by omega) hmaxQ
  change PowerSeries.coeff 1 (wordLog A) =
    (∑ s, onsite (contiguousMatrixWindow
      ((c.originalInternalResponseMatrix A).map c.normalSeries) 1 s)) -
    c.normalCoefficient⁻¹ * (∑ s, pair (contiguousMatrixWindow
      ((c.originalInternalResponseMatrix A).map c.normalSeries) 2 s)) at hlA
  change PowerSeries.coeff 1 (wordLog P) =
    (∑ s, onsite (contiguousMatrixWindow
      ((c.originalInternalResponseMatrix P).map c.normalSeries) 1 s)) -
    c.normalCoefficient⁻¹ * (∑ s, pair (contiguousMatrixWindow
      ((c.originalInternalResponseMatrix P).map c.normalSeries) 2 s)) at hlP
  change PowerSeries.coeff 1 (wordLog Q) =
    (∑ s, onsite (contiguousMatrixWindow
      ((c.originalInternalResponseMatrix Q).map c.normalSeries) 1 s)) -
    c.normalCoefficient⁻¹ * (∑ s, pair (contiguousMatrixWindow
      ((c.originalInternalResponseMatrix Q).map c.normalSeries) 2 s)) at hlQ
  change PowerSeries.coeff 1 ((a + d) • wordLog A - a • wordLog P - d • wordLog Q) = _
  simp only [map_sub, map_nsmul, hlA, hlP, hlQ]
  dsimp only [normalFirstPrefixCharge]
  dsimp only [onsite, pair] at hon hpair
  simp only [nsmul_eq_mul] at hon hpair ⊢
  linear_combination hon - c.normalCoefficient⁻¹ * hpair

end SkewCornerDescent.Matrix.SelectedCoordinate
