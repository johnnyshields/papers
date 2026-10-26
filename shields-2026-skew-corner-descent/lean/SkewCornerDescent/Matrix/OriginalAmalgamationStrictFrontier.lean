/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationMaximalGaps
import SkewCornerDescent.Matrix.OriginalStrictGapFrontier
import SkewCornerDescent.Matrix.OriginalAmalgamationSpan

/-!
# The full amalgamation germ at a strict maximal span

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Its own
complete literal end windows have the same period displacement as the source.
Actual union gap bounds exclude every first-fresh interval in a strict bin,
while complete removed-factor jets remain in the original Schur germ. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every ingredient of the strict-bin union coefficient is supplied from literal
source geometry; no union period or coefficient vanishing is assumed. -/
theorem originalAmalgamation_strict_normalized_log_zero {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u w : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate w W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : ℕ) (hj : 2 ≤ j)
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)
    (M : ℤ) (hstrict : q < M)
    (hbound : ∀ z : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun s => c.originalCompletedGap P ((ZMod.finEquiv _).symm s)) 1 j z ≤ M)
    (K : ℕ+) (hK : c.top < K) (hKeq : (K : ℤ) = (c.top : ℤ) + M) :
    let E := c.normalPolynomialSeries A.schur
    (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l E) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff (j - 1)
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff E)⁻¹ * E))) = 0 ∧
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      E (j - 1) := by
  have hinv := originalAmalgamation_selected_inventory (hD := hD) P W A q v u w
    hv hwindow hW hA
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  have hBA : 0 < originalSelectedCount (hD := hD) A := by omega
  let : NeZero (originalSelectedCount (hD := hD) A) := ⟨by omega⟩
  have hboundA := c.originalAmalgamation_completed_gap_bound P W A q v u w hq hv hwindow
    hW hA hcutq hcutLq hC j (by omega) hjlen M hstrict.le hbound
  have hmaxA := originalAmalgamation_component_span P W A q v u w hv hwindow hW hA
    (c.top : ℕ) hmax
  have ht := c.originalSchur_normalized_log_from_gap_bound A hBA hmaxA j hj (by omega)
    M hboundA K hK hKeq
  obtain ⟨hleft, hright⟩ := originalAmalgamation_complete_end_windows P A q v u
    hq hv hwindow hA
  have hlower : A.cells.filter (fun x => 0 ≤ content x ∧ content x < A.xi 0 - q) =
      translate (-u) P.cells := by
    apply translate_injective u
    rw [hleft, translate_translate, add_neg_cancel, translate_zero]
  have hupper : A.cells.filter (fun x => q ≤ content x ∧ content x < A.xi 0) =
      translate v (A.cells.filter fun x => 0 ≤ content x ∧ content x < A.xi 0 - q) := by
    apply translate_injective u
    rw [hright, translate_translate, add_comm u v, ← translate_translate, hleft]
  have hcuts := originalAmalgamation_private_end_cuts P A q v u
    hq hv hwindow hA hcutq hcutLq
  have hz := c.originalWindow_strict_filtered_inventory_zero A P q (-u) v hv hlower hupper
    (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.1)
    hBA j hj (by omega) (by omega) M hstrict hboundA K hKeq
  dsimp only at ht ⊢
  refine ⟨ht.1, ?_, ht.2.2⟩
  rw [ht.2.1, hz, mul_zero]

end SkewCornerDescent.Matrix.SelectedCoordinate
