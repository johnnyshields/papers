/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalCapSplit
import SkewCornerDescent.Matrix.OriginalAmalgamationEndLogLocality
import SkewCornerDescent.Matrix.OriginalVerticalComparisonEndLogs

/-!
# Complete original comparison logarithms reduce to their internal determinants

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal end windows produce the selected-count bounds and full cap cancellation.
The actual three determinants then reduce to their complete internal logarithms
below the source selected cost, with no boundary coefficient premise supplied.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

private theorem union_selected_count_ge {n m : ℕ} (P : Profile n) (A : Profile m)
    (q : ℤ) (shift u : ℤ × ℤ) (hq : 0 ≤ q) (hv : content shift = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate shift (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate shift P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A := by
  have hcuts := originalAmalgamation_private_end_cuts P A q shift u hq hv hwindow hA
    hcutq hcutLq
  obtain ⟨_, hright⟩ := originalAmalgamation_complete_end_windows P A q shift u hq hv hwindow hA
  have hupper : P.cells = translate (u - shift)
      (A.cells.filter fun x => q ≤ content x ∧ content x < A.xi 0) := by
    apply translate_injective shift
    rw [translate_translate]
    have he : shift + (u - shift) = u := by abel
    rw [he]
    exact hright.symm
  exact originalLiteralWindow_selected_count_le A P q (A.xi 0) (u - shift) hupper
    (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.2)

/-- The actual horizontal comparison has no remaining endpoint logarithm below
its source selected cost. All three internal determinants remain complete. -/
theorem originalHorizontalComparison_internal_log_balance {n m w h : ℕ}
    (P : Profile n) (W : Profile w) (A : Profile m) (H : Profile h)
    (q : ℤ) (shift u z l : ℤ × ℤ) (hq : 0 ≤ q) (hv : content shift = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate shift (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate shift P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate l H.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (b a d : ℕ) (hd : d + a = b) (k : ℕ)
    (hk : k < originalSelectedCount (hD := hD) P) :
    let full := fun {s : ℕ} (X : Profile s) =>
      let p := c.normalSeries (c.originalHessenbergResponse X).det
      PowerSeries.coeff k (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))
    let mid := fun {s : ℕ} (X : Profile s) =>
      let p := c.normalSeries (c.originalInternalResponseMatrix X).det
      PowerSeries.coeff k (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))
    (b : OtherField c.top) * full A - (a : OtherField c.top) * full P -
        (d : OtherField c.top) * full H =
      (b : OtherField c.top) * mid A - (a : OtherField c.top) * mid P -
        (d : OtherField c.top) * mid H := by
  have hmaxA := originalAmalgamation_component_span P W A q shift u z hv hwindow hW hA _ hmax
  have hmaxH := c.originalHorizontalClosure_profile_component_span P H l hH hmax
  have hAP := union_selected_count_ge (hD := hD) P A q shift u hq hv hwindow hA hcutq hcutLq
  have hHP := originalHorizontalClosure_profile_selected_count (hD := hD) P H l hH
  have hAl := c.original_normal_log_internal_caps A hmaxA k (hk.trans_le hAP)
  have hPl := c.original_normal_log_internal_caps P hmax k hk
  have hHl := c.original_normal_log_internal_caps H hmaxH k (by omega)
  obtain ⟨hleft, hright⟩ := c.originalHorizontalComparison_end_log_balance P W A H
    q shift u z l hq hv hwindow hW hA hH hcutq hcutLq hmax b a d hd k hk
  dsimp only at hAl hPl hHl hleft hright ⊢
  linear_combination (b : OtherField c.top) * hAl - (a : OtherField c.top) * hPl -
    (d : OtherField c.top) * hHl + hleft + hright

/-- The actual vertical closure, including its extra central unit vertex, has
the same complete internal logarithmic reduction. No horizontal surrogate is used. -/
theorem originalVerticalComparison_internal_log_balance {n m w h : ℕ}
    (P : Profile n) (W : Profile w) (A : Profile m) (V : Profile h)
    (q : ℤ) (shift u z l : ℤ × ℤ) (hq : 0 ≤ q) (hv : content shift = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate shift (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate shift P.cells = translate u A.cells)
    (hV : originalVerticalClosure P = translate l V.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (b a d : ℕ) (hd : d + a = b) (k : ℕ)
    (hk : k < originalSelectedCount (hD := hD) P) :
    let full := fun {s : ℕ} (X : Profile s) =>
      let p := c.normalSeries (c.originalHessenbergResponse X).det
      PowerSeries.coeff k (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))
    let mid := fun {s : ℕ} (X : Profile s) =>
      let p := c.normalSeries (c.originalInternalResponseMatrix X).det
      PowerSeries.coeff k (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))
    (b : OtherField c.top) * full A - (a : OtherField c.top) * full P -
        (d : OtherField c.top) * full V =
      (b : OtherField c.top) * mid A - (a : OtherField c.top) * mid P -
        (d : OtherField c.top) * mid V := by
  have hmaxA := originalAmalgamation_component_span P W A q shift u z hv hwindow hW hA _ hmax
  have hmaxV := c.originalVerticalClosure_profile_component_span P V l hV hmax
  have hAP := union_selected_count_ge (hD := hD) P A q shift u hq hv hwindow hA hcutq hcutLq
  let v := vH P.cells - eCell - l
  have htop := originalVerticalClosure_profile_top P V l hV
  have hw : P.cells = translate (-v)
      (V.cells.filter fun x => P.xi 0 ≤ content x ∧ content x < V.xi 0) := by
    rw [htop, originalVerticalClosure_upper_window P V l hV]
    change P.cells = translate (-v) (translate v P.cells)
    rw [translate_translate, neg_add_cancel, translate_zero]
  have hjoin := originalVerticalClosure_profile_join_no_interior P V l hV
  have hend : ∀ x ∈ diagramInterior V.cells, content x ≠ V.xi 0 := by
    intro x hx
    have hs := interior_content_strict V.isConnectedSkew_cells hx
    rw [V.maxContent_cells] at hs
    omega
  have hVP := originalLiteralWindow_selected_count_le (hD := hD)
    V P (P.xi 0) (V.xi 0) (-v) hw hjoin hend
  have hAl := c.original_normal_log_internal_caps A hmaxA k (hk.trans_le hAP)
  have hPl := c.original_normal_log_internal_caps P hmax k hk
  have hVl := c.original_normal_log_internal_caps V hmaxV k (hk.trans_le hVP)
  obtain ⟨hleft, hright⟩ := c.originalVerticalComparison_end_log_balance P W A V
    q shift u z l hq hv hwindow hW hA hV hcutq hcutLq hmax b a d hd k hk
  dsimp only at hAl hPl hVl hleft hright ⊢
  linear_combination (b : OtherField c.top) * hAl - (a : OtherField c.top) * hPl -
    (d : OtherField c.top) * hVl + hleft + hright

end SkewCornerDescent.Matrix.SelectedCoordinate
