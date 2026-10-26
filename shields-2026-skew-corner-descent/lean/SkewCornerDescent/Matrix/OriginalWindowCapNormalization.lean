/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowTrueCaps
import SkewCornerDescent.Matrix.OriginalCapNormalization

/-!
# Produced true-cap normalization of a complete overlap window

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`). Literal
complete end windows supply both true exterior germs and the exact signed internal
residue equation. No cap equality or source selected-count positivity is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both actual end windows produce their common residue cap product and an inhabited
source selected inventory. Empty pivots and boundary proper minors are retained. -/
theorem originalWindow_true_cap_product {n k : ℕ} (P : Profile n) (W : Profile k)
    (q : ℤ) (v z : ℤ × ℤ)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W) :
    0 < originalSelectedCount (hD := hD) P ∧
      c.originalTrueCapProduct P = c.originalTrueCapProduct W := by
  have hWP : W.cells = translate (-z)
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
    rw [← hW, translate_translate, neg_add_cancel, translate_zero]
  have hWUpper : W.cells = translate (-z - v)
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0) := by
    rw [hwindow, translate_translate]
    have ht : -z - v + v = -z := by abel
    rw [ht]
    exact hWP
  have hb := originalProfile_interior_boundary_gaps P
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P W 0 (P.xi 0 - q)
    (-z) hWP hb.1 hcutLq
  have hl := c.originalWindow_true_left_response P W q (-z - v) hWUpper hcutq hb.2 hC
  have hr := c.originalWindow_true_right_response P W q (-z) hWP hb.1 hcutLq hC
  refine ⟨hC.trans_le hc, ?_⟩
  unfold originalTrueCapProduct
  rw [hl, hr]

/-- The exact signed internal residue equation follows from literal windows and standing
corner powers. Its scalar, cap equality, and full removed-factor cancellation are produced. -/
theorem originalWindow_cap_normalized_ratio {n k : ℕ} (P : Profile n) (W : Profile k)
    (q : ℤ) (v z : ℤ × ℤ)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hQ : ∀ C ∈ edgeComponents (diagramInterior W.cells), span C ≤ (c.top : ℕ))
    (b a d : ℕ) (hd : d + a = b)
    (hcorner : (jtMatrix (fun j : Fin n => P.xi j.succ)
          (fun j => P.zeta j.castSucc)).det ^ a =
      (jtMatrix (fun j : Fin k => W.xi j.succ)
          (fun j => W.zeta j.castSucc)).det ^ b) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
        (ε : OtherField c.top) * (∏ i, c.originalInternalResidue P i) ^ a /
          ((∏ i, c.originalInternalResidue W i) ^ b * c.originalTrueCapProduct P ^ d) := by
  obtain ⟨hB, hcaps⟩ := c.originalWindow_true_cap_product P W q v z hwindow hW
    hcutq hcutLq hC
  exact c.originalHessenberg_cap_normalized_ratio P W hB hC hP hQ b a d hd hcorner hcaps

end SkewCornerDescent.Matrix.SelectedCoordinate
