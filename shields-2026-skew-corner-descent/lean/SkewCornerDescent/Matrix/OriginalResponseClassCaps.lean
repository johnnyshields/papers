/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClasses
import SkewCornerDescent.Matrix.OriginalClosureCentralResponse
import SkewCornerDescent.Matrix.TrueCapExposureTops

/-!
# True caps in the actual finite response-class family

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:dual-identities`).
Both true cap positions belong to the complete original class family. Their
representatives preserve the literal cap tops, which lie strictly below the actual
closure top even when the two cap values coincide. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The two actual cap classes stay strictly below the literal closure top.
Their representative choices introduce no new top or cap-bound hypotheses. -/
theorem originalResponseClass_caps_below_closure {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) (K : ℕ+)
    (hKeq : let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
      (K : ℤ) = originalHessenbergDistance (hD := hD) Q middle middle) :
    c.originalResponseClassTop P hB (c.originalResponseClassOf P 0) < K ∧
      c.originalResponseClassTop P hB (c.originalResponseClassOf P (Fin.last _)) < K := by
  have hc := c.originalHorizontalClosure_central_distance P Q v hQ hB
  dsimp only at hc hKeq
  rw [c.originalCompletedGap_last_eq_splice P hB] at hc
  have hb := c.originalTrueCaps_below_closure P (originalSelectedEnumeration P ⟨0, hB⟩)
    (originalSelectedEnumeration P ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩)
  have hleft : (c.originalResponseClassTop P hB (c.originalResponseClassOf P 0) : ℤ) =
      originalFirstCapDistance P (originalSelectedEnumeration P ⟨0, hB⟩) := by
    rw [c.originalResponseClassTop_of, c.originalHessenbergTop_coe,
      originalHessenbergDistance_first P hB]
  have hright : (c.originalResponseClassTop P hB
      (c.originalResponseClassOf P (Fin.last _)) : ℤ) = originalLastCapDistance P
        (originalSelectedEnumeration P ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩) := by
    rw [c.originalResponseClassTop_of, c.originalHessenbergTop_coe,
      originalHessenbergDistance_last P hB]
  constructor
  · exact_mod_cast (show (c.originalResponseClassTop P hB (c.originalResponseClassOf P 0) : ℤ) <
      (K : ℤ) by omega)
  · exact_mod_cast (show (c.originalResponseClassTop P hB
      (c.originalResponseClassOf P (Fin.last _)) : ℤ) < (K : ℤ) by omega)

end SkewCornerDescent.Matrix.SelectedCoordinate
