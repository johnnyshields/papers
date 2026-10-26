/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueLowerBounds
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Original-generator support under partial differentiation

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Partial derivatives preserve the supported polynomial algebra. In particular,
every selected-function gradient stays below a later protected generator.
Sorry-free.
-/

namespace SkewCornerDescent
open MvPolynomial

/-- Polynomial partial derivatives introduce no new original generators. -/
theorem partial_mem_supported (p : SkewGluing.Lambda) (s : Set ℕ+)
    (hp : p ∈ supported ℚ s) (j : ℕ+) : pderiv j p ∈ supported ℚ s := by
  classical
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨k, hk, rfl⟩ := hp
    simp only [pderiv_X, Pi.single_apply]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | algebraMap q =>
    change pderiv j (MvPolynomial.C q) ∈ supported ℚ s
    rw [pderiv_C]
    exact Subalgebra.zero_mem _
  | add p q hp hq ihp ihq =>
    rw [map_add]
    exact Subalgebra.add_mem _ ihp ihq
  | mul p q hp hq ihp ihq =>
    rw [pderiv_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ ihp hq) (Subalgebra.mul_mem _ hp ihq)

namespace Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every selected-function gradient stays below any later protected generator. -/
theorem selected_gradient_mem_lower (H : ℕ+) (hH : c.top < H) (j : ℕ+) :
    c.residueMap (pderiv j (cellSchur D hD.1)) ∈ residueLowerField c.top H := by
  apply c.residue_supported_below H hH
  apply partial_mem_supported
  apply mem_supported.mpr
  intro k hk
  have hbound : (k : ℕ) ≤ polynomialSpan (cellSchur D hD.1) := Finset.le_sup hk
  rw [polynomialSpan_cellSchur hD, ← c.span_eq] at hbound
  exact lt_of_le_of_lt hbound hH

end Matrix.SelectedCoordinate
end SkewCornerDescent
