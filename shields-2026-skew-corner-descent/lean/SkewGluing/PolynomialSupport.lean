/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.CofactorAssembly

/-!
# Generator bounds for disconnected skew functions

Formalizes the componentwise generator-span bound used by
`shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`sec:marks`, `eq:normalization-bounds`).

Sorry-free.
-/

namespace SkewGluing

open MvPolynomial SkewCornerDescent.Matrix

/-- Every generator of a disconnected skew function is bounded by the diagram's content span. -/
theorem cellSchur_mem_atMost_span (D : Diagram) (hs : IsSkew D) :
    cellSchur D hs ∈ supported ℚ {k : ℕ+ | (k : ℕ) ≤ span D} := by
  classical
  unfold cellSchur
  apply Subalgebra.prod_mem
  intro C _
  have hc := isConnectedSkew_component hs C.2
  have hsp := polynomialSpan_cellSchur hc
  rw [cellSchur_eq_connected hc] at hsp
  apply mem_supported.mpr
  intro k hk
  have hksp : (k : ℕ) ≤ polynomialSpan (connectedSchur C.1 hc) :=
    Finset.le_sup (f := fun k : ℕ+ => (k : ℕ)) hk
  rw [hsp] at hksp
  exact hksp.trans (Finset.card_le_card (Finset.image_subset_image (component_subset C.2)))

/-- The generator span of a component product does not exceed the total content span. -/
theorem polynomialSpan_cellSchur_le (D : Diagram) (hs : IsSkew D) :
    polynomialSpan (cellSchur D hs) ≤ span D := by
  apply Finset.sup_le
  intro k hk
  exact mem_supported.mp (cellSchur_mem_atMost_span D hs) hk

/-- A skew component product is nonzero, including the empty diagram's empty product. -/
theorem cellSchur_ne_zero (D : Diagram) (hs : IsSkew D) : cellSchur D hs ≠ 0 := by
  classical
  unfold cellSchur
  apply Finset.prod_ne_zero_iff.mpr
  intro C _
  have hc := isConnectedSkew_component hs C.2
  have hir := irreducible_cellSchur hc
  rw [cellSchur_eq_connected hc] at hir
  exact hir.ne_zero

end SkewGluing
