/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.WholeDiagramTranspose
import SkewGluing.RowGeneratorBridge

/-!
# Generator bands of the original Schur involution

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Every generator image is the actual column Schur function of the same span.
The complete polynomial span and every strict lower-generator band are preserved.
Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial SkewCornerDescent.Matrix

/-- The canonical cell function of a positive horizontal row is its generator. -/
theorem cellSchur_horizontal_row (j : ℕ+) :
    cellSchur (horizontalRow j) (isConnectedSkew_horizontalRow j.pos).1 = X j := by
  rw [cellSchur_eq_gluing _ (isConnectedSkew_horizontalRow j.pos).1]
  exact gluing_cellSchur_horizontalRow j

/-- The original generator image has exactly the same span, because it is
an actual transposed row rather than a finite-alphabet elementary polynomial. -/
theorem polynomialSpan_schurInvolution_X (j : ℕ+) :
    polynomialSpan (schurInvolution (X j)) = j := by
  rw [← cellSchur_horizontal_row j,
    schurInvolution_cellSchur (isConnectedSkew_horizontalRow j.pos),
    polynomialSpan_cellSchur (isConnectedSkew_transpose (isConnectedSkew_horizontalRow j.pos)),
    span_transpose, span_horizontalRow]

/-- Every elementary generator image uses only original generators at or below its index. -/
theorem elem_var_le (j k : ℕ+) (hk : k ∈ (elem j).vars) : (k : ℕ) ≤ j := by
  have h : (k : ℕ) ≤ polynomialSpan (elem j) := Finset.le_sup hk
  rw [← schurInvolution_X, polynomialSpan_schurInvolution_X] at h
  exact h

/-- Substitution by the existing Schur involution cannot raise generator span. -/
theorem polynomialSpan_schurInvolution_le (f : Lambda) :
    polynomialSpan (schurInvolution f) ≤ polynomialSpan f := by
  apply Finset.sup_le
  intro k hk
  change k ∈ (bind₁ (fun j : ℕ+ => elem j) f).vars at hk
  obtain ⟨j, hj, hkj⟩ := mem_vars_bind₁ (fun j : ℕ+ => elem j) f hk
  exact (elem_var_le j k hkj).trans (Finset.le_sup hj)

/-- The complete polynomial span is invariant under whole-diagram Schur involution. -/
theorem polynomialSpan_schurInvolution (f : Lambda) :
    polynomialSpan (schurInvolution f) = polynomialSpan f := by
  apply le_antisymm (polynomialSpan_schurInvolution_le f)
  have h := polynomialSpan_schurInvolution_le (schurInvolution f)
  rwa [schurInvolution_involutive] at h

/-- Every strict lower-generator band is preserved in both directions. -/
theorem schurInvolution_mem_supported_below (N : ℕ+) (f : Lambda) :
    schurInvolution f ∈ supported ℚ {j : ℕ+ | j < N} ↔
      f ∈ supported ℚ {j : ℕ+ | j < N} := by
  have hmap : ∀ g : Lambda, g ∈ supported ℚ {j : ℕ+ | j < N} →
      schurInvolution g ∈ supported ℚ {j : ℕ+ | j < N} := by
    intro g hg
    apply mem_supported.mpr
    intro k hk
    change k ∈ (bind₁ (fun j : ℕ+ => elem j) g).vars at hk
    obtain ⟨j, hj, hkj⟩ := mem_vars_bind₁ (fun j : ℕ+ => elem j) g hk
    have hjN := mem_supported.mp hg hj
    have hkN : (k : ℕ) < N := lt_of_le_of_lt (elem_var_le j k hkj) hjN
    exact hkN
  constructor
  · intro h
    have ht := hmap (schurInvolution f) h
    rwa [schurInvolution_involutive] at ht
  · exact hmap f

end SkewCornerDescent
