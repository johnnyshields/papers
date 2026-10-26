/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.RowNormalization
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Modified composition on complete homogeneous generators

Formalizes the generator clause of `eq:homomorphism` in
`shields-2026-skew-corner-descent.tex`, «Corner transport» (`sec:transport`).
The row functions are those of actual compositions.  Lower-generator substitution
cannot introduce the target highest generator.

Sorry-free.
-/

namespace SkewGluing
open MvPolynomial SkewCornerDescent.Matrix

/-- A normalized horizontal row has exactly its stated content span. -/
theorem span_horizontalRow (m : ℕ) : span (horizontalRow m) = m := by
  simp [span, contents, horizontalRow, Finset.image_image, Function.comp_def, content]

namespace MarkedInner
variable (ω : MarkedInner)

/-- The actual Schur function of the positive-length row composite. -/
noncomputable def rowSchur (h : ω.IsLegal) (j : ℕ+) : Lambda :=
  cellSchur (ω.compose (horizontalRow j))
    (h.isConnectedSkew_compose_horizontalRow_all j.pos).1

/-- The image `A^(j-1) b_j` of a complete homogeneous generator. -/
noncomputable def modifiedGenerator (h : ω.IsLegal) (j : ℕ+) : Lambda :=
  ω.normalA h ^ ((j : ℕ) - 1) * ω.rowSchur h j

/-- The algebra map uniquely specified by the paper's complete-homogeneous generator values. -/
noncomputable def modifiedCompositionMap (h : ω.IsLegal) : Lambda →ₐ[ℚ] Lambda :=
  bind₁ (ω.modifiedGenerator h)

variable {ω}

/-- The actual row function has its geometric highest generator. -/
theorem IsLegal.rowSchur_span (h : ω.IsLegal) (j : ℕ+) :
    (polynomialSpan (ω.rowSchur h j) : ℤ) = (j : ℤ) * ω.period + ω.width := by
  rw [rowSchur, polynomialSpan_cellSchur (h.isConnectedSkew_compose_horizontalRow_all j.pos),
    span_compose (isConnectedSkew_horizontalRow j.pos) h, span_horizontalRow]

/-- Every variable of the substituted generator is bounded by the actual row span. -/
theorem IsLegal.modifiedGenerator_var_le (h : ω.IsLegal) (j k : ℕ+)
    (hk : k ∈ (ω.modifiedGenerator h j).vars) :
    (k : ℤ) ≤ (j : ℤ) * ω.period + ω.width := by
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  have hj : 1 ≤ (j : ℤ) := by exact_mod_cast j.pos
  have hn := h.normal_mark_spans.1
  have hs := h.rowSchur_span j
  rcases Finset.mem_union.mp (vars_mul _ _ hk) with hk | hk
  · have hkA := vars_pow (ω.normalA h) ((j : ℕ) - 1) hk
    have hkn : (k : ℕ) ≤ polynomialSpan (ω.normalA h) := Finset.le_sup hkA
    have hkZ : (k : ℤ) ≤ polynomialSpan (ω.normalA h) := by exact_mod_cast hkn
    have hm := mul_le_mul_of_nonneg_right hj hp.le
    nlinarith
  · have hkn : (k : ℕ) ≤ polynomialSpan (ω.rowSchur h j) := Finset.le_sup hk
    have hkZ : (k : ℤ) ≤ polynomialSpan (ω.rowSchur h j) := by exact_mod_cast hkn
    omega

/-- Substituting lower generators cannot introduce the transported top generator. -/
theorem IsLegal.modifiedCompositionMap_mem_below (h : ω.IsLegal) (M L : ℕ+)
    (hL : (L : ℤ) = (M : ℤ) * ω.period + ω.width) {f : Lambda}
    (hf : f ∈ supported ℚ {j : ℕ+ | j < M}) :
    ω.modifiedCompositionMap h f ∈ supported ℚ {k : ℕ+ | k < L} := by
  apply mem_supported.mpr
  intro k hk
  obtain ⟨j, hj, hkj⟩ := mem_vars_bind₁ (ω.modifiedGenerator h) f hk
  have hjM := mem_supported.mp hf hj
  have hjZ : (j : ℤ) + 1 ≤ M := by exact_mod_cast hjM
  have hb := h.modifiedGenerator_var_le j k hkj
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  have hm := mul_le_mul_of_nonneg_right hjZ hp.le
  have hkL : (k : ℤ) < L := by nlinarith
  exact_mod_cast hkL

/-- Lower-generator remainders have zero derivative at the transported top generator. -/
theorem IsLegal.pderiv_modifiedCompositionMap_eq_zero (h : ω.IsLegal) (M L : ℕ+)
    (hL : (L : ℤ) = (M : ℤ) * ω.period + ω.width) {f : Lambda}
    (hf : f ∈ supported ℚ {j : ℕ+ | j < M}) :
    pderiv L (ω.modifiedCompositionMap h f) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hh
  have := mem_supported.mp (h.modifiedCompositionMap_mem_below M L hL hf) hh
  exact (lt_irrefl L) this

end MarkedInner
end SkewGluing
