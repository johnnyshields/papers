/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.ModifiedGenerators

/-!
# Highest-generator coefficient under modified substitution

Formalizes the coefficient extraction step of `eq:coefficient-transport` in
`shields-2026-skew-corner-descent.tex`, «Corner transport» (`sec:transport`).
The algebra map and all its row coefficients are constructed.  This module proves
coefficient extraction, not the separate geometric modified-composition identity.

Sorry-free.
-/

namespace SkewGluing
open MvPolynomial SkewCornerDescent.Matrix

/-- Integral lower-generator support survives the rational coefficient embedding. -/
theorem map_integral_mem_below {L : ℕ+} {R : MvPolynomial ℕ+ ℤ}
    (hR : R ∈ supported ℤ {k : ℕ+ | k < L}) :
    map (Int.castRingHom ℚ) R ∈ supported ℚ {k : ℕ+ | k < L} := by
  apply mem_supported.mpr
  intro k hk
  exact mem_supported.mp hR (vars_map _ _ hk)

/-- A connected diagram's actual interior uses only generators below its geometric span. -/
theorem interiorSchur_mem_below {D : Diagram} (hD : IsConnectedSkew D) (M : ℕ+)
    (hM : (M : ℕ) = span D) :
    cellSchur (diagramInterior D) hD.1.interior ∈ supported ℚ {k : ℕ+ | k < M} := by
  have hg := MarkedInner.span_le_of_content_Ioo (minContent D) (maxContent D)
    (fun x hx => interior_content_strict hD hx)
  have hsp := span_eq_of_isConnectedSkew hD
  have hp := polynomialSpan_cellSchur_le (diagramInterior D) hD.1.interior
  have hpZ : (polynomialSpan (cellSchur (diagramInterior D) hD.1.interior) : ℤ) ≤
      span (diagramInterior D) := by exact_mod_cast hp
  have hMZ : (M : ℤ) = (span D : ℤ) := by exact_mod_cast hM
  have hpos : 0 < (M : ℤ) := by exact_mod_cast M.pos
  apply mem_supported.mpr
  intro k hk
  have hkn : (k : ℕ) ≤ polynomialSpan (cellSchur (diagramInterior D) hD.1.interior) :=
    Finset.le_sup hk
  have hkZ : (k : ℤ) ≤ polynomialSpan (cellSchur (diagramInterior D) hD.1.interior) := by
    exact_mod_cast hkn
  have hkM : (k : ℤ) < M := by omega
  exact_mod_cast hkM

/-- The signed actual interior function is the derivative at the actual geometric top index. -/
theorem pderiv_cellSchur_corner {D : Diagram} (hD : IsConnectedSkew D) (M : ℕ+)
    (hM : (M : ℕ) = span D) :
    pderiv M (cellSchur D hD.1) =
      (-1) ^ ((D.image Prod.fst).card - 1) * cellSchur (diagramInterior D) hD.1.interior := by
  obtain ⟨L, hL, _, R, hR, he⟩ := cellSchur_corner hD
  have hLM : L = M := Subtype.ext (hL.trans hM.symm)
  subst L
  have hzI : pderiv M (cellSchur (diagramInterior D) hD.1.interior) = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hh
    exact (lt_irrefl M) (mem_supported.mp (interiorSchur_mem_below hD M hM) hh)
  have hzR : pderiv M (map (Int.castRingHom ℚ) R) = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hh
    exact (lt_irrefl M) (mem_supported.mp (map_integral_mem_below hR) hh)
  rw [he]
  simp [hzI, hzR, mul_comm]

namespace MarkedInner
variable {ω : MarkedInner}

/-- The substituted top generator has exactly the signed row cap coefficient. -/
theorem IsLegal.pderiv_modifiedGenerator_top (h : ω.IsLegal) (M L : ℕ+)
    (hL : (L : ℤ) = (M : ℤ) * ω.period + ω.width) :
    pderiv L (ω.modifiedGenerator h M) =
      ω.normalA h ^ ((M : ℕ) - 1) *
        ((-1) ^ (((ω.compose (horizontalRow M)).image Prod.fst).card - 1) *
          (ω.normalTheta h * ω.normalC h ^ (M : ℕ) * ω.normalB h ^ ((M : ℕ) - 1))) := by
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  have hM : 1 ≤ (M : ℤ) := by exact_mod_cast M.pos
  have hm := mul_le_mul_of_nonneg_right hM hp.le
  have hzA : pderiv L (ω.normalA h) = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hk
    have hkn : (L : ℕ) ≤ polynomialSpan (ω.normalA h) := Finset.le_sup hk
    have hkZ : (L : ℤ) ≤ polynomialSpan (ω.normalA h) := by exact_mod_cast hkn
    have hs := h.normal_mark_spans.1
    nlinarith
  have hs : (L : ℕ) = span (ω.compose (horizontalRow M)) := by
    have he := span_compose (isConnectedSkew_horizontalRow M.pos) h
    rw [span_horizontalRow] at he
    exact_mod_cast (hL.trans he.symm)
  have hd := pderiv_cellSchur_corner (h.isConnectedSkew_compose_horizontalRow_all M.pos) L hs
  rw [h.interiorSchur_compose_row_normalization M.pos] at hd
  simp only [modifiedGenerator, pderiv_mul, pderiv_pow, hzA, mul_zero, zero_mul, zero_add]
  exact congrArg (fun f => ω.normalA h ^ ((M : ℕ) - 1) * f) hd

/-- Coefficient extraction for the actual constructed algebra map at the actual transported span. -/
theorem IsLegal.coefficient_transport_substitution (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (M L : ℕ+) (hM : (M : ℕ) = span D)
    (hL : (L : ℤ) = (M : ℤ) * ω.period + ω.width) :
    pderiv L (ω.modifiedCompositionMap h (cellSchur D hD.1)) =
      (-1) ^ ((D.image Prod.fst).card - 1) * ω.normalA h ^ ((M : ℕ) - 1) *
        ((-1) ^ (((ω.compose (horizontalRow M)).image Prod.fst).card - 1) *
          (ω.normalTheta h * ω.normalC h ^ (M : ℕ) * ω.normalB h ^ ((M : ℕ) - 1))) *
        ω.modifiedCompositionMap h (cellSchur (diagramInterior D) hD.1.interior) := by
  obtain ⟨M', hM', _, R, hR, he⟩ := cellSchur_corner hD
  have hMM : M' = M := Subtype.ext (hM'.trans hM.symm)
  subst M'
  have hzI := h.pderiv_modifiedCompositionMap_eq_zero M L hL
    (interiorSchur_mem_below hD M hM)
  have hzR := h.pderiv_modifiedCompositionMap_eq_zero M L hL (map_integral_mem_below hR)
  rw [he]
  simp only [map_add, map_mul, map_pow, map_neg, map_one]
  have hX : ω.modifiedCompositionMap h (X M) = ω.modifiedGenerator h M := bind₁_X_right _ _
  rw [hX]
  simp only [pderiv_mul, pderiv_pow, map_neg, pderiv_one, neg_zero, mul_zero,
    zero_mul, zero_add, add_zero, hzI, hzR, h.pderiv_modifiedGenerator_top M L hL]
  ring

end MarkedInner
end SkewGluing
