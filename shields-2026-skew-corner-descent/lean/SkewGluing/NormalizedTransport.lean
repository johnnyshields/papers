/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.GeometricCompositionMap

/-!
# Normalized coefficient transport

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:coefficient-transport`).  Differentiating the actual geometric
composition identity supplies the normalized cofactor relation before cancellation.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
open MvPolynomial SkewCornerDescent.Matrix
variable {ω : MarkedInner}

/-- No normalization factor contains a transported top generator. -/
theorem IsLegal.pderiv_normalFactors (h : ω.IsLegal) (M L : ℕ+)
    (hL : (L : ℤ) = (M : ℤ) * ω.period + ω.width) :
    pderiv L (ω.normalA h) = 0 ∧ pderiv L (ω.normalB h) = 0 ∧
      pderiv L (ω.normalC h) = 0 := by
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  have hw : (ω.width : ℤ) < ω.period := h.2.2.1.2
  have hm : 1 ≤ (M : ℤ) := by exact_mod_cast M.pos
  have hmp := mul_le_mul_of_nonneg_right hm hp.le
  have hz (f : Lambda) (hb : (polynomialSpan f : ℤ) < (L : ℤ)) : pderiv L f = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hk
    have hn : (L : ℕ) ≤ polynomialSpan f := Finset.le_sup hk
    have hnZ : (L : ℤ) ≤ polynomialSpan f := by exact_mod_cast hn
    omega
  refine ⟨hz _ ?_, hz _ ?_, hz _ ?_⟩
  · have := h.normal_mark_spans.1
    nlinarith
  · have := h.normal_mark_spans.2
    nlinarith
  · have := h.normalC_span_le
    have hw0 : 0 ≤ (ω.width : ℤ) := Int.natCast_nonneg _
    have hL0 : 0 < (L : ℤ) := by exact_mod_cast L.pos
    omega

/-- The geometric identity and the generator coefficient computation have the same top coefficient. -/
theorem IsLegal.normalized_cofactor_transport (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (M L : ℕ+) (hM : (M : ℕ) = span D)
    (hL : (L : ℤ) = (M : ℤ) * ω.period + ω.width) :
    ∃ sign : ℕ,
      (-1 : Lambda) ^ sign *
        (ω.normalA h ^ (D.card - (D.image Prod.fst).card) *
         ω.normalB h ^ (D.card - (D.image Prod.snd).card) *
         ω.normalC h ^ (D.card - span D) *
         ((-1) ^ (((ω.compose D).image Prod.fst).card - 1) *
           cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior)) =
      (-1) ^ ((D.image Prod.fst).card - 1) * ω.normalA h ^ ((M : ℕ) - 1) *
        ((-1) ^ (((ω.compose (horizontalRow M)).image Prod.fst).card - 1) *
          (ω.normalTheta h * ω.normalC h ^ (M : ℕ) * ω.normalB h ^ ((M : ℕ) - 1))) *
        ω.modifiedCompositionMap h (cellSchur (diagramInterior D) hD.1.interior) := by
  obtain ⟨sign, hs⟩ := h.modifiedCompositionMap_cellSchur hD
  have hd := congrArg (pderiv L) hs
  obtain ⟨ha, hb, hc⟩ := h.pderiv_normalFactors M L hL
  have hspan : (L : ℕ) = span (ω.compose D) := by
    have he := span_compose hD h
    rw [← hM] at he
    exact_mod_cast (hL.trans he.symm)
  simp only [pderiv_mul, pderiv_pow, map_neg, pderiv_one, neg_zero, mul_zero,
    zero_mul, zero_add, add_zero, ha, hb, hc,
    pderiv_cellSchur_corner (h.connected_compose hD) L hspan] at hd
  exact ⟨sign, hd.symm.trans (h.coefficient_transport_substitution hD M L hM hL)⟩

end SkewGluing.MarkedInner
