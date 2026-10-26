/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.ChildDescent
import Mathlib.RingTheory.Multiplicity
import Mathlib.Algebra.BigOperators.Associated

/-!
# High-span factors of the actual transported cofactor

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `thm:transport`).  The normal scalar has span strictly below the
period.  Thus every high-span irreducible factor is an actual composed child, and
its multiplicity is counted in the displayed child product.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
open SkewCornerDescent.Matrix
variable {ω : MarkedInner}

/-- None of the normalizing factors annihilates the transport scalar. -/
theorem IsLegal.transportScalar_ne_zero (h : ω.IsLegal) (D : Diagram) :
    ω.transportScalar h D ≠ 0 := by
  obtain ⟨ha, hb, hc, ht⟩ := h.normal_factors_ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero ht (pow_ne_zero _ ha))
    (pow_ne_zero _ hb)) (pow_ne_zero _ hc)

/-- Every scalar factor lies strictly below the period threshold. -/
theorem IsLegal.transportScalar_span_lt (h : ω.IsLegal) (D : Diagram) :
    (polynomialSpan (ω.transportScalar h D) : ℤ) < ω.period := by
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  have ha := h.normal_mark_spans.1
  have hb := h.normal_mark_spans.2
  have hc := h.normalC_span_le
  have ht := h.normalTheta_span_le
  have hw := h.2.2.1.2
  have hbound : polynomialSpan (ω.transportScalar h D) ≤
      max (max (max (polynomialSpan (ω.normalTheta h)) (polynomialSpan (ω.normalA h)))
        (polynomialSpan (ω.normalB h))) (polynomialSpan (ω.normalC h)) := by
    unfold transportScalar
    exact (polynomialSpan_mul_le _ _).trans (max_le_max
      ((polynomialSpan_mul_le _ _).trans (max_le_max
        ((polynomialSpan_mul_le _ _).trans (max_le_max_left _ (polynomialSpan_pow_le _ _)))
        (polynomialSpan_pow_le _ _))) (polynomialSpan_pow_le _ _))
  have ha' : (polynomialSpan (ω.normalA h) : ℤ) < ω.period := by omega
  have hb' : (polynomialSpan (ω.normalB h) : ℤ) < ω.period := by omega
  have hc' : (polynomialSpan (ω.normalC h) : ℤ) < ω.period := by
    have := Int.natCast_nonneg ω.width
    omega
  have ht' : (polynomialSpan (ω.normalTheta h) : ℤ) < ω.period := by
    have := Int.natCast_nonneg ω.width
    omega
  have hbound' : (polynomialSpan (ω.transportScalar h D) : ℤ) ≤
      max (max (max (polynomialSpan (ω.normalTheta h) : ℤ) (polynomialSpan (ω.normalA h)))
        (polynomialSpan (ω.normalB h))) (polynomialSpan (ω.normalC h)) := by
    exact_mod_cast hbound
  exact hbound'.trans_lt (max_lt (max_lt (max_lt ht' ha') hb') hc')

/-- High-span polynomials cannot divide the low-span normal scalar. -/
theorem IsLegal.not_dvd_transportScalar (h : ω.IsLegal) (D : Diagram) {f : Lambda}
    (hs : ω.period ≤ (polynomialSpan f : ℤ)) : ¬ f ∣ ω.transportScalar h D := by
  intro hd
  have hb := polynomialSpan_le_of_dvd (h.transportScalar_ne_zero D) hd
  have ht := h.transportScalar_span_lt D
  have hb' : (polynomialSpan f : ℤ) ≤ polynomialSpan (ω.transportScalar h D) := by
    exact_mod_cast hb
  omega

/-- Connected actual children give irreducible factors over the rational field. -/
theorem IsLegal.irreducible_child (h : ω.IsLegal) {D C : Diagram}
    (hD : IsConnectedSkew D) (hC : C ∈ edgeComponents (diagramInterior D)) :
    Irreducible (cellSchur (ω.compose C)
      (h.connected_compose (isConnectedSkew_component hD.1.interior hC)).1) := by
  simpa only [map_integralCellSchur] using
    (irreducible_integralCellSchur (K := ℚ)
      (h.connected_compose (isConnectedSkew_component hD.1.interior hC)))

/-- Every high-span irreducible divisor is associated to a displayed actual child. -/
theorem IsLegal.highSpan_factor_is_child (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) {f : Lambda}
    (hf : Irreducible f) (hs : ω.period ≤ (polynomialSpan f : ℤ))
    (hd : f ∣ cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior) :
    ∃ C : {C // C ∈ edgeComponents (diagramInterior D)},
      Associated f (cellSchur (ω.compose C.1)
        (h.connected_compose (isConnectedSkew_component hD.1.interior C.2)).1) := by
  rw [h.corner_transport hD hcard] at hd
  have hp : Prime f := hf.prime
  have hd' := (hp.dvd_mul.mp hd).resolve_left (h.not_dvd_transportScalar D hs)
  obtain ⟨C, _, hC⟩ := (hp.dvd_finsetProd_iff _).mp hd'
  exact ⟨C, hf.associated_of_dvd (h.irreducible_child hD C.2) hC⟩

/-- High-span multiplicities are exactly the sum of the actual child multiplicities. -/
theorem IsLegal.highSpan_multiplicity (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) {f : Lambda}
    (hf : Irreducible f) (hs : ω.period ≤ (polynomialSpan f : ℤ)) :
    emultiplicity f (cellSchur (diagramInterior (ω.compose D))
      (h.connected_compose hD).1.interior) =
      ∑ C ∈ (edgeComponents (diagramInterior D)).attach,
        emultiplicity f (cellSchur (ω.compose C.1)
          (h.connected_compose (isConnectedSkew_component hD.1.interior C.2)).1) := by
  rw [h.corner_transport hD hcard, emultiplicity_mul hf.prime,
    emultiplicity_eq_zero.mpr (h.not_dvd_transportScalar D hs), zero_add]
  exact Finset.emultiplicity_prod hf.prime _ _

/-- Each actual child lies at or above the high-span threshold. -/
theorem IsLegal.child_span_ge_period (h : ω.IsLegal) {D C : Diagram}
    (hD : IsConnectedSkew D) (hC : C ∈ edgeComponents (diagramInterior D)) :
    ω.period ≤ (polynomialSpan (cellSchur (ω.compose C)
      (h.connected_compose (isConnectedSkew_component hD.1.interior hC)).1) : ℤ) := by
  have hc := isConnectedSkew_component hD.1.interior hC
  have hs : 0 < span C := Finset.card_pos.mpr (hc.2.1.image content)
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  rw [polynomialSpan_cellSchur (h.connected_compose hc), span_compose hc h]
  have := Int.natCast_nonneg ω.width
  nlinarith

/-- Classification in both directions, up to the units of the rational polynomial ring. -/
theorem IsLegal.highSpan_factor_iff (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) {f : Lambda}
    (hf : Irreducible f) (hs : ω.period ≤ (polynomialSpan f : ℤ)) :
    f ∣ cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior ↔
      ∃ C : {C // C ∈ edgeComponents (diagramInterior D)},
        Associated f (cellSchur (ω.compose C.1)
          (h.connected_compose (isConnectedSkew_component hD.1.interior C.2)).1) := by
  constructor
  · exact h.highSpan_factor_is_child hD hcard hf hs
  · rintro ⟨C, he⟩
    exact he.dvd.trans (h.child_dvd_cofactor hD hcard C.2)

open scoped Classical in
/-- The multiplicity counts exactly the associated children, including repetitions. -/
theorem IsLegal.highSpan_multiplicity_count (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) {f : Lambda}
    (hf : Irreducible f) (hs : ω.period ≤ (polynomialSpan f : ℤ)) :
    emultiplicity f (cellSchur (diagramInterior (ω.compose D))
      (h.connected_compose hD).1.interior) =
      ∑ C ∈ (edgeComponents (diagramInterior D)).attach,
        if Associated f (cellSchur (ω.compose C.1)
          (h.connected_compose (isConnectedSkew_component hD.1.interior C.2)).1)
        then (1 : ℕ∞) else 0 := by
  classical
  rw [h.highSpan_multiplicity hD hcard hf hs]
  apply Finset.sum_congr rfl
  intro C _
  split_ifs with he
  · rw [← emultiplicity_eq_of_associated_right he]
    simpa only [pow_one, Nat.cast_one] using emultiplicity_pow_self_of_prime hf.prime 1
  · exact emultiplicity_eq_zero.mpr ((hf.dvd_irreducible_iff_associated
      (h.irreducible_child hD C.2)).not.mpr he)

end SkewGluing.MarkedInner
