/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.SchurPrimitive
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Gcd-reduced numerators

The exact division by the actual polynomial gcd in «Recovering the factors»
(`sec:extraction`, `eq:inner-recovery`, `eq:ratio`) of
`shields-2026-skew-marked-factor.tex`.
A gcd representative is chosen by Mathlib's UFD construction.  Its unit
ambiguity disappears under canonical primitive normalization.
-/

namespace SkewMarkedFactor
open Gluing

/-- The UFD supplies actual gcd representatives in the rational complete-generator ring. -/
noncomputable instance readoutGCD : GCDMonoid Lambda :=
  UniqueFactorizationMonoid.toGCDMonoid Lambda

/-- Exact polynomial division by the gcd, without a totalized field quotient. -/
noncomputable def reducedNumerator (U T : Lambda) : Lambda :=
  Classical.choose (gcd_dvd_left U T)

/-- The selected quotient satisfies the actual polynomial multiplication identity. -/
theorem gcd_mul_reducedNumerator (U T : Lambda) :
    gcd U T * reducedNumerator U T = U :=
  (Classical.choose_spec (gcd_dvd_left U T)).symm

/-- A nonzero numerator produces a nonzero gcd and a nonzero reduced numerator. -/
theorem reducedNumerator_ne_zero {U T : Lambda} (hU : U ≠ 0) : reducedNumerator U T ≠ 0 := by
  intro h
  have he := gcd_mul_reducedNumerator U T
  rw [h, mul_zero] at he
  exact hU he.symm

/-- A coprime cross-multiplication identifies the actual gcd-reduced numerator up to a unit. -/
theorem reducedNumerator_associated {U T E Ξ : Lambda}
    (hU : U ≠ 0) (hE : E ≠ 0) (hcop : IsRelPrime E Ξ)
    (hratio : U * Ξ = T * E) : Associated (reducedNumerator U T) E := by
  have hdiv : E ∣ U := hcop.dvd_of_dvd_mul_right (by
    rw [hratio]
    exact dvd_mul_left E T)
  obtain ⟨c, hUc⟩ := hdiv
  have hTc : T = c * Ξ := by
    apply mul_right_cancel₀ hE
    calc
      T * E = U * Ξ := hratio.symm
      _ = (c * Ξ) * E := by rw [hUc]; ring
  have hc : c ≠ 0 := by intro he; rw [hUc, he, mul_zero] at hU; exact hU rfl
  have hGc : Associated (gcd U T) c := by
    have hg := gcd_mul_left' c E Ξ
    have hu : IsUnit (gcd E Ξ) := gcd_isUnit_iff_isRelPrime.mpr hcop
    have ha : Associated (c * gcd E Ξ) c := by
      simpa only [mul_one] using (associated_one_iff_isUnit.mpr hu).mul_left c
    rw [hUc, hTc, mul_comm E c]
    exact hg.trans ha
  have hg : gcd U T ≠ 0 := by
    intro he
    have h := gcd_mul_reducedNumerator U T
    rw [he, zero_mul] at h
    exact hU h.symm
  obtain ⟨u, hu⟩ := hGc
  have hr : reducedNumerator U T = (u : Lambda) * E := by
    apply mul_left_cancel₀ hg
    calc
      gcd U T * reducedNumerator U T = U := gcd_mul_reducedNumerator U T
      _ = E * c := hUc
      _ = gcd U T * ((u : Lambda) * E) := by rw [← hu]; ring
  refine ⟨u⁻¹, ?_⟩
  rw [hr]
  simp [mul_assoc, mul_comm]

/-- Units in this polynomial ring are precisely nonzero rational constants. -/
theorem scalar_of_associated {f g : Lambda} (h : Associated f g) :
    ∃ q : ℚ, q ≠ 0 ∧ f = q • g := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨q, hq, he⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp
    (Units.isUnit (u⁻¹ : Lambdaˣ))
  refine ⟨q, hq.ne_zero, ?_⟩
  have hf : f = (u⁻¹ : Lambdaˣ) * g := by
    calc
      f = (f * (u : Lambda)) * (u⁻¹ : Lambdaˣ) := by simp [mul_assoc]
      _ = g * (u⁻¹ : Lambdaˣ) := by rw [hu]
      _ = (u⁻¹ : Lambdaˣ) * g := mul_comm _ _
  rw [he] at hf
  simpa only [MvPolynomial.smul_eq_C_mul] using hf

/-- An irreducible polynomial is relatively prime to anything it does not divide. -/
theorem relPrime_of_irreducible_not_dvd {E Ξ : Lambda} (hE : Irreducible E)
    (hnot : ¬ E ∣ Ξ) : IsRelPrime E Ξ := by
  intro d hd hΞ
  obtain ⟨c, hc⟩ := hd
  rcases hE.isUnit_or_isUnit hc with hu | hu
  · exact hu
  · apply False.elim
    apply hnot
    rw [hc]
    exact hu.mul_right_dvd.mpr hΞ

/-- Once the ratio is proved, primitive normalization recovers the genuine inner function. -/
theorem primitive_reducedNumerator_of_ratio {D : Diagram} (hD : IsSkew D)
    {U T Ξ : Lambda} (hU : U ≠ 0) (hcop : IsRelPrime (cellSchur D) Ξ)
    (hratio : U * Ξ = T * cellSchur D) :
    primitive (reducedNumerator U T) = cellSchur D := by
  have hE : cellSchur D ≠ 0 := by
    have hc := (coefficient_one_minimum_cell_schur hD).1
    intro hz
    rw [hz, AddMonoidAlgebra.coeff_zero] at hc
    exact zero_ne_one hc
  obtain ⟨q, hq, he⟩ := scalar_of_associated
    (reducedNumerator_associated hU hE hcop hratio)
  rw [he]
  exact primitive_cellSchur_scalar hD q hq

end SkewMarkedFactor
