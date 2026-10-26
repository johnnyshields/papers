/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TranscendentalConstants
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Constant polynomial factors over a rational generator field

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Monic divisors of constant polynomials
have algebraic coefficients. Algebraic independence and generation force these
coefficients back into the original field, preserving irreducibility.

Sorry-free.
-/

namespace SkewCornerDescent

variable {ι k E : Type*} [Field k] [Field E] [Algebra k E]

/-- Every monic factor of a coefficient-field polynomial descends to that field. -/
theorem monic_divisor_descends_of_algebraic_constants
    (hconst : ∀ z : E, IsAlgebraic k z → ∃ c : k, algebraMap k E c = z)
    {p : Polynomial k} (hp : p.Monic) {q : Polynomial E} (hq : q.Monic)
    (hd : q ∣ p.map (algebraMap k E)) :
    ∃ q₀ : Polynomial k, q₀.map (algebraMap k E) = q := by
  apply (Polynomial.mem_lifts q).mp
  apply (Polynomial.lifts_iff_coeff_lifts q).mpr
  intro i
  have hi := Polynomial.isIntegral_coeff_of_dvd p q hp hq hd i
  exact hconst _ hi.isAlgebraic

/-- Irreducible constant polynomials stay irreducible over the generated rational field. -/
theorem irreducible_map_of_algebraic_constants
    (hconst : ∀ z : E, IsAlgebraic k z → ∃ c : k, algebraMap k E c = z)
    {p : Polynomial k} (hp : p.Monic) (hirr : Irreducible p) :
    Irreducible (p.map (algebraMap k E)) := by
  have hinj := Polynomial.map_injective (algebraMap k E) (RingHom.injective _)
  have hp1 : p.map (algebraMap k E) ≠ 1 := by
    intro h
    apply hirr.ne_one
    apply hinj
    simpa only [Polynomial.map_one] using h
  apply (Polynomial.irreducible_of_monic (hp.map _) hp1).mpr
  intro f g hf hg hfg
  obtain ⟨f₀, hfm⟩ := monic_divisor_descends_of_algebraic_constants hconst hp hf
    ⟨g, hfg.symm⟩
  obtain ⟨g₀, hgm⟩ := monic_divisor_descends_of_algebraic_constants hconst hp hg
    ⟨f, by rw [mul_comm]; exact hfg.symm⟩
  have hprod : f₀ * g₀ = p := by
    apply hinj
    rw [Polynomial.map_mul, hfm, hgm]
    exact hfg
  rcases hirr.isUnit_or_isUnit hprod.symm with h | h
  · exact Or.inl (hf.eq_one_of_isUnit (hfm ▸ h.map (Polynomial.mapRingHom _)))
  · exact Or.inr (hg.eq_one_of_isUnit (hgm ▸ h.map (Polynomial.mapRingHom _)))

/-- Algebraic independence supplies the constant-field condition used in factor descent. -/
theorem irreducible_map_rational_generators {x : ι → E}
    (hx : AlgebraicIndependent k x) (hgen : IntermediateField.adjoin k (Set.range x) = ⊤)
    {p : Polynomial k} (hp : p.Monic) (hirr : Irreducible p) :
    Irreducible (p.map (algebraMap k E)) := by
  apply irreducible_map_of_algebraic_constants _ hp hirr
  intro z hz
  apply algebraic_constant_of_mem_adjoin hx _ hz
  rw [hgen]
  trivial

end SkewCornerDescent
