/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SignedRationalRepresentation
import SkewCornerDescent.RationalReflection

/-!
# Active signed support as roots of the reduced rational pair

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The roots of a coprime rational numerator/denominator pair are exactly the
nonzero signed linear-factor support. Both signs and complete cancellations
are retained. Sorry-free.
-/

namespace SkewCornerDescent

open scoped BigOperators

/-- A finite product of rational linear factors vanishes exactly at one of
its retained roots with positive multiplicity. -/
theorem finite_linear_product_eval_zero (s : Finset ℚ) (m : ℚ → ℕ) (α : ℚ) :
    (∏ γ ∈ s, (Polynomial.X - Polynomial.C γ) ^ m γ).eval α = 0 ↔
      α ∈ s ∧ m α ≠ 0 := by
  classical
  simp only [Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨γ, hγ, hpow⟩
    have hm : m γ ≠ 0 := by
      intro hzero
      rw [hzero, pow_zero] at hpow
      exact one_ne_zero hpow
    have ha : α = γ := sub_eq_zero.mp ((pow_eq_zero_iff hm).mp hpow)
    subst γ
    exact ⟨hγ, hm⟩
  · rintro ⟨hα, hm⟩
    refine ⟨α, hα, ?_⟩
    rw [sub_self, zero_pow hm]

/-- The numerator keeps exactly the positive signed roots when its scalar is nonzero. -/
theorem signedRationalNumerator_eval_zero (ε : ℤ) (s : Finset ℚ) (e : ℚ → ℤ)
    (hε : (ε : ℚ) ≠ 0) (α : ℚ) :
    (signedRationalNumerator ε s e).eval α = 0 ↔ α ∈ s ∧ 0 < e α := by
  rw [signedRationalNumerator, Polynomial.eval_mul, Polynomial.eval_C,
    mul_eq_zero, or_iff_right hε, finite_linear_product_eval_zero]
  apply and_congr_right
  intro _
  omega

/-- The denominator keeps exactly the negative signed roots. -/
theorem signedRationalDenominator_eval_zero (s : Finset ℚ) (e : ℚ → ℤ) (α : ℚ) :
    (signedRationalDenominator s e).eval α = 0 ↔ α ∈ s ∧ e α < 0 := by
  rw [signedRationalDenominator, finite_linear_product_eval_zero]
  apply and_congr_right
  intro _
  omega

/-- A coprime rational polynomial pair cannot vanish simultaneously at one rational point. -/
theorem coprime_rational_pair_not_both_zero (p q : Polynomial ℚ) (hpq : IsCoprime p q)
    (α : ℚ) : ¬ (p.eval α = 0 ∧ q.eval α = 0) := by
  intro hz
  obtain ⟨a, b, hab⟩ := hpq.map (Polynomial.evalRingHom α)
  change a * p.eval α + b * q.eval α = 1 at hab
  have h : (0 : ℚ) = 1 := by
    simpa only [hz.1, hz.2, mul_zero, zero_mul, zero_add] using hab
  exact zero_ne_one h

/-- The active signed factor support is precisely the root union of the
coprime rational pair, independently of the chosen cross-product representation. -/
theorem signedRational_root_support (p q : Polynomial ℚ) (hpq : IsCoprime p q)
    (ε : ℤ) (s : Finset ℚ) (e : ℚ → ℤ) (hε : (ε : ℚ) ≠ 0)
    (he : ∀ α ∈ s, e α ≠ 0)
    (hcross : p * signedRationalDenominator s e = signedRationalNumerator ε s e * q)
    (α : ℚ) : α ∈ s ↔ p.eval α = 0 ∨ q.eval α = 0 := by
  have hc := congrArg (Polynomial.eval α) hcross
  rw [Polynomial.eval_mul, Polynomial.eval_mul] at hc
  constructor
  · intro hα
    rcases lt_or_gt_of_ne (he α hα) with hneg | hpos
    · have hd := (signedRationalDenominator_eval_zero s e α).mpr ⟨hα, hneg⟩
      have hn : (signedRationalNumerator ε s e).eval α ≠ 0 := by
        intro hz
        have h := (signedRationalNumerator_eval_zero ε s e hε α).mp hz
        exact (not_lt_of_ge hneg.le) h.2
      rw [hd, mul_zero] at hc
      exact Or.inr ((mul_eq_zero.mp hc.symm).resolve_left hn)
    · have hn := (signedRationalNumerator_eval_zero ε s e hε α).mpr ⟨hα, hpos⟩
      have hd : (signedRationalDenominator s e).eval α ≠ 0 := by
        intro hz
        have h := (signedRationalDenominator_eval_zero s e α).mp hz
        exact (not_lt_of_ge hpos.le) h.2
      rw [hn, zero_mul] at hc
      exact Or.inl ((mul_eq_zero.mp hc).resolve_right hd)
  · intro hroot
    by_contra hα
    have hn : (signedRationalNumerator ε s e).eval α ≠ 0 := by
      intro hz
      exact hα ((signedRationalNumerator_eval_zero ε s e hε α).mp hz).1
    have hd : (signedRationalDenominator s e).eval α ≠ 0 := by
      intro hz
      exact hα ((signedRationalDenominator_eval_zero s e α).mp hz).1
    rcases hroot with hp | hq
    · rw [hp, zero_mul] at hc
      have hq := (mul_eq_zero.mp hc.symm).resolve_left hn
      exact coprime_rational_pair_not_both_zero p q hpq α ⟨hp, hq⟩
    · rw [hq, mul_zero] at hc
      have hp := (mul_eq_zero.mp hc).resolve_right hd
      exact coprime_rational_pair_not_both_zero p q hpq α ⟨hp, hq⟩

/-- Reflecting the reduced rational pair reflects its complete root union. -/
theorem rationalReflection_root_union (p q : Polynomial ℚ) (α : ℚ) :
    (rationalReflection p).eval α = 0 ∨ (rationalReflection q).eval α = 0 ↔
      p.eval (1 - α) = 0 ∨ q.eval (1 - α) = 0 := by
  change Polynomial.aeval α (rationalReflection p) = 0 ∨
      Polynomial.aeval α (rationalReflection q) = 0 ↔ _
  rw [rationalReflection_aeval, rationalReflection_aeval]
  rfl

end SkewCornerDescent
