/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.EmptyClosureComplement

/-!
# Rational support under complementary closure coordinates

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Changing the complete horizontal reference to the vertical one sends the
normalized closure coordinate to its complement. The exact substitution
`X ↦ 1-X` preserves coprime rational polynomial pairs. Sorry-free.
-/

namespace SkewCornerDescent

/-- Reflection of the rational closure coordinate, as a genuine algebra equivalence. -/
noncomputable def rationalReflection : Polynomial ℚ ≃ₐ[ℚ] Polynomial ℚ :=
  Polynomial.algEquivOfCompEqX (1 - Polynomial.X) (1 - Polynomial.X)
    (by simp only [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp]; ring)
    (by simp only [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp]; ring)

/-- Reflection is the full polynomial substitution, not coefficientwise sign changes. -/
theorem rationalReflection_apply (p : Polynomial ℚ) :
    rationalReflection p = p.comp (1 - Polynomial.X) := rfl

/-- Evaluating the reflected polynomial evaluates the original one at the complementary point. -/
theorem rationalReflection_aeval {K : Type*} [CommRing K] [Algebra ℚ K]
    (x : K) (p : Polynomial ℚ) :
    Polynomial.aeval x (rationalReflection p) = Polynomial.aeval (1 - x) p := by
  rw [rationalReflection_apply, Polynomial.aeval_comp]
  simp only [map_sub, map_one, Polynomial.aeval_X]

/-- A coprime rational numerator and denominator remain coprime after reflection. -/
theorem rationalReflection_isCoprime {p q : Polynomial ℚ} (h : IsCoprime p q) :
    IsCoprime (rationalReflection p) (rationalReflection q) :=
  h.map rationalReflection.toRingHom

/-- The two polynomial substitutions really undo each other on every rational polynomial. -/
theorem rationalReflection_involutive : Function.Involutive rationalReflection := by
  intro p
  rw [rationalReflection_apply, rationalReflection_apply, Polynomial.comp_assoc]
  have h : (1 - Polynomial.X : Polynomial ℚ).comp (1 - Polynomial.X) = Polynomial.X := by
    simp only [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp]
    ring
  rw [h, Polynomial.comp_X]

/-- The complementary coordinate keeps the same rational function after
reflecting its actual numerator and denominator. -/
theorem rationalReflection_fraction {K : Type*} [Field K] [Algebra ℚ K]
    (x : K) (p q : Polynomial ℚ) :
    Polynomial.aeval (1 - x) (rationalReflection p) /
        Polynomial.aeval (1 - x) (rationalReflection q) =
      Polynomial.aeval x p / Polynomial.aeval x q := by
  rw [rationalReflection_aeval, rationalReflection_aeval]
  have h : (1 : K) - (1 - x) = x := by ring
  rw [h]

/-- Complementing a rational root and applying either orientation sign
preserves a consecutive integral interval of the same length. -/
theorem signed_complement_integer_interval (η δ : ℤ)
    (hη : η = 1 ∨ η = -1) (hδ : δ = 1 ∨ δ = -1) (origin limit : ℕ) :
    ∃ start : ℤ, ∀ k : ℕ, k ≤ limit → ∃ j : ℕ, j ≤ limit ∧
      (η : ℚ) * (1 - (δ : ℚ) * ((k : ℚ) - (origin : ℚ))) =
        (start : ℚ) + (j : ℚ) := by
  rcases hη with rfl | rfl <;> rcases hδ with rfl | rfl
  · refine ⟨1 + (origin : ℤ) - (limit : ℤ), fun k hk => ⟨limit - k, Nat.sub_le _ _, ?_⟩⟩
    have hs : ((limit - k : ℕ) : ℚ) = (limit : ℚ) - (k : ℚ) := Nat.cast_sub hk
    push_cast
    rw [hs]
    ring
  · refine ⟨1 - (origin : ℤ), fun k hk => ⟨k, hk, ?_⟩⟩
    push_cast
    ring
  · refine ⟨-1 - (origin : ℤ), fun k hk => ⟨k, hk, ?_⟩⟩
    push_cast
    ring
  · refine ⟨-1 + (origin : ℤ) - (limit : ℤ),
      fun k hk => ⟨limit - k, Nat.sub_le _ _, ?_⟩⟩
    have hs : ((limit - k : ℕ) : ℚ) = (limit : ℚ) - (k : ℚ) := Nat.cast_sub hk
    push_cast
    rw [hs]
    ring

end SkewCornerDescent
