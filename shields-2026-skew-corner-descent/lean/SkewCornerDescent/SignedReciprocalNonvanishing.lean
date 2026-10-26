/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TranscendentalRationalFunctions
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Nonvanishing of signed rational reciprocal families

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). A nontrivial
finite integer-weighted reciprocal family cannot vanish at a transcendental
rational coordinate. Clearing denominators and evaluating at a retained root
proves nonvanishing without assuming any sign of the weights. Sorry-free.
-/

namespace SkewCornerDescent

open scoped BigOperators

private noncomputable def reciprocalNumerator (s : Finset ℚ) (e : ℚ → ℤ) : Polynomial ℚ :=
  ∑ α ∈ s, Polynomial.C (e α : ℚ) * ∏ β ∈ s.erase α, (Polynomial.X - Polynomial.C β)

private theorem reciprocalNumerator_eval (s : Finset ℚ) (e : ℚ → ℤ)
    (α : ℚ) (hα : α ∈ s) :
    Polynomial.eval α (reciprocalNumerator s e) =
      (e α : ℚ) * ∏ β ∈ s.erase α, (α - β) := by
  classical
  unfold reciprocalNumerator
  rw [Polynomial.eval_finsetSum, Finset.sum_eq_single α]
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X]
  · intro β hβ hne
    have hi : α ∈ s.erase β := Finset.mem_erase.mpr ⟨(fun h => hne h.symm), hα⟩
    have hz : (∏ γ ∈ s.erase β, (α - γ)) = 0 :=
      Finset.prod_eq_zero hi (sub_self α)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, hz, mul_zero]
  · intro hnot
    exact (hnot hα).elim

private theorem reciprocalNumerator_ne_zero (s : Finset ℚ) (e : ℚ → ℤ)
    (hweights : ∃ α ∈ s, e α ≠ 0) : reciprocalNumerator s e ≠ 0 := by
  classical
  obtain ⟨α, hα, he⟩ := hweights
  have hc : (e α : ℚ) ≠ 0 := by exact_mod_cast he
  have hp : (∏ β ∈ s.erase α, (α - β)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro β hβ
    apply sub_ne_zero.mpr
    intro h
    exact (Finset.mem_erase.mp hβ).1 h.symm
  intro hz
  have h := reciprocalNumerator_eval s e α hα
  rw [hz, Polynomial.eval_zero] at h
  exact (mul_ne_zero hc hp) h.symm

theorem transcendental_signed_reciprocal_sum_ne_zero {F : Type*}
    [Field F] [CharZero F] [Algebra ℚ F] (u : F) (hu : Transcendental ℚ u)
    (s : Finset ℚ) (e : ℚ → ℤ) (hweights : ∃ α ∈ s, e α ≠ 0) :
    (∑ α ∈ s, (e α : F) / (u - (α : F))) ≠ 0 := by
  classical
  have hcast (α : ℚ) : algebraMap ℚ F α = (α : F) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ F) α
  have hi := transcendental_iff_injective.mp hu
  have hf (α : ℚ) : u - (α : F) ≠ 0 := by
    intro hz
    have he : Polynomial.aeval u (Polynomial.X - Polynomial.C α) = 0 := by
      simpa only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hcast] using hz
    exact (Polynomial.monic_X_sub_C α).ne_zero (hi (he.trans (map_zero _).symm))
  have hclear : (∑ α ∈ s, (e α : F) / (u - (α : F))) *
      (∏ β ∈ s, (u - (β : F))) = Polynomial.aeval u (reciprocalNumerator s e) := by
    rw [Finset.sum_mul]
    simp only [reciprocalNumerator, map_sum, map_mul, map_prod, map_sub,
      Polynomial.aeval_C, Polynomial.aeval_X, hcast, Rat.cast_intCast]
    apply Finset.sum_congr rfl
    intro α hα
    rw [← Finset.mul_prod_erase s _ hα]
    field_simp [hf α]
  intro hz
  rw [hz, zero_mul] at hclear
  exact reciprocalNumerator_ne_zero s e hweights (hi (hclear.symm.trans (map_zero _).symm))

end SkewCornerDescent
