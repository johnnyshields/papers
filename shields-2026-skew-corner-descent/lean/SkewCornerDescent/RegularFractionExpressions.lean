/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-!
# Regular specialization of dependent fraction expressions

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`, `lem:peeling`).
A finite polynomial expression in actual dependent fractions has one common numerator and
regular denominator before and after specialization. Its expression variables encode operations,
not an algebraic independence assumption on the responses. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

/-- Clear the same finite expression over both fields. Denominators are produced inductively
from the actual response denominators, so specialization requires no map of the full field. -/
theorem eval₂_fraction_representative {σ R F K : Type*}
    [CommRing R] [Field F] [Field K] (ι : R →+* F) (φ : R →+* K)
    (num den : σ → R) (hF : ∀ i, ι (den i) ≠ 0) (hK : ∀ i, φ (den i) ≠ 0)
    (P : MvPolynomial σ R) :
    ∃ a b : R, ι b ≠ 0 ∧ φ b ≠ 0 ∧
      P.eval₂ ι (fun i => ι (num i) / ι (den i)) = ι a / ι b ∧
      P.eval₂ φ (fun i => φ (num i) / φ (den i)) = φ a / φ b := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨c, 1, by simp, by simp, by simp, by simp⟩
  | add P Q hP hQ =>
    obtain ⟨a, b, hbF, hbK, hPF, hPK⟩ := hP
    obtain ⟨c, d, hdF, hdK, hQF, hQK⟩ := hQ
    refine ⟨a * d + b * c, b * d, ?_, ?_, ?_, ?_⟩
    · simpa only [map_mul] using mul_ne_zero hbF hdF
    · simpa only [map_mul] using mul_ne_zero hbK hdK
    · rw [eval₂_add, hPF, hQF, map_add, map_mul, map_mul, map_mul]
      exact div_add_div _ _ hbF hdF
    · rw [eval₂_add, hPK, hQK, map_add, map_mul, map_mul, map_mul]
      exact div_add_div _ _ hbK hdK
  | mul_X P i hP =>
    obtain ⟨a, b, hbF, hbK, hPF, hPK⟩ := hP
    refine ⟨a * num i, b * den i, ?_, ?_, ?_, ?_⟩
    · simpa only [map_mul] using mul_ne_zero hbF (hF i)
    · simpa only [map_mul] using mul_ne_zero hbK (hK i)
    · rw [eval₂_mul, eval₂_X, hPF, map_mul, map_mul, div_mul_div_comm]
    · rw [eval₂_mul, eval₂_X, hPK, map_mul, map_mul, div_mul_div_comm]

/-- A zero identity among dependent fractions survives any regular specialization.
Injectivity is required only into the original field, never for the specialized coordinate map. -/
theorem eval₂_fraction_zero_transfer {σ R F K : Type*}
    [CommRing R] [Field F] [Field K] (ι : R →+* F) (φ : R →+* K)
    (hι : Function.Injective ι) (num den : σ → R)
    (hF : ∀ i, ι (den i) ≠ 0) (hK : ∀ i, φ (den i) ≠ 0)
    (P : MvPolynomial σ R)
    (hzero : P.eval₂ ι (fun i => ι (num i) / ι (den i)) = 0) :
    P.eval₂ φ (fun i => φ (num i) / φ (den i)) = 0 := by
  obtain ⟨a, b, hbF, hbK, hPF, hPK⟩ :=
    eval₂_fraction_representative ι φ num den hF hK P
  rw [hPF, div_eq_zero_iff] at hzero
  have ha : a = 0 := hι ((hzero.resolve_right hbF).trans ι.map_zero.symm)
  rw [hPK, ha, map_zero, zero_div]

end SkewCornerDescent
