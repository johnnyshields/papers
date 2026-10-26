/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.RegularFractionExpressions
import SkewCornerDescent.CyclicDetectors

/-!
# Regular specialization of every complete literal window detector

Supports `shields-2026-skew-corner-descent.tex` (`lem:positive-support`). The
complete detector is a polynomial in inverse response values. Its literal
positions, cyclic starts, closures and signed integer coefficients are retained
when transferring a zero identity through one regular finite specialization.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

/-- The complete polynomial inventory in inverse response coordinates. -/
noncomputable def windowDefectPolynomial {α R : Type*} [Fintype α] [CommRing R]
    {n B : ℕ} [NeZero n] [NeZero B] (word : ZMod n → α)
    (e : α → ℤ) (b j : ℕ) : MvPolynomial α R :=
  MvPolynomial.C (b : R) *
      (∑ i : ZMod n, ∏ a ∈ Finset.range j, MvPolynomial.X (word (i + a • 1))) -
    ∑ X, MvPolynomial.C (e X : R) *
      (∑ i : ZMod B, ∏ a ∈ Finset.range j,
        MvPolynomial.X (closureWord word X B (i + a • 1)))

private theorem response_closure {α F : Type*} {n B : ℕ}
    (response : α → F) (word : ZMod n → α) (X : α) (i : ZMod B) :
    response (closureWord word X B i) = closureWord (response ∘ word) (response X) B i := by
  unfold closureWord
  split_ifs <;> rfl

private theorem inverse_response_closure {α F : Type*} [Inv F] {n B : ℕ}
    (response : α → F) (word : ZMod n → α) (X : α) (i : ZMod B) :
    (response (closureWord word X B i))⁻¹ =
      (closureWord (response ∘ word) (response X) B i)⁻¹ :=
  congrArg Inv.inv (response_closure response word X i)

/-- Evaluation at the actual inverse responses gives the literal detector. -/
theorem windowDefectPolynomial_eval {α R F : Type*}
    [Fintype α] [CommRing R] [Field F] {n B : ℕ} [NeZero n] [NeZero B]
    (φ : R →+* F) (word : ZMod n → α) (e : α → ℤ) (b j : ℕ) (response : α → F) :
    (windowDefectPolynomial (B := B) word e b j).eval₂ φ (fun X => (response X)⁻¹) =
      windowDefect (response ∘ word) response e b B j := by
  classical
  simp only [windowDefectPolynomial, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X]
  simp only [map_natCast, map_intCast, inverse_response_closure,
    windowDefect, inverseWindowSum, windowProduct, Function.comp_apply, Finset.prod_inv_distrib]

/-- A zero complete original detector transfers through the finite regular
fraction expressions. No specialization of the entire source field is assumed. -/
theorem windowDefect_zero_specialize {α R F K : Type*}
    [Fintype α] [CommRing R] [Field F] [Field K]
    {n B : ℕ} [NeZero n] [NeZero B]
    (ι : R →+* F) (φ : R →+* K) (hι : Function.Injective ι)
    (num den : α → R) (hnF : ∀ X, ι (num X) ≠ 0) (hnK : ∀ X, φ (num X) ≠ 0)
    (word : ZMod n → α) (e : α → ℤ) (b j : ℕ)
    (hzero : windowDefect ((fun X => ι (num X) / ι (den X)) ∘ word)
      (fun X => ι (num X) / ι (den X)) e b B j = 0) :
    windowDefect ((fun X => φ (num X) / φ (den X)) ∘ word)
      (fun X => φ (num X) / φ (den X)) e b B j = 0 := by
  let P : MvPolynomial α R := windowDefectPolynomial (B := B) word e b j
  have hsource : P.eval₂ ι (fun X => ι (den X) / ι (num X)) = 0 := by
    rw [← windowDefectPolynomial_eval ι word e b j] at hzero
    simpa only [inv_div] using hzero
  have ht := eval₂_fraction_zero_transfer ι φ hι den num hnF hnK P hsource
  rw [← windowDefectPolynomial_eval φ word e b j]
  simpa only [inv_div] using ht

end SkewCornerDescent.CyclicWindows
