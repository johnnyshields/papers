/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.RegularFractionExpressions
import SkewCornerDescent.FilteredClosureWindows

/-!
# Nonvanishing dependent reciprocal inventories

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). A regular
positive assignment of the same actual rational responses witnesses nonvanishing
of any inhabited finite inverse-product inventory. No independence of response
variables is assumed. Sorry-free.
-/

namespace SkewCornerDescent

open scoped BigOperators

/-- A common positive regular specialization rules out cancellation in a finite
nonempty inverse-product sum. Repeated occurrences remain distinct positions. -/
theorem sum_prod_inv_ne_zero_of_positive_specialization {ι σ τ R F : Type*}
    [CommRing R] [Field F] (ιR : R →+* F) (φ : R →+* ℝ)
    (hι : Function.Injective ιR) (num den : τ → R)
    (hnF : ∀ a, ιR (num a) ≠ 0) (hpos : ∀ a, 0 < φ (num a) / φ (den a))
    (s : Finset ι) (hs : s.Nonempty) (positions : ι → Finset σ) (letter : ι → σ → τ) :
    (∑ i ∈ s, ∏ j ∈ positions i, (ιR (num (letter i j)) / ιR (den (letter i j)))⁻¹) ≠ 0 := by
  classical
  let P : MvPolynomial τ R :=
    ∑ i ∈ s, ∏ j ∈ positions i, MvPolynomial.X (letter i j)
  have hpositive : 0 < ∑ i ∈ s,
      ∏ j ∈ positions i, (φ (num (letter i j)) / φ (den (letter i j)))⁻¹ := by
    apply Finset.sum_pos
    · intro i _
      exact Finset.prod_pos fun j _ => inv_pos.mpr (hpos (letter i j))
    · exact hs
  intro hz
  have hsource : P.eval₂ ιR (fun a => ιR (den a) / ιR (num a)) = 0 := by
    simpa [P, inv_div] using hz
  have hnum : ∀ a, φ (num a) ≠ 0 := by
    intro a hz
    have hp := hpos a
    rw [hz, zero_div] at hp
    exact (lt_irrefl _ hp)
  have ht := eval₂_fraction_zero_transfer ιR φ hι den num hnF hnum P hsource
  have ht' : (∑ i ∈ s,
      ∏ j ∈ positions i, (φ (num (letter i j)) / φ (den (letter i j)))⁻¹) = 0 := by
    simpa [P, inv_div] using ht
  exact (ne_of_gt hpositive) ht'

end SkewCornerDescent
