-- TODO-COPIED: skew-cofactor-independence/lean/SkewCofactorIndependence/Base/GeneratorProducts.lean
/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/GeneratorProducts.lean
import SkewCofactorIndependence.Base.CompleteRing
import SkewCofactorIndependence.Base.ConvexWeights
import SkewCofactorIndependence.Base.WeightedPolynomials

/-!
# Weights of complete-generator products

Formalizes determinant-term weights in "Strict-Monge geometry of cofactor actions"
(`sec:geometry`, `subsec:valuations`, `lem:valuation-laws`) and the generator
products in "Reconstruction from two boundary observations" (`sec:reconstruction`).  Nonnegative
subscripts give nonzero homogeneous products, including index-zero factors.
Their initial forms, real least weights, finite valuations, ordinary degrees,
and positive-generator factor counts are exact.  Sorry-free.
-/

namespace SkewCofactorIndependence.Base

open MvPolynomial
open scoped BigOperators

namespace ConvexWeight

/-- The weight of each positive complete generator. -/
def generatorWeight (w : ConvexWeight) (k : ℕ+) : ℝ := w.weight (k : ℕ)

end ConvexWeight

/-- Any additive grading of nonnegative complete subscripts which assigns zero to `h₀`. -/
theorem complete_isWeightedHomogeneous {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (hf : f 0 = 0) (a : ℤ) (ha : 0 ≤ a) :
    IsWeightedHomogeneous (fun k : ℕ+ => f (k : ℕ)) (complete a) (f a.toNat) := by
  by_cases hz : a = 0
  · subst a
    rw [complete_zero, Int.toNat_zero, hf]
    exact isWeightedHomogeneous_one ℤ _
  · have hp : 0 < a := by omega
    rw [complete_of_pos hp]
    exact isWeightedHomogeneous_X ℤ _ _

/-- A nonnegative complete generator is never zero, including `h₀ = 1`. -/
theorem complete_ne_zero_of_nonneg (a : ℤ) (ha : 0 ≤ a) : complete a ≠ 0 :=
  (complete_ne_zero_iff a).mpr ha

/-- A nonzero real-weight homogeneous polynomial has its homogeneous degree as least weight. -/
theorem leastWeight_eq_of_homogeneous {σ R : Type*} [CommRing R]
    {v : σ → ℝ} {p : MvPolynomial σ R} {d : ℝ}
    (hp : p ≠ 0) (hd : IsWeightedHomogeneous v p d) : leastWeight v p = d := by
  obtain ⟨e, he, hw⟩ := exists_leastWeight_monomial (w := v) hp
  exact hw.symm.trans (hd he)

/-- The initial form of a nonzero homogeneous polynomial is the polynomial itself. -/
theorem initialForm_eq_of_homogeneous {σ R : Type*} [CommRing R]
    {v : σ → ℝ} {p : MvPolynomial σ R} {d : ℝ}
    (hp : p ≠ 0) (hd : IsWeightedHomogeneous v p d) : initialForm v p = p := by
  rw [initialForm, leastWeight_eq_of_homogeneous hp hd]
  exact hd.weightedHomogeneousComponent_same

/-- The valuation of a nonzero homogeneous polynomial is its finite homogeneous degree. -/
theorem monomialValuation_eq_of_homogeneous {σ R : Type*} [CommRing R]
    {v : σ → ℝ} {p : MvPolynomial σ R} {d : ℝ}
    (hp : p ≠ 0) (hd : IsWeightedHomogeneous v p d) :
    monomialValuation v p = (d : WithTop ℝ) := by
  rw [monomialValuation_eq_coe hp, leastWeight_eq_of_homogeneous hp hd]

theorem complete_convex_homogeneous (w : ConvexWeight) (a : ℤ) (ha : 0 ≤ a) :
    IsWeightedHomogeneous w.generatorWeight (complete a) (w.weight a.toNat) :=
  complete_isWeightedHomogeneous w.weight w.zero a ha

theorem complete_leastWeight (w : ConvexWeight) (a : ℤ) (ha : 0 ≤ a) :
    leastWeight w.generatorWeight (complete a) = w.weight a.toNat :=
  leastWeight_eq_of_homogeneous (complete_ne_zero_of_nonneg a ha)
    (complete_convex_homogeneous w a ha)

theorem complete_initialForm (w : ConvexWeight) (a : ℤ) (ha : 0 ≤ a) :
    initialForm w.generatorWeight (complete a) = complete a :=
  initialForm_eq_of_homogeneous (complete_ne_zero_of_nonneg a ha)
    (complete_convex_homogeneous w a ha)

theorem complete_monomialValuation (w : ConvexWeight) (a : ℤ) (ha : 0 ≤ a) :
    monomialValuation w.generatorWeight (complete a) =
      (w.weight a.toNat : WithTop ℝ) :=
  monomialValuation_eq_of_homogeneous (complete_ne_zero_of_nonneg a ha)
    (complete_convex_homogeneous w a ha)

section Products

variable {ι : Type*} (s : Finset ι) (a : ι → ℤ)

/-- Finite products inherit any zero-preserving additive grading of the subscripts. -/
theorem complete_prod_isWeightedHomogeneous {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (hf : f 0 = 0) (ha : ∀ i ∈ s, 0 ≤ a i) :
    IsWeightedHomogeneous (fun k : ℕ+ => f (k : ℕ)) (∏ i ∈ s, complete (a i))
      (∑ i ∈ s, f (a i).toNat) := by
  apply IsWeightedHomogeneous.prod
  intro i hi
  exact complete_isWeightedHomogeneous f hf (a i) (ha i hi)

theorem complete_prod_ne_zero (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∏ i ∈ s, complete (a i)) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun i hi => complete_ne_zero_of_nonneg (a i) (ha i hi)

theorem complete_prod_convex_homogeneous (w : ConvexWeight)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    IsWeightedHomogeneous w.generatorWeight (∏ i ∈ s, complete (a i))
      (∑ i ∈ s, w.weight (a i).toNat) :=
  complete_prod_isWeightedHomogeneous s a w.weight w.zero ha

theorem complete_prod_leastWeight (w : ConvexWeight) (ha : ∀ i ∈ s, 0 ≤ a i) :
    leastWeight w.generatorWeight (∏ i ∈ s, complete (a i)) =
      ∑ i ∈ s, w.weight (a i).toNat :=
  leastWeight_eq_of_homogeneous (complete_prod_ne_zero s a ha)
    (complete_prod_convex_homogeneous s a w ha)

theorem complete_prod_initialForm (w : ConvexWeight) (ha : ∀ i ∈ s, 0 ≤ a i) :
    initialForm w.generatorWeight (∏ i ∈ s, complete (a i)) = ∏ i ∈ s, complete (a i) :=
  initialForm_eq_of_homogeneous (complete_prod_ne_zero s a ha)
    (complete_prod_convex_homogeneous s a w ha)

theorem complete_prod_monomialValuation (w : ConvexWeight) (ha : ∀ i ∈ s, 0 ≤ a i) :
    monomialValuation w.generatorWeight (∏ i ∈ s, complete (a i)) =
      ((∑ i ∈ s, w.weight (a i).toNat) : WithTop ℝ) :=
  by
    simpa only [WithTop.coe_sum] using
      monomialValuation_eq_of_homogeneous (complete_prod_ne_zero s a ha)
        (complete_prod_convex_homogeneous s a w ha)

/-- Ordinary complete-function degree assigns degree `k` to `h_k`, not degree one. -/
theorem complete_prod_degree_homogeneous (ha : ∀ i ∈ s, 0 ≤ a i) :
    IsWeightedHomogeneous (fun k : ℕ+ => (k : ℕ)) (∏ i ∈ s, complete (a i))
      (∑ i ∈ s, (a i).toNat) :=
  complete_prod_isWeightedHomogeneous s a id rfl ha

/-- Real-valued ordinary grading, suitable for the least-weight and valuation APIs. -/
theorem complete_prod_real_degree_homogeneous (ha : ∀ i ∈ s, 0 ≤ a i) :
    IsWeightedHomogeneous (fun k : ℕ+ => ((k : ℕ) : ℝ)) (∏ i ∈ s, complete (a i))
      ((∑ i ∈ s, (a i).toNat : ℕ) : ℝ) := by
  simpa only [Nat.cast_sum] using
    complete_prod_isWeightedHomogeneous s a (fun k : ℕ => (k : ℝ)) (by simp) ha

theorem complete_prod_degree_leastWeight (ha : ∀ i ∈ s, 0 ≤ a i) :
    leastWeight (fun k : ℕ+ => ((k : ℕ) : ℝ)) (∏ i ∈ s, complete (a i)) =
      ((∑ i ∈ s, (a i).toNat : ℕ) : ℝ) :=
  leastWeight_eq_of_homogeneous (complete_prod_ne_zero s a ha)
    (complete_prod_real_degree_homogeneous s a ha)

theorem complete_prod_degree_initialForm (ha : ∀ i ∈ s, 0 ≤ a i) :
    initialForm (fun k : ℕ+ => ((k : ℕ) : ℝ)) (∏ i ∈ s, complete (a i)) =
      ∏ i ∈ s, complete (a i) :=
  initialForm_eq_of_homogeneous (complete_prod_ne_zero s a ha)
    (complete_prod_real_degree_homogeneous s a ha)

theorem complete_prod_degree_monomialValuation (ha : ∀ i ∈ s, 0 ≤ a i) :
    monomialValuation (fun k : ℕ+ => ((k : ℕ) : ℝ)) (∏ i ∈ s, complete (a i)) =
      (((∑ i ∈ s, (a i).toNat : ℕ) : ℝ) : WithTop ℝ) :=
  monomialValuation_eq_of_homogeneous (complete_prod_ne_zero s a ha)
    (complete_prod_real_degree_homogeneous s a ha)

/-- Counting polynomial factors uses degree one per positive generator and zero for `h₀`. -/
theorem complete_prod_factorCount_homogeneous (ha : ∀ i ∈ s, 0 ≤ a i) :
    IsWeightedHomogeneous (fun _ : ℕ+ => (1 : ℕ)) (∏ i ∈ s, complete (a i))
      (s.filter (fun i => 0 < a i)).card := by
  classical
  have h := complete_prod_isWeightedHomogeneous s a
    (fun k : ℕ => if k = 0 then (0 : ℕ) else 1) (by simp) ha
  have hf : (fun k : ℕ+ => if (k : ℕ) = 0 then (0 : ℕ) else 1) =
      (fun _ : ℕ+ => (1 : ℕ)) := by
    funext k
    simp [ne_of_gt k.pos]
  rw [hf] at h
  have hs : (∑ i ∈ s, if (a i).toNat = 0 then (0 : ℕ) else 1) =
      (s.filter (fun i => 0 < a i)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    have hn := ha i hi
    by_cases hp : 0 < a i
    · have hnat : (a i).toNat ≠ 0 := by omega
      simp [hp, hnat]
    · have hz : (a i).toNat = 0 := by omega
      simp [hp, hz]
  rw [hs] at h
  exact h

end Products
end SkewCofactorIndependence.Base
