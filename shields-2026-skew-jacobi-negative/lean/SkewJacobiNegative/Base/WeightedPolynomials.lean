/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib

/-!
# Lowest-weight components of polynomials

Formalizes «Convex valuations» (`subsec:valuations`, `lem:valuation-laws`) in
`shields-2026-skew-schur-reconstruction.tex`.  The weight may be any real additive
monomial weight.  Initial forms retain their coefficients and do not collapse distinct
monomials of equal weight.  Sorry-free.
-/

namespace SkewJacobiNegative.Base

open MvPolynomial
open scoped BigOperators

variable {σ R : Type*} [CommRing R]

/-- Every occupied monomial has weight at least `a`. -/
def WeightLowerBound (w : σ → ℝ) (p : MvPolynomial σ R) (a : ℝ) : Prop :=
  ∀ d, p.coeff d ≠ 0 → a ≤ Finsupp.weight w d

/-- Lowest real weight of a nonzero polynomial; the zero value is used only for projection. -/
noncomputable def leastWeight (w : σ → ℝ) (p : MvPolynomial σ R) : ℝ :=
  if hp : p.support.Nonempty then p.support.inf' hp (Finsupp.weight w) else 0

/-- The valuation of zero is infinity, not the projection's auxiliary zero value. -/
noncomputable def monomialValuation (w : σ → ℝ) (p : MvPolynomial σ R) : WithTop ℝ :=
  p.support.inf fun d => (Finsupp.weight w d : WithTop ℝ)

/-- The initial form is a genuine polynomial component, retaining every tied monomial. -/
noncomputable def initialForm (w : σ → ℝ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  weightedHomogeneousComponent w (leastWeight w p) p

@[simp]
theorem monomialValuation_zero (w : σ → ℝ) :
    monomialValuation w (0 : MvPolynomial σ R) = ⊤ := by
  simp [monomialValuation]

@[simp]
theorem initialForm_zero (w : σ → ℝ) : initialForm w (0 : MvPolynomial σ R) = 0 := by
  simp [initialForm]

/-- Finite-support infimum agrees with the real least weight away from zero. -/
theorem monomialValuation_eq_coe {w : σ → ℝ} {p : MvPolynomial σ R} (hp : p ≠ 0) :
    monomialValuation w p = (leastWeight w p : WithTop ℝ) := by
  have hs := support_nonempty.mpr hp
  rw [leastWeight, dite_eq_left hs]
  exact (Finset.coe_inf' hs (Finsupp.weight w)).symm

theorem leastWeight_lowerBound (w : σ → ℝ) (p : MvPolynomial σ R) :
    WeightLowerBound w p (leastWeight w p) := by
  classical
  intro d hd
  have hmem : d ∈ p.support := mem_support_iff.mpr hd
  rw [leastWeight, dite_eq_left ⟨d, hmem⟩]
  exact Finset.inf'_le (Finsupp.weight w) hmem

/-- A nonzero polynomial has an occupied monomial at its least weight. -/
theorem exists_leastWeight_monomial {w : σ → ℝ} {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ∃ d, p.coeff d ≠ 0 ∧ Finsupp.weight w d = leastWeight w p := by
  classical
  obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_inf p.support (support_nonempty.mpr hp)
    (fun d => (Finsupp.weight w d : WithTop ℝ))
  refine ⟨d, mem_support_iff.mp hd, ?_⟩
  have hc : (leastWeight w p : WithTop ℝ) = (Finsupp.weight w d : WithTop ℝ) :=
    (monomialValuation_eq_coe hp).symm.trans he
  exact (WithTop.coe_injective hc).symm

/-- The initial form cannot disappear by combining equal-weight but distinct monomials. -/
theorem initialForm_ne_zero {w : σ → ℝ} {p : MvPolynomial σ R} (hp : p ≠ 0) :
    initialForm w p ≠ 0 := by
  classical
  obtain ⟨d, hd, hw⟩ := exists_leastWeight_monomial (w := w) hp
  apply ne_zero_iff.mpr
  refine ⟨d, ?_⟩
  rw [initialForm, coeff_weightedHomogeneousComponent, ite_eq_left hw]
  exact hd

/-- At the sum of two lower bounds, convolution uses only the corresponding components. -/
theorem lowest_component_mul {w : σ → ℝ} {p q : MvPolynomial σ R} {a b : ℝ}
    (hp : WeightLowerBound w p a) (hq : WeightLowerBound w q b) :
    weightedHomogeneousComponent w (a + b) (p * q) =
      weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent, coeff_mul]
  by_cases hd : Finsupp.weight w d = a + b
  · simp only [hd, ite_true]
    apply Finset.sum_congr rfl
    intro uv huv
    have hsum : uv.1 + uv.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    by_cases hpu : p.coeff uv.1 = 0
    · simp [hpu]
    by_cases hqv : q.coeff uv.2 = 0
    · simp [hqv]
    have hwa := hp uv.1 hpu
    have hwb := hq uv.2 hqv
    have hw : Finsupp.weight w uv.1 + Finsupp.weight w uv.2 = a + b := by
      rw [← map_add, hsum, hd]
    have hua : Finsupp.weight w uv.1 = a := by linarith
    have hvb : Finsupp.weight w uv.2 = b := by linarith
    simp [hua, hvb]
  · simp only [hd, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro uv huv
    have hsum : uv.1 + uv.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    by_cases hua : Finsupp.weight w uv.1 = a
    · have hvb : Finsupp.weight w uv.2 ≠ b := by
        intro hvb
        apply hd
        rw [← hsum, map_add, hua, hvb]
      simp [hua, hvb]
    · simp [hua]

/-- Convolution cannot introduce a monomial below the sum of two lower bounds. -/
theorem WeightLowerBound.mul {w : σ → ℝ} {p q : MvPolynomial σ R} {a b : ℝ}
    (hp : WeightLowerBound w p a) (hq : WeightLowerBound w q b) :
    WeightLowerBound w (p * q) (a + b) := by
  classical
  intro d hd
  rw [coeff_mul] at hd
  obtain ⟨uv, huv, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have hsum : uv.1 + uv.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  rw [← hsum, map_add]
  exact add_le_add (hp _ (left_ne_zero_of_mul hprod)) (hq _ (right_ne_zero_of_mul hprod))

/-- A nonzero component at a lower bound identifies the least weight exactly. -/
theorem leastWeight_eq_of_component {w : σ → ℝ} {p : MvPolynomial σ R} {a : ℝ}
    (hp : WeightLowerBound w p a) (hc : weightedHomogeneousComponent w a p ≠ 0) :
    leastWeight w p = a := by
  classical
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hc
  have hw : Finsupp.weight w d = a := by
    by_contra hne
    rw [coeff_weightedHomogeneousComponent, ite_eq_right hne] at hd
    exact hd rfl
  rw [coeff_weightedHomogeneousComponent, ite_eq_left hw] at hd
  have hs : p.support.Nonempty := ⟨d, mem_support_iff.mpr hd⟩
  rw [leastWeight, dite_eq_left hs]
  apply le_antisymm
  · exact (Finset.inf'_le (Finsupp.weight w) (mem_support_iff.mpr hd)).trans_eq hw
  · exact (Finset.le_inf'_iff hs (Finsupp.weight w)).mpr fun e he =>
      hp e (mem_support_iff.mp he)

section Domain

variable [IsDomain R]

/-- The two genuine initial components multiply without cancellation in an integral domain. -/
theorem leastWeight_mul {w : σ → ℝ} {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    leastWeight w (p * q) = leastWeight w p + leastWeight w q := by
  apply leastWeight_eq_of_component
    ((leastWeight_lowerBound w p).mul (leastWeight_lowerBound w q))
  rw [lowest_component_mul (leastWeight_lowerBound w p) (leastWeight_lowerBound w q)]
  exact mul_ne_zero (initialForm_ne_zero hp) (initialForm_ne_zero hq)

/-- Initial forms multiply as polynomials, rather than as coefficient-collapsed series. -/
theorem initialForm_mul {w : σ → ℝ} {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    initialForm w (p * q) = initialForm w p * initialForm w q := by
  unfold initialForm
  rw [leastWeight_mul hp hq]
  exact lowest_component_mul (leastWeight_lowerBound w p) (leastWeight_lowerBound w q)

/-- Multiplicativity of the convex valuation in `lem:valuation-laws`, including zero. -/
theorem monomialValuation_mul (w : σ → ℝ) (p q : MvPolynomial σ R) :
    monomialValuation w (p * q) = monomialValuation w p + monomialValuation w q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [monomialValuation_eq_coe (mul_ne_zero hp hq), monomialValuation_eq_coe hp,
    monomialValuation_eq_coe hq, leastWeight_mul hp hq, WithTop.coe_add]

end Domain

/-- Zero is the only polynomial of infinite valuation. -/
theorem monomialValuation_eq_top_iff (w : σ → ℝ) (p : MvPolynomial σ R) :
    monomialValuation w p = ⊤ ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    rw [monomialValuation_eq_coe hp] at h
    exact WithTop.coe_ne_top h
  · rintro rfl
    exact monomialValuation_zero w

/-- The lower bound for sums in `lem:valuation-laws`, valid even when terms cancel. -/
theorem monomialValuation_add_ge (w : σ → ℝ) (p q : MvPolynomial σ R) :
    min (monomialValuation w p) (monomialValuation w q) ≤
      monomialValuation w (p + q) := by
  classical
  apply Finset.le_inf
  intro d hd
  have hc : p.coeff d + q.coeff d ≠ 0 := by simpa using mem_support_iff.mp hd
  by_cases hp : p.coeff d = 0
  · have hq : q.coeff d ≠ 0 := by simpa [hp] using hc
    exact (min_le_right _ _).trans (Finset.inf_le (mem_support_iff.mpr hq))
  · exact (min_le_left _ _).trans (Finset.inf_le (mem_support_iff.mpr hp))

/-- Every occupied monomial is strictly above `a`. -/
def WeightStrictLowerBound (w : σ → ℝ) (p : MvPolynomial σ R) (a : ℝ) : Prop :=
  ∀ d, p.coeff d ≠ 0 → a < Finsupp.weight w d

theorem WeightStrictLowerBound.le {w : σ → ℝ} {p : MvPolynomial σ R} {a : ℝ}
    (hp : WeightStrictLowerBound w p a) : WeightLowerBound w p a :=
  fun d hd => (hp d hd).le

theorem WeightLowerBound.add {w : σ → ℝ} {p q : MvPolynomial σ R} {a : ℝ}
    (hp : WeightLowerBound w p a) (hq : WeightLowerBound w q a) :
    WeightLowerBound w (p + q) a := by
  intro d hd
  by_cases hpd : p.coeff d = 0
  · apply hq d
    change p.coeff d + q.coeff d ≠ 0 at hd
    simpa only [hpd, zero_add] using hd
  · exact hp d hpd

/-- A component strictly below the support vanishes coefficient by coefficient. -/
theorem component_eq_zero_of_strict_lowerBound {w : σ → ℝ} {p : MvPolynomial σ R}
    {a : ℝ} (hp : WeightStrictLowerBound w p a) :
    weightedHomogeneousComponent w a p = 0 := by
  classical
  ext d
  by_cases hw : Finsupp.weight w d = a
  · have hd : p.coeff d = 0 := by
      by_contra hne
      have h := hp d hne
      rw [hw] at h
      exact (lt_irrefl a) h
    simp [coeff_weightedHomogeneousComponent, hd]
  · simp [coeff_weightedHomogeneousComponent, hw]

/-- A higher-weight perturbation cannot remove the lower initial component. -/
theorem leastWeight_add_eq_left {w : σ → ℝ} {p q : MvPolynomial σ R} (hp : p ≠ 0)
    (hq : WeightStrictLowerBound w q (leastWeight w p)) :
    leastWeight w (p + q) = leastWeight w p := by
  apply leastWeight_eq_of_component ((leastWeight_lowerBound w p).add hq.le)
  rw [map_add, component_eq_zero_of_strict_lowerBound hq, add_zero]
  exact initialForm_ne_zero hp

/-- The initial polynomial survives a perturbation with strictly higher occupied weights. -/
theorem initialForm_add_eq_left {w : σ → ℝ} {p q : MvPolynomial σ R} (hp : p ≠ 0)
    (hq : WeightStrictLowerBound w q (leastWeight w p)) :
    initialForm w (p + q) = initialForm w p := by
  unfold initialForm
  rw [leastWeight_add_eq_left hp hq, map_add,
    component_eq_zero_of_strict_lowerBound hq, add_zero]

/-- Comparing finite support to a valuation bound gives a strict support bound. -/
theorem strict_lowerBound_of_valuation_lt {w : σ → ℝ} {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hlt : monomialValuation w p < monomialValuation w q) :
    WeightStrictLowerBound w q (leastWeight w p) := by
  classical
  intro d hd
  have hm : d ∈ q.support := mem_support_iff.mpr hd
  have hc := hlt.trans_le (Finset.inf_le hm)
  rw [monomialValuation_eq_coe hp] at hc
  exact WithTop.coe_lt_coe.mp hc

/-- Unequal valuations cannot cancel the term with lower valuation. -/
theorem monomialValuation_add_eq_left {w : σ → ℝ} {p q : MvPolynomial σ R}
    (hlt : monomialValuation w p < monomialValuation w q) :
    monomialValuation w (p + q) = monomialValuation w p := by
  have hp : p ≠ 0 := by
    intro h
    rw [h, monomialValuation_zero] at hlt
    exact (not_top_lt hlt)
  have hq := strict_lowerBound_of_valuation_lt hp hlt
  have hi := initialForm_add_eq_left hp hq
  have hsum : p + q ≠ 0 := by
    intro hz
    apply initialForm_ne_zero hp
    rw [← hi, hz, initialForm_zero]
  rw [monomialValuation_eq_coe hsum, leastWeight_add_eq_left hp hq,
    monomialValuation_eq_coe hp]

/-- The equality case for unequal valuations in `lem:valuation-laws`. -/
theorem monomialValuation_add_eq_min {w : σ → ℝ} {p q : MvPolynomial σ R}
    (hne : monomialValuation w p ≠ monomialValuation w q) :
    monomialValuation w (p + q) = min (monomialValuation w p) (monomialValuation w q) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [monomialValuation_add_eq_left hlt, min_eq_left hlt.le]
  · rw [add_comm, monomialValuation_add_eq_left hgt, min_eq_right hgt.le]

/-- Finite sums of strict higher-weight terms remain strictly above the same bound. -/
theorem strict_lowerBound_sum {ι : Type*} {w : σ → ℝ} {a : ℝ}
    (s : Finset ι) (f : ι → MvPolynomial σ R)
    (hf : ∀ i ∈ s, WeightStrictLowerBound w (f i) a) :
    WeightStrictLowerBound w (∑ i ∈ s, f i) a := by
  classical
  intro d hd
  rw [coeff_sum] at hd
  obtain ⟨i, hi, hcoeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  exact hf i hi d hcoeff

/-- A uniquely lowest summand controls both the initial form and the least weight. -/
theorem initialForm_sum_unique {ι : Type*} {w : σ → ℝ}
    (s : Finset ι) (f : ι → MvPolynomial σ R) {i : ι} (hi : i ∈ s) (hfi : f i ≠ 0)
    (hmin : ∀ j ∈ s, j ≠ i → monomialValuation w (f i) < monomialValuation w (f j)) :
    initialForm w (∑ j ∈ s, f j) = initialForm w (f i) ∧
      leastWeight w (∑ j ∈ s, f j) = leastWeight w (f i) := by
  classical
  have hrest : WeightStrictLowerBound w (∑ j ∈ s.erase i, f j) (leastWeight w (f i)) := by
    apply strict_lowerBound_sum
    intro j hj
    exact strict_lowerBound_of_valuation_lt hfi
      (hmin j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj))
  rw [← Finset.add_sum_erase s f hi]
  exact ⟨initialForm_add_eq_left hfi hrest, leastWeight_add_eq_left hfi hrest⟩

/-- A polynomial sum with one strictly lowest summand is nonzero. -/
theorem sum_ne_zero_of_unique_min {ι : Type*} {w : σ → ℝ}
    (s : Finset ι) (f : ι → MvPolynomial σ R) {i : ι} (hi : i ∈ s) (hfi : f i ≠ 0)
    (hmin : ∀ j ∈ s, j ≠ i → monomialValuation w (f i) < monomialValuation w (f j)) :
    (∑ j ∈ s, f j) ≠ 0 := by
  intro hz
  have h := (initialForm_sum_unique s f hi hfi hmin).1
  rw [hz, initialForm_zero] at h
  exact initialForm_ne_zero hfi h.symm

/-- An exact zero relation cannot have a unique finite valuation minimum. -/
theorem exists_second_minimizer_of_sum_zero {ι : Type*} {w : σ → ℝ}
    (s : Finset ι) (f : ι → MvPolynomial σ R) {i : ι} (hi : i ∈ s) (hfi : f i ≠ 0)
    (hzero : ∑ j ∈ s, f j = 0)
    (hmin : ∀ j ∈ s, monomialValuation w (f i) ≤ monomialValuation w (f j)) :
    ∃ j ∈ s, j ≠ i ∧ monomialValuation w (f j) = monomialValuation w (f i) := by
  classical
  by_contra hnone
  apply sum_ne_zero_of_unique_min (w := w) s f hi hfi ?_ hzero
  intro j hj hji
  apply lt_of_le_of_ne (hmin j hj)
  intro heq
  exact hnone ⟨j, hj, hji, heq.symm⟩

@[simp]
theorem monomialValuation_neg (w : σ → ℝ) (p : MvPolynomial σ R) :
    monomialValuation w (-p) = monomialValuation w p := by
  simp [monomialValuation]

/-- Cancellation in a difference can only raise the lower parent valuation. -/
theorem monomialValuation_sub_ge (w : σ → ℝ) (p q : MvPolynomial σ R) :
    min (monomialValuation w p) (monomialValuation w q) ≤
      monomialValuation w (p - q) := by
  simpa only [sub_eq_add_neg, monomialValuation_neg] using monomialValuation_add_ge w p (-q)

/-- Different parent valuations give a nonzero defect with the lower parent's valuation. -/
theorem monomialValuation_sub_eq_min {w : σ → ℝ} {p q : MvPolynomial σ R}
    (hne : monomialValuation w p ≠ monomialValuation w q) :
    monomialValuation w (p - q) = min (monomialValuation w p) (monomialValuation w q) := by
  have hn : monomialValuation w p ≠ monomialValuation w (-q) := by simpa using hne
  simpa only [sub_eq_add_neg, monomialValuation_neg] using monomialValuation_add_eq_min hn

end SkewJacobiNegative.Base
