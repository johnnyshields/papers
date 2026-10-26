/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.CompleteAlgebra
import SkewCofactorIndependence.Base.MongeAssignments
import SkewCofactorIndependence.Base.WeightedPolynomials
import SkewCofactorIndependence.Base.GeneratorProducts
import Vendor.AlgebraicCombinatorics.DeterminantsBasic

/-!
# Maximum-square assignments

The maximum, rather than minimum, matching used in `eq:symmetric-leader`.
Both coordinate lists decrease, and the matrix labels are their sums.
Negative square weights make this maximum an ordinary lowest initial form.
-/

namespace SkewCofactorIndependence

open scoped BigOperators
open MvPolynomial

/-- The negative real square weight on the genuine positive generators. -/
def negativeSquareWeight (k : ℕ+) : ℝ := -((k.val : ℝ) ^ 2)

/-- Square cost before its sign is reversed for the polynomial valuation. -/
def squareAssignment {n : ℕ} (a b : Fin n → ℤ) (c : ℤ)
    (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ k, (((a k + b (σ k) - c : ℤ) : ℝ) ^ 2)

private theorem sum_two {n : ℕ} (f : Fin n → ℝ) {i j : Fin n} (h : i ≠ j) :
    (∑ k, f k) = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [h.symm]
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.add_sum_erase (Finset.univ.erase i) f hj]
  ring

/-- Removing an inversion strictly increases the square cost for decreasing lists. -/
theorem square_assignment_swap_lt {n : ℕ} {a b : Fin n → ℤ} (c : ℤ)
    (ha : StrictAnti a) (hb : StrictAnti b) (σ : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i < j) (hinv : σ j < σ i) :
    squareAssignment a b c σ < squareAssignment a b c (Base.uncrossMatching σ i j) := by
  have ha' : (a j : ℝ) < a i := by exact_mod_cast ha hij
  have hb' : (b (σ i) : ℝ) < b (σ j) := by exact_mod_cast hb hinv
  have hp : 0 < ((a i : ℝ) - a j) * ((b (σ j) : ℝ) - b (σ i)) :=
    mul_pos (sub_pos.mpr ha') (sub_pos.mpr hb')
  have hr :
      (∑ k ∈ (Finset.univ.erase i).erase j,
        (((a k + b (Base.uncrossMatching σ i j k) - c : ℤ) : ℝ) ^ 2)) =
      ∑ k ∈ (Finset.univ.erase i).erase j,
        (((a k + b (σ k) - c : ℤ) : ℝ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj := (Finset.mem_erase.mp hk).1
    simp [Base.uncrossMatching_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  unfold squareAssignment
  rw [sum_two _ (ne_of_lt hij), sum_two _ (ne_of_lt hij)]
  rw [hr]
  simp only [Base.uncrossMatching_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  push_cast
  nlinarith

/-- Every square-cost maximizer is the identity assignment. -/
theorem square_assignment_maximizer {n : ℕ} {a b : Fin n → ℤ} (c : ℤ)
    (ha : StrictAnti a) (hb : StrictAnti b) (σ : Equiv.Perm (Fin n))
    (hmax : ∀ τ, squareAssignment a b c τ ≤ squareAssignment a b c σ) :
    σ = Equiv.refl _ := by
  by_contra hne
  obtain ⟨i, j, hij, hinv⟩ := Base.exists_matching_inversion σ hne
  exact (not_lt_of_ge (hmax _)) (square_assignment_swap_lt c ha hb σ hij hinv)

/-- Strict rearrangement, including the empty and singleton assignment boundaries. -/
theorem square_assignment_lt_identity {n : ℕ} {a b : Fin n → ℤ} (c : ℤ)
    (ha : StrictAnti a) (hb : StrictAnti b) (σ : Equiv.Perm (Fin n))
    (hne : σ ≠ Equiv.refl _) :
    squareAssignment a b c σ < squareAssignment a b c (Equiv.refl _) := by
  classical
  obtain ⟨τ, _, hmax⟩ := Set.exists_max_image (Set.univ : Set (Equiv.Perm (Fin n)))
    (squareAssignment a b c) (Set.toFinite _) ⟨Equiv.refl _, Set.mem_univ _⟩
  have ht := square_assignment_maximizer c ha hb τ (fun υ => hmax υ (Set.mem_univ υ))
  subst τ
  obtain ⟨i, j, hij, hinv⟩ := Base.exists_matching_inversion σ hne
  exact (square_assignment_swap_lt c ha hb σ hij hinv).trans_le
    (hmax _ (Set.mem_univ _))

/-- Positive sums become genuine variables, not index-zero units. -/
def positiveSumIndex {n : ℕ} (a b : Fin n → ℤ) (c : ℤ)
    (h : ∀ i j, 0 < a i + b j - c) (i j : Fin n) : ℕ+ :=
  ⟨(a i + b j - c).toNat, by have := h i j; omega⟩

/-- The exponent vector of the identity matching. -/
noncomputable def assignmentExponent {n : ℕ} (a b : Fin n → ℤ) (c : ℤ)
    (h : ∀ i j, 0 < a i + b j - c) : ℕ+ →₀ ℕ :=
  ∑ k, Finsupp.single (positiveSumIndex a b c h k k) 1

private theorem prod_X_eq_monomial {ι : Type*} [Fintype ι] (g : ι → ℕ+) :
    (∏ k, (X (g k) : CompleteRing)) =
      monomial (∑ k, Finsupp.single (g k) 1) 1 := by
  classical
  have h : ∀ s : Finset ι, (∏ k ∈ s, (X (g k) : CompleteRing)) =
      monomial (∑ k ∈ s, Finsupp.single (g k) 1) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
      simp only [Finset.prod_insert hk, Finset.sum_insert hk, ih]
      rw [X, monomial_mul_monomial]
      simp
  simpa using h Finset.univ

private theorem assignment_term_homogeneous {n : ℕ} (a b : Fin n → ℤ) (c : ℤ)
    (h : ∀ i j, 0 < a i + b j - c) (σ : Equiv.Perm (Fin n)) :
    IsWeightedHomogeneous negativeSquareWeight
      (Equiv.Perm.sign σ • ∏ k, complete (a k + b (σ k) - c))
      (-squareAssignment a b c σ) := by
  have hp : IsWeightedHomogeneous negativeSquareWeight
      (∏ k, complete (a k + b (σ k) - c)) (-squareAssignment a b c σ) := by
    have hh := IsWeightedHomogeneous.prod Finset.univ
      (fun k => complete (a k + b (σ k) - c))
      (fun k => -(((a k + b (σ k) - c : ℤ) : ℝ) ^ 2)) (w := negativeSquareWeight)
      (fun k _ => by
        have hz : (((a k + b (σ k) - c).toNat : ℕ) : ℤ) =
            a k + b (σ k) - c := Int.toNat_of_nonneg (h k (σ k)).le
        have hr : (((a k + b (σ k) - c).toNat : ℕ) : ℝ) =
            ((a k + b (σ k) - c : ℤ) : ℝ) := by exact_mod_cast hz
        rw [complete_of_pos (h k (σ k))]
        have hd : negativeSquareWeight (positiveSumIndex a b c h k (σ k)) =
            -(((a k + b (σ k) - c : ℤ) : ℝ) ^ 2) := by
          change -((((a k + b (σ k) - c).toNat : ℕ) : ℝ) ^ 2) = _
          rw [hr]
        have hx := isWeightedHomogeneous_X ℚ negativeSquareWeight
          (positiveSumIndex a b c h k (σ k))
        rw [hd] at hx
        simpa only [positiveSumIndex] using hx)
    simpa [squareAssignment, Finset.sum_neg_distrib] using hh
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using hp.neg

private theorem assignment_term_ne_zero {n : ℕ} (a b : Fin n → ℤ) (c : ℤ)
    (h : ∀ i j, 0 < a i + b j - c) (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign σ • ∏ k, complete (a k + b (σ k) - c)) ≠ 0 := by
  have hp : (∏ k, complete (a k + b (σ k) - c)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact (complete_ne_zero_iff _).2 (h k (σ k)).le
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs] using hp

/-- The actual determinant has the unique maximum-square matching as its initial form. -/
theorem maximum_square_initialForm {n : ℕ} (a b : Fin n → ℤ) (c : ℤ)
    (ha : StrictAnti a) (hb : StrictAnti b)
    (h : ∀ i j, 0 < a i + b j - c) :
    Base.initialForm negativeSquareWeight
      (Matrix.of (fun i j => complete (a i + b j - c))).det =
      monomial (assignmentExponent a b c h) 1 := by
  classical
  let t := fun σ : Equiv.Perm (Fin n) =>
    Equiv.Perm.sign σ • ∏ k, complete (a k + b (σ k) - c)
  have hd : (Matrix.of (fun i j => complete (a i + b j - c))).det = ∑ σ, t σ := by
    simpa [t] using AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook
      (Matrix.of (fun i j => complete (a i + b j - c)))
  have hv (σ) : Base.monomialValuation negativeSquareWeight (t σ) =
      (-squareAssignment a b c σ : WithTop ℝ) :=
    Base.monomialValuation_eq_of_homogeneous (assignment_term_ne_zero a b c h σ)
      (assignment_term_homogeneous a b c h σ)
  rw [hd, (Base.initialForm_sum_unique Finset.univ t (Finset.mem_univ (Equiv.refl _))
    (assignment_term_ne_zero a b c h _) (by
      intro σ _ hσ
      rw [hv, hv]
      exact WithTop.coe_lt_coe.mpr (neg_lt_neg (square_assignment_lt_identity c ha hb σ hσ)))).1]
  rw [Base.initialForm_eq_of_homogeneous (assignment_term_ne_zero a b c h _)
    (assignment_term_homogeneous a b c h _)]
  simp only [Equiv.Perm.sign_refl, one_smul, Equiv.refl_apply]
  simp_rw [complete_of_pos (h _ _)]
  exact prod_X_eq_monomial _

/-- Distinct monomial initial forms force rational linear independence, even at tied weights. -/
theorem linearIndependent_of_monomial_initial {ι : Type*} [Finite ι]
    (p : ι → CompleteRing) (d : ι → ℕ+ →₀ ℕ) (u : ι → ℚ)
    (hu : ∀ i, u i ≠ 0) (hd : Function.Injective d)
    (hi : ∀ i, Base.initialForm negativeSquareWeight (p i) = monomial (d i) (u i)) :
    LinearIndependent ℚ p := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply Fintype.linearIndependent_iff.mpr
  intro v hz
  by_contra hnone
  have hv : ∃ i, v i ≠ 0 := by simpa only [not_forall] using hnone
  let S : Finset ι := Finset.univ.filter fun i => v i ≠ 0
  have hs : S.Nonempty := by obtain ⟨i, h⟩ := hv; exact ⟨i, by simp [S, h]⟩
  obtain ⟨i, his, hmin⟩ := Finset.exists_min_image S
    (fun i => Base.leastWeight negativeSquareWeight (p i)) hs
  have hwd (j) : Finsupp.weight negativeSquareWeight (d j) =
      Base.leastWeight negativeSquareWeight (p j) := by
    have hc : (Base.initialForm negativeSquareWeight (p j)).coeff (d j) ≠ 0 := by
      rw [hi j]; simpa using hu j
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _ hc
  have hci : (p i).coeff (d i) = u i := by
    have hh := congrArg (fun q : CompleteRing => q.coeff (d i)) (hi i)
    simpa [Base.initialForm, coeff_weightedHomogeneousComponent, hwd i] using hh
  have hother : ∀ j ∈ S, j ≠ i → (p j).coeff (d i) = 0 := by
    intro j hj hji
    by_cases hw : Base.leastWeight negativeSquareWeight (p j) =
        Base.leastWeight negativeSquareWeight (p i)
    · have hh := congrArg (fun q : CompleteRing => q.coeff (d i)) (hi j)
      have hdi : d j ≠ d i := fun h => hji (hd h)
      simpa [Base.initialForm, coeff_weightedHomogeneousComponent,
        hwd i, hw, hdi, hdi.symm] using hh
    · by_contra hc
      have hb := Base.leastWeight_lowerBound negativeSquareWeight (p j) (d i) hc
      rw [hwd i] at hb
      exact hw (le_antisymm hb (hmin j hj))
  have hz' := congrArg (fun q : CompleteRing => q.coeff (d i)) hz
  have hzS : ∑ j ∈ S, v j * (p j).coeff (d i) = 0 := by
    have hsum : (∑ j ∈ S, v j * (p j).coeff (d i)) =
        ∑ j, v j * (p j).coeff (d i) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hvj : v j = 0 := by simpa [S] using hj
      simp [hvj]
    rw [hsum]
    simpa only [coeff_sum, coeff_smul, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, smul_eq_mul] using hz'
  rw [Finset.sum_eq_single i (by
    intro j hj hji; rw [hother j hj hji, mul_zero]) (by simp [his]), hci] at hzS
  exact (mul_ne_zero (by simpa [S] using his) (hu i)) hzS

end SkewCofactorIndependence
