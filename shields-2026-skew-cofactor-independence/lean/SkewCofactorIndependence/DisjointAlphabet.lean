/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.DilationAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Independence over a disjoint alphabet

The coefficient argument in `eq:offgrid-relation` is proved by currying a
polynomial in a sum alphabet.  The sum alphabet is then identified, by an
actual variable equivalence, with the divisible and nondivisible positive
complete-generator indices.  The weight projections in `thm:dilation`
separate the grid relation from the first-variation relation.
-/

noncomputable section

open scoped BigOperators

namespace SkewCofactorIndependence

section SumAlphabet

variable {A B ι : Type*}

/-- Currying leaves the first alphabet as polynomial variables. -/
theorem curry_rename_inl (q : MvPolynomial A ℚ) :
    MvPolynomial.sumRingEquiv ℚ A B (MvPolynomial.rename Sum.inl q) =
      MvPolynomial.map (MvPolynomial.C : ℚ →+* MvPolynomial B ℚ) q := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a hp => simp [hp]

/-- Currying regards the second alphabet as coefficient polynomials. -/
theorem curry_rename_inr (f : MvPolynomial B ℚ) :
    MvPolynomial.sumRingEquiv ℚ A B (MvPolynomial.rename Sum.inr f) =
      MvPolynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p b hp => simp [hp]

/-- Rationally independent coefficient polynomials stay independent over an
entire disjoint polynomial alphabet.  No finiteness of either alphabet is required. -/
theorem disjointAlphabet_independence [Fintype ι]
    (f : ι → MvPolynomial B ℚ) (q : ι → MvPolynomial A ℚ)
    (hf : LinearIndependent ℚ f)
    (h : (∑ i, MvPolynomial.rename Sum.inr (f i) *
      MvPolynomial.rename Sum.inl (q i) : MvPolynomial (A ⊕ B) ℚ) = 0) :
    ∀ i, q i = 0 := by
  classical
  have he : (∑ i, MvPolynomial.C (f i) *
      MvPolynomial.map (MvPolynomial.C : ℚ →+* MvPolynomial B ℚ) (q i)) = 0 := by
    simpa only [map_sum, map_mul, curry_rename_inr, curry_rename_inl, map_zero]
      using congrArg (MvPolynomial.sumRingEquiv ℚ A B) h
  intro i
  apply MvPolynomial.ext
  intro d
  have hc := congrArg (fun p : MvPolynomial A (MvPolynomial B ℚ) => p.coeff d) he
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  have hs : ∑ j, (q j).coeff d • f j = 0 := by
    calc
      _ = ∑ j, f j * MvPolynomial.C ((q j).coeff d) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_comm, MvPolynomial.C_mul']
      _ = 0 := hc
  exact (linearIndependent_iff'.mp hf) Finset.univ
    (fun j => (q j).coeff d) hs i (Finset.mem_univ i)

/-- A relation with at least one nonzero off-alphabet coefficient is impossible. -/
theorem disjointAlphabet_sum_ne_zero [Fintype ι]
    (f : ι → MvPolynomial B ℚ) (q : ι → MvPolynomial A ℚ)
    (hf : LinearIndependent ℚ f) (hq : ∃ i, q i ≠ 0) :
    (∑ i, MvPolynomial.rename Sum.inr (f i) *
      MvPolynomial.rename Sum.inl (q i) : MvPolynomial (A ⊕ B) ℚ) ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := hq
  exact hi (disjointAlphabet_independence f q hf h i)

end SumAlphabet

/-- Indices of generators outside the dilation grid.  This type is empty for `t = 1`. -/
def OffGridIndex (t : ℕ+) := {k : ℕ+ // ¬ (t : ℕ) ∣ (k : ℕ)}

/-- The actual variable map from the disjoint sum of alphabets to positive indices. -/
def joinAlphabet (t : ℕ+) : OffGridIndex t ⊕ ℕ+ → ℕ+
  | Sum.inl k => k.val
  | Sum.inr j => gridIndex t j

/-- The divisible and nondivisible generator alphabets partition all positive indices. -/
theorem joinAlphabet_bijective (t : ℕ+) : Function.Bijective (joinAlphabet t) := by
  constructor
  · intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
        exfalso
        apply a.property
        have hh := congrArg (fun k : ℕ+ => (k : ℕ)) h
        exact ⟨(b : ℕ), hh⟩
    | inr a =>
      cases y with
      | inl b =>
        exfalso
        apply b.property
        have hh := congrArg (fun k : ℕ+ => (k : ℕ)) h
        exact ⟨(a : ℕ), hh.symm⟩
      | inr b => exact congrArg Sum.inr (gridIndex_injective t h)
  · intro k
    by_cases hk : (t : ℕ) ∣ (k : ℕ)
    · obtain ⟨j, hj⟩ := hk
      have hjpos : 0 < j := by
        by_contra hn
        have hz : j = 0 := by omega
        simp [hz] at hj
      refine ⟨Sum.inr ⟨j, hjpos⟩, ?_⟩
      apply Subtype.ext
      exact hj.symm
    · exact ⟨Sum.inl ⟨k, hk⟩, rfl⟩

/-- Variable equivalence between the disjoint alphabet and the original complete alphabet. -/
def alphabetEquiv (t : ℕ+) : OffGridIndex t ⊕ ℕ+ ≃ ℕ+ :=
  Equiv.ofBijective (joinAlphabet t) (joinAlphabet_bijective t)

/-- The induced, faithful polynomial algebra equivalence. -/
def alphabetAlgEquiv (t : ℕ+) :
    MvPolynomial (OffGridIndex t ⊕ ℕ+) ℚ ≃ₐ[ℚ] CompleteRing :=
  MvPolynomial.renameEquiv ℚ (alphabetEquiv t)

/-- Inclusion of the nondivisible polynomial-generator algebra. -/
def offGridEmbed (t : ℕ+) : MvPolynomial (OffGridIndex t) ℚ →ₐ[ℚ] CompleteRing :=
  MvPolynomial.rename Subtype.val

/-- The disjoint equivalence identifies the grid inclusion with the actual dilation. -/
theorem alphabetAlgEquiv_grid (t : ℕ+) (f : CompleteRing) :
    alphabetAlgEquiv t (MvPolynomial.rename Sum.inr f) = dilation t f := by
  change MvPolynomial.rename (alphabetEquiv t)
    (MvPolynomial.rename Sum.inr f) = MvPolynomial.rename (gridIndex t) f
  rw [MvPolynomial.rename_rename]
  rfl

/-- The disjoint equivalence identifies the off-grid inclusion with actual variable renaming. -/
theorem alphabetAlgEquiv_offGrid (t : ℕ+) (q : MvPolynomial (OffGridIndex t) ℚ) :
    alphabetAlgEquiv t (MvPolynomial.rename Sum.inl q) = offGridEmbed t q := by
  change MvPolynomial.rename (alphabetEquiv t)
    (MvPolynomial.rename Sum.inl q) = MvPolynomial.rename Subtype.val q
  rw [MvPolynomial.rename_rename]
  rfl

/-- The coefficientwise conclusion of `eq:offgrid-relation`, proved in `CompleteRing`. -/
theorem dilation_offGrid_independence {ι : Type*} [Fintype ι]
    (t : ℕ+) (f : ι → CompleteRing) (q : ι → MvPolynomial (OffGridIndex t) ℚ)
    (hf : LinearIndependent ℚ f)
    (h : ∑ i, dilation t (f i) * offGridEmbed t (q i) = 0) :
    ∀ i, q i = 0 := by
  apply disjointAlphabet_independence f q hf
  apply (alphabetAlgEquiv t).injective
  simpa only [map_sum, map_mul, alphabetAlgEquiv_grid,
    alphabetAlgEquiv_offGrid, map_zero] using h

/-- A concrete off-grid coefficient cannot give a relation between independent grid cofactors. -/
theorem dilation_offGrid_sum_ne_zero {ι : Type*} [Fintype ι]
    (t : ℕ+) (f : ι → CompleteRing) (q : ι → MvPolynomial (OffGridIndex t) ℚ)
    (hf : LinearIndependent ℚ f) (hq : ∃ i, q i ≠ 0) :
    ∑ i, dilation t (f i) * offGridEmbed t (q i) ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := hq
  exact hi (dilation_offGrid_independence t f q hf h i)

/-- Weight one for nondivisible variables and zero for grid variables. -/
def offGridWeight (t : ℕ+) (k : ℕ+) : ℕ := if (t : ℕ) ∣ (k : ℕ) then 0 else 1

@[simp]
theorem offGridWeight_grid (t j : ℕ+) : offGridWeight t (gridIndex t j) = 0 := by
  simp [offGridWeight]

@[simp]
theorem offGridWeight_offGrid (t : ℕ+) (k : OffGridIndex t) :
    offGridWeight t k.val = 1 := by simp [offGridWeight, k.property]

/-- Every polynomial in the grid algebra has nondivisible degree zero. -/
theorem dilation_weightedHomogeneous (t : ℕ+) (p : CompleteRing) :
    MvPolynomial.IsWeightedHomogeneous (offGridWeight t) (dilation t p) 0 := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa using MvPolynomial.isWeightedHomogeneous_C (offGridWeight t) r
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p j hp =>
    have hx : MvPolynomial.IsWeightedHomogeneous (offGridWeight t)
        (MvPolynomial.X (gridIndex t j) : CompleteRing) 0 := by
      simpa using MvPolynomial.isWeightedHomogeneous_X ℚ (offGridWeight t) (gridIndex t j)
    simpa only [map_mul, dilation_X, zero_add] using hp.mul hx

/-- Each return-factor pair outside the grid has exactly two nondivisible factors. -/
theorem offGrid_pair_weightedHomogeneous (t : ℕ+) (a b : OffGridIndex t) :
    MvPolynomial.IsWeightedHomogeneous (offGridWeight t)
      (MvPolynomial.X a.val * MvPolynomial.X b.val : CompleteRing) 2 := by
  have ha := MvPolynomial.isWeightedHomogeneous_X (R := ℚ) (offGridWeight t) a.val
  have hb := MvPolynomial.isWeightedHomogeneous_X (R := ℚ) (offGridWeight t) b.val
  simpa using ha.mul hb

/-- Multiplication by any dilated cofactor preserves the return pair's degree two. -/
theorem firstVariation_term_weightedHomogeneous (t : ℕ+) (p : CompleteRing)
    (a b : OffGridIndex t) (c : ℚ) :
    MvPolynomial.IsWeightedHomogeneous (offGridWeight t)
      (MvPolynomial.C c * (dilation t p * (MvPolynomial.X a.val * MvPolynomial.X b.val))) 2 := by
  have hp := dilation_weightedHomogeneous t p
  have hq := offGrid_pair_weightedHomogeneous t a b
  simpa only [zero_add] using (hp.mul hq).C_mul c

/-- Distinct nondivisible degrees are separated by the actual weighted component maps. -/
theorem grid_offGrid_separation (t : ℕ+) {p q : CompleteRing}
    (hp : MvPolynomial.IsWeightedHomogeneous (offGridWeight t) p 0)
    (hq : MvPolynomial.IsWeightedHomogeneous (offGridWeight t) q 2)
    (h : p + q = 0) : p = 0 ∧ q = 0 := by
  have hp0 : MvPolynomial.weightedHomogeneousComponent (offGridWeight t) 0 p = p := by
    simpa using MvPolynomial.weightedHomogeneousComponent_of_mem (m := 0) hp
  have hq0 : MvPolynomial.weightedHomogeneousComponent (offGridWeight t) 0 q = 0 := by
    simpa using MvPolynomial.weightedHomogeneousComponent_of_mem (m := 0) hq
  have hpz : p = 0 := by
    have hc := congrArg (MvPolynomial.weightedHomogeneousComponent (offGridWeight t) 0) h
    simpa only [map_add, hp0, hq0, add_zero, map_zero] using hc
  exact ⟨hpz, by simpa [hpz] using h⟩

/-- A complete finite grid/off-grid first-variation relation splits without
assuming coefficientwise separation or any homogeneous property of its inputs. -/
theorem firstVariation_sum_separation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ℕ+) (grid : ι → CompleteRing) (cofactor : κ → CompleteRing)
    (a b : κ → OffGridIndex t) (c : κ → ℚ)
    (h : (∑ i, dilation t (grid i)) +
      (∑ j, MvPolynomial.C (c j) * (dilation t (cofactor j) *
        (MvPolynomial.X (a j).val * MvPolynomial.X (b j).val))) = 0) :
    (∑ i, grid i = 0) ∧
      (∑ j, MvPolynomial.C (c j) * (dilation t (cofactor j) *
        (MvPolynomial.X (a j).val * MvPolynomial.X (b j).val))) = 0 := by
  classical
  have hg : MvPolynomial.IsWeightedHomogeneous (offGridWeight t)
      (∑ i, dilation t (grid i)) 0 :=
    MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 0
      (fun i hi => dilation_weightedHomogeneous t (grid i))
  have ho : MvPolynomial.IsWeightedHomogeneous (offGridWeight t)
      (∑ j, MvPolynomial.C (c j) * (dilation t (cofactor j) *
        (MvPolynomial.X (a j).val * MvPolynomial.X (b j).val))) 2 :=
    MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 2 (fun j hj =>
      firstVariation_term_weightedHomogeneous t (cofactor j) (a j) (b j) (c j))
  obtain ⟨hgrid, hoff⟩ := grid_offGrid_separation t hg ho h
  refine ⟨(dilation_eq_zero_iff t _).mp ?_, hoff⟩
  simpa only [map_sum] using hgrid

/-- There are no nondivisible positive generators for the identity dilation. -/
theorem offGridIndex_one_empty : IsEmpty (OffGridIndex 1) :=
  ⟨fun k => k.property (one_dvd _)⟩

end SkewCofactorIndependence
