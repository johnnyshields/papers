/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.PrimitiveNormalization
import SkewMarkedFactor.Gluing.CellSchur

/-!
# Primitive skew Schur functions

«Recovering the factors» (`sec:extraction`, `lem:primitive`): the row-length monomial of every
skew diagram has coefficient one and is the unique least-square-weight monomial.  The proof
uses strict rearrangement on each component's Jacobi--Trudi determinant and the coefficient
convolution formula to multiply the minima.  Empty and disconnected diagrams are included.
-/

namespace SkewMarkedFactor

open MvPolynomial Gluing

/-- A coefficient-one monomial strictly below every other nonzero coefficient in square weight. -/
def coefficientOneMinimum (f : Lambda) (m : MonomialIndex) : Prop :=
  f.coeff m = 1 ∧ ∀ n, f.coeff n ≠ 0 → n ≠ m → sqWeight m < sqWeight n

theorem coefficient_one_minimum_weight_le {f : Lambda} {m n : MonomialIndex}
    (hf : coefficientOneMinimum f m) (hn : f.coeff n ≠ 0) : sqWeight m ≤ sqWeight n := by
  by_cases h : n = m
  · simp [h]
  · exact (hf.2 n hn h).le

theorem coefficient_one_minimum_pair_eq {f g : Lambda} {a b u v : MonomialIndex}
    (hf : coefficientOneMinimum f a) (hg : coefficientOneMinimum g b)
    (hu : f.coeff u ≠ 0) (hv : g.coeff v ≠ 0)
    (hw : sqWeight (u + v) ≤ sqWeight (a + b)) : u = a ∧ v = b := by
  have ha := coefficient_one_minimum_weight_le hf hu
  have hb := coefficient_one_minimum_weight_le hg hv
  simp only [map_add] at hw
  have hua : u = a := by
    by_contra h
    have := hf.2 u hu h
    omega
  have hvb : v = b := by
    by_contra h
    have := hg.2 v hv h
    omega
  exact ⟨hua, hvb⟩

theorem coefficient_one_minimum_one : coefficientOneMinimum (1 : Lambda) 0 := by
  constructor
  · simp
  · intro n hn hne
    simp [MvPolynomial.coeff_one, Ne.symm hne] at hn

/-- The strict minimum of a product is the sum of its two strict minima, with coefficient one. -/
theorem coefficient_one_minimum_mul {f g : Lambda} {a b : MonomialIndex}
    (hf : coefficientOneMinimum f a) (hg : coefficientOneMinimum g b) :
    coefficientOneMinimum (f * g) (a + b) := by
  classical
  constructor
  · rw [coeff_mul, Finset.sum_eq_single (a, b)]
    · simp [hf.1, hg.1]
    · intro x hx hne
      by_contra hn
      have hu : f.coeff x.1 ≠ 0 := (mul_ne_zero_iff.mp hn).1
      have hv : g.coeff x.2 ≠ 0 := (mul_ne_zero_iff.mp hn).2
      have hxsum : x.1 + x.2 = a + b := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      obtain ⟨hu', hv'⟩ := coefficient_one_minimum_pair_eq hf hg hu hv (by rw [hxsum])
      exact hne (Prod.ext hu' hv')
    · intro h
      exact (h (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)).elim
  · intro n hn hne
    rw [coeff_mul] at hn
    obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have hu : f.coeff x.1 ≠ 0 := (mul_ne_zero_iff.mp hxne).1
    have hv : g.coeff x.2 ≠ 0 := (mul_ne_zero_iff.mp hxne).2
    have hxsum : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    by_contra h
    obtain ⟨hu', hv'⟩ := coefficient_one_minimum_pair_eq hf hg hu hv
      (by rw [hxsum]; exact not_lt.mp h)
    exact hne (by rw [← hxsum, hu', hv'])

theorem coefficient_one_minimum_prod {ι : Type*} (s : Finset ι)
    (f : ι → Lambda) (m : ι → MonomialIndex)
    (hf : ∀ i ∈ s, coefficientOneMinimum (f i) (m i)) :
    coefficientOneMinimum (∏ i ∈ s, f i) (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefficient_one_minimum_one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact coefficient_one_minimum_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem integral_polynomial_one : IntegralPolynomial (1 : Lambda) := by
  intro m
  by_cases hm : m = 0
  · subst m; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [MvPolynomial.coeff_one, Ne.symm hm]⟩

theorem integral_polynomial_mul {f g : Lambda} (hf : IntegralPolynomial f)
    (hg : IntegralPolynomial g) : IntegralPolynomial (f * g) := by
  classical
  intro m
  refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
    (f.coeff x.1).num * (g.coeff x.2).num, ?_⟩
  rw [coeff_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_coefficient_num hf, integral_coefficient_num hg]

theorem integral_polynomial_prod {ι : Type*} (s : Finset ι) (f : ι → Lambda)
    (hf : ∀ i ∈ s, IntegralPolynomial (f i)) : IntegralPolynomial (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integral_polynomial_one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact integral_polynomial_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Jacobi--Trudi has integer coefficients, including for arbitrary integer beta lists. -/
theorem integral_polynomial_beta_det {k : ℕ} (ξ ζ : Fin k → ℤ) :
    IntegralPolynomial (betaDet ξ ζ) := by
  classical
  intro m
  refine ⟨∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) *
    (if (∀ i, 0 ≤ ξ (σ i) - ζ i) ∧ (∑ i, hExp (ξ (σ i) - ζ i).toNat) = m
      then 1 else 0), ?_⟩
  rw [coeff_betaDet]
  push_cast
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp [zsmul_eq_mul]

theorem integral_polynomial_profile_schur {n : ℕ} (P : Profile n) :
    IntegralPolynomial P.schur :=
  integral_polynomial_beta_det P.xi P.zeta

theorem coefficient_one_minimum_profile_schur {n : ℕ} (P : Profile n) :
    coefficientOneMinimum P.schur (betaMon P.xi P.zeta) := by
  exact betaDet_extremal P.xi_strictAnti P.zeta_strictAnti fun i => by
    have := P.xi_sub_zeta i
    have := P.r_pos i
    omega

/-- The row-length monomial, summing over the actual occupied rows of the finite diagram. -/
noncomputable def rowLengthMonomial (D : Diagram) : MonomialIndex :=
  ∑ a ∈ rowSet D, hExp (rowLength D a)

/-- The beta-list diagonal monomial is precisely the monomial of the component's row lengths. -/
theorem row_length_monomial_connected {D : Diagram} (hD : IsConnectedSkew D) :
    rowLengthMonomial D = betaMon (cellProfile D).2.xi (cellProfile D).2.zeta := by
  classical
  obtain ⟨v, hv⟩ := hD.exists_translate_cells
  have hrows : rowSet D = Finset.univ.image (fun i : Fin ((cellProfile D).1 + 1) =>
      v.1 + (i : ℕ)) := by
    conv_lhs => rw [hv, rowSet_translate_cells]
    ext a
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨⟨(a - v.1).toNat, by omega⟩, ?_⟩
      change v.1 + ((a - v.1).toNat : ℤ) = a
      omega
    · rintro ⟨i, rfl⟩
      have := i.isLt
      constructor <;> omega
  rw [rowLengthMonomial, hrows, Finset.sum_image]
  · unfold betaMon
    apply Finset.sum_congr rfl
    intro i _
    have hl : rowLength D (v.1 + (i : ℕ)) = ((cellProfile D).2.r i : ℕ) := by
      exact (congrArg (fun X : Diagram => rowLength X (v.1 + (i : ℕ))) hv).trans
        (rowLength_translate_cells (cellProfile D).2 v i)
    rw [hl, (cellProfile D).2.xi_sub_zeta]
    simp
  · intro i _ j _ hij
    apply Fin.ext
    exact_mod_cast (add_left_cancel hij)

/-- A component containing a row contains that entire row of a skew diagram. -/
theorem row_cols_component {D C : Diagram} (hD : IsSkew D) (hC : C ∈ edgeComponents D)
    {a : ℤ} (ha : a ∈ rowSet C) : rowCols C a = rowCols D a := by
  classical
  obtain ⟨b, hb⟩ := mem_rowSet.mp ha
  have hcell : (a, b) ∈ C := mem_rowCols.mp hb
  have he := component_eq_of_mem hC hcell
  ext c
  rw [mem_rowCols, mem_rowCols]
  constructor
  · exact fun hc => component_subset hC hc
  · intro hc
    rw [he]
    apply Finset.mem_filter.mpr
    exact ⟨hc, hD.reach_row (component_subset hC hcell) hc⟩

theorem row_sets_components_disjoint {D : Diagram} (hD : IsSkew D) :
    Set.PairwiseDisjoint (↑(edgeComponents D)) rowSet := by
  classical
  intro C hC C' hC' hne
  apply Finset.disjoint_left.mpr
  intro a ha ha'
  obtain ⟨b, hb⟩ := mem_rowSet.mp ha
  have hcell : (a, b) ∈ C := mem_rowCols.mp hb
  have hc' : (a, b) ∈ C' := by
    apply mem_rowCols.mp
    rw [row_cols_component hD hC' ha', ← row_cols_component hD hC ha]
    exact hb
  exact hne ((component_eq_of_mem hC hcell).trans (component_eq_of_mem hC' hc').symm)

theorem row_sets_components_union (D : Diagram) :
    (edgeComponents D).biUnion rowSet = rowSet D := by
  classical
  ext a
  simp only [Finset.mem_biUnion, mem_rowSet]
  constructor
  · rintro ⟨C, hC, b, hb⟩
    exact ⟨b, mem_rowCols.mpr (component_subset hC (mem_rowCols.mp hb))⟩
  · rintro ⟨b, hb⟩
    have hcell : (a, b) ∈ (edgeComponents D).biUnion id := by
      rw [biUnion_edgeComponents]
      exact mem_rowCols.mp hb
    obtain ⟨C, hC, hc⟩ := Finset.mem_biUnion.mp hcell
    exact ⟨C, hC, b, mem_rowCols.mpr hc⟩

/-- Multiplication of component minima reconstructs exactly the diagram's row-length monomial. -/
theorem row_length_monomial_components {D : Diagram} (hD : IsSkew D) :
    rowLengthMonomial D = ∑ C ∈ edgeComponents D,
      betaMon (cellProfile C).2.xi (cellProfile C).2.zeta := by
  classical
  unfold rowLengthMonomial
  rw [← row_sets_components_union D, Finset.sum_biUnion (row_sets_components_disjoint hD)]
  apply Finset.sum_congr rfl
  intro C hC
  rw [← row_length_monomial_connected (isConnectedSkew_component hD hC)]
  unfold rowLengthMonomial
  apply Finset.sum_congr rfl
  intro a ha
  rw [rowLength, rowLength, row_cols_component hD hC ha]

/-- Integer coefficients are proved for every skew diagram, without connectedness. -/
theorem integral_polynomial_cell_schur {D : Diagram} (hD : IsSkew D) :
    IntegralPolynomial (cellSchur D) := by
  rw [cellSchur_eq_prod hD]
  exact integral_polynomial_prod _ _ fun C _ => integral_polynomial_profile_schur _

/-- The full arbitrary-skew coefficient-one, unique least-square-weight assertion. -/
theorem coefficient_one_minimum_cell_schur {D : Diagram} (hD : IsSkew D) :
    coefficientOneMinimum (cellSchur D) (rowLengthMonomial D) := by
  rw [cellSchur_eq_prod hD, row_length_monomial_components hD]
  exact coefficient_one_minimum_prod _ _ _ fun C _ => coefficient_one_minimum_profile_schur _

/-- `lem:primitive`, with its full arbitrary-skew scope. -/
theorem primitive_cellSchur_scalar {D : Diagram} (hD : IsSkew D)
    (q : ℚ) (hq : q ≠ 0) : primitive (q • cellSchur D) = cellSchur D := by
  obtain ⟨hc, hm⟩ := coefficient_one_minimum_cell_schur hD
  exact primitive_smul_of_coefficient_one (integral_polynomial_cell_schur hD) hc hm q hq

end SkewMarkedFactor
