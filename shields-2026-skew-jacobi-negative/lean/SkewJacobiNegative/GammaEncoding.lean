/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.AffineHomogenization
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.Finsupp.Weight

/-!
# The coefficient formula for the affine zero-free map

The linear encoding in `eq:homogenization` and `lem:homogenization` of
`shields-2026-skew-jacobi-negative.tex`.  Padding uses the full determinant
order, including the entries equal to one.  The determinant identity applies
to every beta diagram, without a connectedness assumption.
-/

namespace SkewJacobiNegative

open MvPolynomial

/-- Positive complete-generator labels become odd positive labels. -/
def oddIndex (j : ℕ+) : ℕ+ := ⟨2 * (j : ℕ) + 1, by omega⟩

/-- The exponent vector after inserting all omitted unit factors. -/
noncomputable def gammaExp (n : ℕ) (d : ℕ+ →₀ ℕ) : ℕ+ →₀ ℕ :=
  Finsupp.single 1 (n - d.degree) + d.mapDomain oddIndex

/-- The genuine rational linear map on monomials; coinciding exponents are
collected by the coefficient finitely supported function. -/
noncomputable def gammaEncoding (n : ℕ) : CompleteRing →ₗ[ℚ] CompleteRing :=
  AddMonoidAlgebra.mapDomainLinearMap ℚ ℚ (gammaExp n)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem gammaEncoding_monomial (n : ℕ) (d : ℕ+ →₀ ℕ) (c : ℚ) :
    gammaEncoding n (monomial d c) = monomial (gammaExp n d) c := by
  change (AddMonoidAlgebra.mapDomainLinearMap ℚ ℚ (gammaExp n))
    (AddMonoidAlgebra.single d c) = AddMonoidAlgebra.single (gammaExp n d) c
  exact AddMonoidAlgebra.mapDomainLinearMap_single (R := ℚ) (gammaExp n) c d

/-- Exact support-sum form, valid for every polynomial and every padding order. -/
theorem gammaEncoding_sum (n : ℕ) (p : CompleteRing) :
    gammaEncoding n p = ∑ d ∈ p.support, monomial (gammaExp n d) (p.coeff d) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, gammaEncoding_monomial]

/-- Each output coefficient includes all contributions, including cancellation. -/
theorem coeff_gammaEncoding (n : ℕ) (p : CompleteRing) (e : ℕ+ →₀ ℕ) :
    (gammaEncoding n p).coeff e =
      ∑ d ∈ p.support, if gammaExp n d = e then p.coeff d else 0 := by
  rw [gammaEncoding_sum]
  simp only [coeff_sum, coeff_monomial]

/-- The monomial form is the manuscript's unit power times the odd-label product. -/
theorem monomial_gammaExp (n : ℕ) (d : ℕ+ →₀ ℕ) (c : ℚ) :
    monomial (gammaExp n d) c =
      X (1 : ℕ+) ^ (n - d.degree) *
        (C c * d.prod fun j k => (X (oddIndex j) : CompleteRing) ^ k) := by
  rw [gammaExp, monomial_single_add, ← rename_monomial, monomial_eq]
  simp only [map_mul, rename_C, map_finsuppProd, map_pow, rename_X]

/-- Addition of exponents also adds padding, provided neither order is exceeded. -/
theorem gammaExp_add {n m : ℕ} (d e : ℕ+ →₀ ℕ)
    (hd : d.degree ≤ n) (he : e.degree ≤ m) :
    gammaExp (n + m) (d + e) = gammaExp n d + gammaExp m e := by
  have hsub : n + m - (d.degree + e.degree) =
      (n - d.degree) + (m - e.degree) := by omega
  simp only [gammaExp, map_add, hsub, Finsupp.mapDomain_add, Finsupp.single_add]
  ac_rfl

private noncomputable def entryExp (k : ℤ) : ℕ+ →₀ ℕ :=
  if hk : 0 < k then Finsupp.single (⟨k.toNat, by omega⟩ : ℕ+) 1 else 0

set_option backward.isDefEq.respectTransparency false in
private theorem entryExp_degree_le (k : ℤ) : (entryExp k).degree ≤ 1 := by
  by_cases hk : 0 < k
  · let j : ℕ+ := ⟨k.toNat, by omega⟩
    rw [entryExp, dite_eq_left hk]
    change (Finsupp.single j 1).degree ≤ 1
    simp only [Finsupp.degree_single, le_refl]
  · rw [entryExp, dite_eq_right hk]
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem complete_entryExp {k : ℤ} (hk : 0 ≤ k) :
    complete k = monomial (entryExp k) 1 := by
  by_cases hpos : 0 < k
  · rw [complete_of_pos hpos]
    let j : ℕ+ := ⟨k.toNat, by omega⟩
    rw [entryExp, dite_eq_left hpos]
    change X j = monomial (Finsupp.single j 1) 1
    rfl
  · have hz : k = 0 := by omega
    subst k
    simp [entryExp]

set_option backward.isDefEq.respectTransparency false in
private theorem complete_gamma_entryExp {k : ℤ} (hk : 0 ≤ k) :
    complete (2 * k + 1) = monomial (gammaExp 1 (entryExp k)) 1 := by
  have hpos : 0 < 2 * k + 1 := by omega
  rw [complete_of_pos hpos]
  by_cases hkp : 0 < k
  · let j : ℕ+ := ⟨k.toNat, by omega⟩
    have hidx : (⟨(2 * k + 1).toNat, by omega⟩ : ℕ+) = oddIndex j := by
      apply Subtype.ext
      change (2 * k + 1).toNat = 2 * k.toNat + 1
      omega
    have he : entryExp k = Finsupp.single j 1 := by
      rw [entryExp, dite_eq_left hkp]
    have hg : gammaExp 1 (Finsupp.single j 1) = Finsupp.single (oddIndex j) 1 := by
      unfold gammaExp
      rw [Finsupp.degree_single, Finsupp.mapDomain_single]
      simp only [Nat.sub_self, Finsupp.single_zero, zero_add]
    rw [he, hg, hidx]
    rfl
  · have hz : k = 0 := by omega
    subst k
    simp [entryExp, gammaExp, X]

private theorem entryExp_sum_degree_le {ι : Type*} (s : Finset ι) (k : ι → ℤ) :
    (∑ i ∈ s, entryExp (k i)).degree ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, map_add, Finset.card_insert_of_notMem hi]
    have h := entryExp_degree_le (k i)
    omega

private theorem complete_prod_monomial {ι : Type*} (s : Finset ι) (k : ι → ℤ)
    (hk : ∀ i ∈ s, 0 ≤ k i) :
    (∏ i ∈ s, complete (k i)) = monomial (∑ i ∈ s, entryExp (k i)) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      complete_entryExp (hk i (Finset.mem_insert_self i s)),
      ih (fun j hj => hk j (Finset.mem_insert_of_mem hj)), monomial_mul_monomial,
      one_mul]

private theorem gamma_monomial_prod {ι : Type*} (s : Finset ι) (k : ι → ℤ)
    (hk : ∀ i ∈ s, 0 ≤ k i) :
    monomial (gammaExp s.card (∑ i ∈ s, entryExp (k i))) (1 : ℚ) =
      ∏ i ∈ s, complete (2 * k i + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gammaExp]
  | @insert i s hi ih =>
    have hmul (a b : ℕ+ →₀ ℕ) :
        monomial (a + b) (1 : ℚ) =
          (monomial a 1 : CompleteRing) * monomial b 1 := by
      simp only [monomial_mul_monomial, one_mul]
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
      show s.card + 1 = 1 + s.card by omega,
      gammaExp_add _ _ (entryExp_degree_le (k i)) (entryExp_sum_degree_le s k),
      hmul,
      ← complete_gamma_entryExp (hk i (Finset.mem_insert_self i s)),
      ih (fun j hj => hk j (Finset.mem_insert_of_mem hj)), Finset.prod_insert hi]

/-- The unit-sensitive formula for a product of matrix entries.  A negative
entry annihilates both sides; otherwise each of the factors occupies one row. -/
theorem gammaEncoding_complete_prod {ι : Type*} (s : Finset ι) (k : ι → ℤ) :
    gammaEncoding s.card (∏ i ∈ s, complete (k i)) =
      ∏ i ∈ s, complete (2 * k i + 1) := by
  classical
  by_cases hk : ∀ i ∈ s, 0 ≤ k i
  · rw [complete_prod_monomial s k hk, gammaEncoding_monomial]
    exact gamma_monomial_prod s k hk
  · push_neg at hk
    obtain ⟨i, hi, hneg⟩ := hk
    have hneg' : 2 * k i + 1 < 0 := by omega
    have hz : (∏ j ∈ s, complete (k j)) = 0 :=
      Finset.prod_eq_zero hi (complete_of_neg hneg)
    have hz' : (∏ j ∈ s, complete (2 * k j + 1)) = 0 :=
      Finset.prod_eq_zero hi (complete_of_neg hneg')
    rw [hz, hz', map_zero]

private theorem gammaEncoding_intCast_mul (n : ℕ) (z : ℤ) (p : CompleteRing) :
    gammaEncoding n ((z : CompleteRing) * p) =
      (z : CompleteRing) * gammaEncoding n p := by
  have hs : (z : CompleteRing) * p = (z : ℚ) • p := by
    simp [MvPolynomial.smul_eq_C_mul]
  rw [hs, map_smul]
  simp [MvPolynomial.smul_eq_C_mul]

namespace BetaDiagram

/-- The actual full-order Gamma determinant is the linear coefficient encoding.
No row deletion, connectedness assumption, or determinant-identity premise is used. -/
theorem gamma_schur_encoding {n : ℕ} (D : BetaDiagram n) :
    D.gamma.schur = gammaEncoding n D.schur := by
  classical
  rw [schur, schur, Matrix.det_apply', Matrix.det_apply', map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [gammaEncoding_intCast_mul]
  congr 1
  have h := gammaEncoding_complete_prod (Finset.univ : Finset (Fin n))
    (fun i => D.row (σ i) - D.col i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simp only [matrix, Matrix.of_apply, gamma]
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

/-- The displayed coefficient formula, with padding by the original full order. -/
theorem gamma_schur_sum {n : ℕ} (D : BetaDiagram n) :
    D.gamma.schur =
      ∑ d ∈ D.schur.support, monomial (gammaExp n d) (D.schur.coeff d) := by
  rw [gamma_schur_encoding, gammaEncoding_sum]

/-- The same formula with the unit power and odd-generator product displayed. -/
theorem gamma_schur_padded_product {n : ℕ} (D : BetaDiagram n) :
    D.gamma.schur = ∑ d ∈ D.schur.support,
      X (1 : ℕ+) ^ (n - d.degree) *
        (C (D.schur.coeff d) *
          d.prod fun j k => (X (oddIndex j) : CompleteRing) ^ k) := by
  rw [gamma_schur_sum]
  apply Finset.sum_congr rfl
  intro d _
  exact monomial_gammaExp n d (D.schur.coeff d)

/-- Every coefficient of the affine image is produced from the original coefficients. -/
theorem coeff_gamma_schur {n : ℕ} (D : BetaDiagram n) (e : ℕ+ →₀ ℕ) :
    D.gamma.schur.coeff e = ∑ d ∈ D.schur.support,
      if gammaExp n d = e then D.schur.coeff d else 0 := by
  rw [gamma_schur_encoding, coeff_gammaEncoding]

end BetaDiagram
end SkewJacobiNegative
