/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.MaximalCofactors
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Tactic

/-!
# Row scaling without a common sampled family

The actual polynomial matrices in «An abstract Strict-Monge cofactor principle»
(`subsec:abstract`, `rem:abstract-family`) of
`shields-2026-skew-boundary-reconstruction.tex`.
The valuation is `Polynomial.trailingDegree`, the multiplicity of the variable,
with infinity at zero.  The finite values are also computed as
`Polynomial.natTrailingDegree`.  Coefficient computations supply nonvanishing
and every claimed order; no example outcomes are hypotheses.  Sorry-free.
-/

namespace SkewSchurReconstruction

open Polynomial

/-- The second row is scaled by the integer `a`, in the actual ring ℤ[t]. -/
noncomputable def abstractFamilyMatrix (a : ℤ) : Matrix (Fin 2) (Fin 3) (Polynomial ℤ) :=
  Matrix.of ![![1, 1, 1], ![C a * X ^ 3, C a * X ^ 2, C a * X]]

/-- The first matrix in `rem:abstract-family`. -/
noncomputable def abstractFamilyM : Matrix (Fin 2) (Fin 3) (Polynomial ℤ) :=
  abstractFamilyMatrix 1

/-- The row-scaled matrix in `rem:abstract-family`. -/
noncomputable def abstractFamilyN : Matrix (Fin 2) (Fin 3) (Polynomial ℤ) :=
  abstractFamilyMatrix 2

/-- The entry valuation pattern of both matrices. -/
def abstractFamilyEntryOrders : Matrix (Fin 2) (Fin 3) ℕ :=
  Matrix.of ![![0, 0, 0], ![3, 2, 1]]

private def cofactorLow : Fin 3 → ℕ := ![1, 1, 2]
private def cofactorHigh : Fin 3 → ℕ := ![2, 3, 3]
private def cofactorCoefficient (a : ℤ) : Fin 3 → ℤ := ![a, -a, a]

/-- Identification with the displayed matrices, including genuine integer scaling. -/
theorem abstractFamily_displayed :
    abstractFamilyM = Matrix.of ![![1, 1, 1], ![X ^ 3, X ^ 2, X]] ∧
    abstractFamilyN = Matrix.of ![![1, 1, 1], ![2 * X ^ 3, 2 * X ^ 2, 2 * X]] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [abstractFamilyM, abstractFamilyN, abstractFamilyMatrix]

private theorem binomial_coeff (a : ℤ) (l h k : ℕ) :
    (C a * (X ^ l - X ^ h) : Polynomial ℤ).coeff k =
      a * ((if k = l then 1 else 0) - (if k = h then 1 else 0)) := by
  simp [coeff_X_pow]

private theorem binomial_order (a : ℤ) (ha : a ≠ 0) (l h : ℕ) (hlh : l < h) :
    (C a * (X ^ l - X ^ h) : Polynomial ℤ) ≠ 0 ∧
    (C a * (X ^ l - X ^ h) : Polynomial ℤ).natTrailingDegree = l := by
  have hc : (C a * (X ^ l - X ^ h) : Polynomial ℤ).coeff l = a := by
    rw [binomial_coeff]
    simp [hlh.ne]
  have hp : (C a * (X ^ l - X ^ h) : Polynomial ℤ) ≠ 0 := by
    intro hp
    apply ha
    calc
      a = (C a * (X ^ l - X ^ h) : Polynomial ℤ).coeff l := hc.symm
      _ = 0 := by rw [hp]; simp
  refine ⟨hp, le_antisymm ?_ ?_⟩
  · exact natTrailingDegree_le_of_ne_zero (by rw [hc]; exact ha)
  · apply le_natTrailingDegree hp
    intro k hkl
    have hkh : k < h := hkl.trans hlh
    rw [binomial_coeff]
    simp [hkl.ne, hkh.ne]

/-- Direct evaluation of the signed determinants, not a surrogate cofactor vector. -/
theorem abstractFamily_cofactor_formula (a : ℤ) (j : Fin 3) :
    signedMaximalCofactor (abstractFamilyMatrix a) j =
      C (cofactorCoefficient a j) * (X ^ cofactorLow j - X ^ cofactorHigh j) := by
  fin_cases j <;>
    norm_num [signedMaximalCofactor, abstractFamilyMatrix, Matrix.det_fin_two,
      Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove,
      cofactorCoefficient, cofactorLow, cofactorHigh, C_neg] <;> ring

/-- Every coefficient of the actual maximal cofactors is computed in ℤ. -/
theorem abstractFamily_cofactor_coeff (a : ℤ) (j : Fin 3) (k : ℕ) :
    (signedMaximalCofactor (abstractFamilyMatrix a) j).coeff k =
      cofactorCoefficient a j *
        ((if k = cofactorLow j then 1 else 0) -
          (if k = cofactorHigh j then 1 else 0)) := by
  rw [abstractFamily_cofactor_formula]
  exact binomial_coeff _ _ _ _

/-- Nonzero integer row scalars produce nonzero actual cofactors of orders (1,1,2). -/
theorem abstractFamily_cofactor_order (a : ℤ) (ha : a ≠ 0) (j : Fin 3) :
    signedMaximalCofactor (abstractFamilyMatrix a) j ≠ 0 ∧
    (signedMaximalCofactor (abstractFamilyMatrix a) j).natTrailingDegree =
      ![1, 1, 2] j := by
  rw [abstractFamily_cofactor_formula]
  have hcoeff : cofactorCoefficient a j ≠ 0 := by
    fin_cases j <;> simpa [cofactorCoefficient] using ha
  have horder : cofactorLow j < cofactorHigh j := by
    fin_cases j <;> norm_num [cofactorLow, cofactorHigh]
  exact binomial_order _ hcoeff _ _ horder

/-- The leading t-adic coefficients are ±a, so scaling by two does not kill them. -/
theorem abstractFamily_cofactor_leading_coeff (a : ℤ) (j : Fin 3) :
    (signedMaximalCofactor (abstractFamilyMatrix a) j).coeff (![1, 1, 2] j) =
      ![a, -a, a] j := by
  rw [abstractFamily_cofactor_coeff]
  fin_cases j <;> norm_num [cofactorCoefficient, cofactorLow, cofactorHigh]

/-- The actual cofactor vector of N is twice that of M. -/
theorem abstractFamily_cofactor_scaling (j : Fin 3) :
    signedMaximalCofactor abstractFamilyN j =
      2 * signedMaximalCofactor abstractFamilyM j := by
  simp only [abstractFamilyN, abstractFamilyM, abstractFamily_cofactor_formula]
  fin_cases j <;> norm_num [cofactorCoefficient, cofactorLow, cofactorHigh, C_neg]
  all_goals ring

/-- All entries are supported: the Ferrers support is the full rectangle. -/
theorem abstractFamily_entry_nonzero (a : ℤ) (ha : a ≠ 0) (i : Fin 2) (j : Fin 3) :
    abstractFamilyMatrix a i j ≠ 0 := by
  fin_cases i
  · fin_cases j <;> simp [abstractFamilyMatrix]
  · change abstractFamilyMatrix a (1 : Fin 2) j ≠ 0
    have hc : (abstractFamilyMatrix a (1 : Fin 2) j).coeff (3 - j.val) = a := by
      fin_cases j <;> simp [abstractFamilyMatrix, coeff_X_pow]
    intro hp
    apply ha
    calc
      a = (abstractFamilyMatrix a 1 j).coeff (3 - j.val) := hc.symm
      _ = 0 := by rw [hp]; simp

/-- The bottom entries have actual trailing degrees 3,2,1. -/
theorem abstractFamily_entry_order (a : ℤ) (ha : a ≠ 0) (i : Fin 2) (j : Fin 3) :
    (abstractFamilyMatrix a i j).natTrailingDegree = abstractFamilyEntryOrders i j := by
  fin_cases i <;> fin_cases j <;>
    simp [abstractFamilyMatrix, abstractFamilyEntryOrders, natTrailingDegree_mul, ha]

/-- The finite orders identify the standard t-adic valuation, with no zero convention issue. -/
theorem abstractFamily_entry_valuation (a : ℤ) (ha : a ≠ 0) (i : Fin 2) (j : Fin 3) :
    (abstractFamilyMatrix a i j).trailingDegree = (abstractFamilyEntryOrders i j : ℕ∞) := by
  rw [trailingDegree_eq_natTrailingDegree (abstractFamily_entry_nonzero a ha i j),
    abstractFamily_entry_order a ha]

/-- Strict Monge inequalities hold for every pair of ordered rows and columns. -/
theorem abstractFamily_strict_monge (a : ℤ) (ha : a ≠ 0)
    (i i' : Fin 2) (j j' : Fin 3) (hi : i < i') (hj : j < j') :
    (abstractFamilyMatrix a i j).natTrailingDegree +
        (abstractFamilyMatrix a i' j').natTrailingDegree <
      (abstractFamilyMatrix a i j').natTrailingDegree +
        (abstractFamilyMatrix a i' j).natTrailingDegree := by
  simp only [abstractFamily_entry_order a ha]
  fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;>
    norm_num [abstractFamilyEntryOrders] at *

/-- Every column injection, hence every increasing matching, is feasible. -/
theorem abstractFamily_matching_feasible (a : ℤ) (ha : a ≠ 0)
    (matching : Fin 2 ↪ Fin 3) :
    ∀ i, abstractFamilyMatrix a i (matching i) ≠ 0 := by
  intro i
  exact abstractFamily_entry_nonzero a ha i (matching i)

/-- The first rows agree, while the actual second rows differ over ℤ[t]. -/
theorem abstractFamily_rows : abstractFamilyM 0 = abstractFamilyN 0 ∧
    abstractFamilyM 1 ≠ abstractFamilyN 1 := by
  constructor
  · funext j
    simp [abstractFamilyM, abstractFamilyN, abstractFamilyMatrix]
  · intro h
    have hc := congrArg (fun row : Fin 3 → Polynomial ℤ => (row 2).coeff 1) h
    norm_num [abstractFamilyM, abstractFamilyN, abstractFamilyMatrix] at hc

/-- Both cofactor vectors are nonzero in every column and have equal actual t-adic valuations. -/
theorem abstractFamily_no_split (j : Fin 3) :
    signedMaximalCofactor abstractFamilyM j ≠ 0 ∧
    signedMaximalCofactor abstractFamilyN j ≠ 0 ∧
    (signedMaximalCofactor abstractFamilyM j).trailingDegree = (![1, 1, 2] j : ℕ∞) ∧
    (signedMaximalCofactor abstractFamilyN j).trailingDegree = (![1, 1, 2] j : ℕ∞) := by
  obtain ⟨hM, hvM⟩ := abstractFamily_cofactor_order 1 (by norm_num) j
  obtain ⟨hN, hvN⟩ := abstractFamily_cofactor_order 2 (by norm_num) j
  refine ⟨hM, hN, ?_, ?_⟩
  · change (signedMaximalCofactor (abstractFamilyMatrix 1) j).trailingDegree = _
    rw [trailingDegree_eq_natTrailingDegree hM, hvM]
    fin_cases j <;> norm_cast
  · change (signedMaximalCofactor (abstractFamilyMatrix 2) j).trailingDegree = _
    rw [trailingDegree_eq_natTrailingDegree hN, hvN]
    fin_cases j <;> norm_cast

/-- No column has a valuation split between the two actual cofactor vectors. -/
theorem abstractFamily_split_set_empty :
    {j : Fin 3 | (signedMaximalCofactor abstractFamilyM j).trailingDegree ≠
      (signedMaximalCofactor abstractFamilyN j).trailingDegree} = ∅ := by
  ext j
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact (abstractFamily_no_split j).2.2.1.trans (abstractFamily_no_split j).2.2.2.symm

/-- The complete concrete matrix obstruction: supported strictly Monge boards sharing their
first row but differing in the second, with nonzero scaled cofactors and no valuation split. -/
theorem abstractFamily_witness :
    abstractFamilyM 0 = abstractFamilyN 0 ∧
    abstractFamilyM 1 ≠ abstractFamilyN 1 ∧
    (∀ i j, abstractFamilyM i j ≠ 0 ∧ abstractFamilyN i j ≠ 0) ∧
    (∀ i j, (abstractFamilyM i j).trailingDegree = (abstractFamilyEntryOrders i j : ℕ∞) ∧
      (abstractFamilyN i j).trailingDegree = (abstractFamilyEntryOrders i j : ℕ∞)) ∧
    (∀ i i' j j', i < i' → j < j' →
      (abstractFamilyM i j).natTrailingDegree + (abstractFamilyM i' j').natTrailingDegree <
        (abstractFamilyM i j').natTrailingDegree + (abstractFamilyM i' j).natTrailingDegree) ∧
    (∀ i i' j j', i < i' → j < j' →
      (abstractFamilyN i j).natTrailingDegree + (abstractFamilyN i' j').natTrailingDegree <
        (abstractFamilyN i j').natTrailingDegree + (abstractFamilyN i' j).natTrailingDegree) ∧
    (∀ j, signedMaximalCofactor abstractFamilyN j =
      2 * signedMaximalCofactor abstractFamilyM j) ∧
    (∀ j, signedMaximalCofactor abstractFamilyM j ≠ 0 ∧
      signedMaximalCofactor abstractFamilyN j ≠ 0 ∧
      (signedMaximalCofactor abstractFamilyM j).trailingDegree =
        (signedMaximalCofactor abstractFamilyN j).trailingDegree) := by
  refine ⟨abstractFamily_rows.1, abstractFamily_rows.2, ?_, ?_, ?_, ?_,
    abstractFamily_cofactor_scaling, ?_⟩
  · intro i j
    exact ⟨abstractFamily_entry_nonzero 1 (by norm_num) i j,
      abstractFamily_entry_nonzero 2 (by norm_num) i j⟩
  · intro i j
    exact ⟨abstractFamily_entry_valuation 1 (by norm_num) i j,
      abstractFamily_entry_valuation 2 (by norm_num) i j⟩
  · exact abstractFamily_strict_monge 1 (by norm_num)
  · exact abstractFamily_strict_monge 2 (by norm_num)
  · intro j
    obtain ⟨hM, hN, hvM, hvN⟩ := abstractFamily_no_split j
    exact ⟨hM, hN, hvM.trans hvN.symm⟩

/-- Strict Monge inequalities on supported samples of a common row family, with the
same ordered columns.  This is a standing family condition, not an example outcome. -/
def abstractFamilyStrictMonge {ι : Type*} [LinearOrder ι]
    (entry : ι → Fin 3 → Polynomial ℤ) : Prop :=
  ∀ A B : ι, A < B → ∀ j k : Fin 3, j < k →
    entry A j ≠ 0 → entry B k ≠ 0 → entry A k ≠ 0 → entry B j ≠ 0 →
    (entry A j).natTrailingDegree + (entry B k).natTrailingDegree <
      (entry A k).natTrailingDegree + (entry B j).natTrailingDegree

/-- The two second rows cannot be samples of one strictly Monge family.  Equal row
parameters would give equal rows; unequal parameters contradict their equal valuation profiles. -/
theorem abstractFamily_no_common_sampling {ι : Type*} [LinearOrder ι] :
    ¬ ∃ (entry : ι → Fin 3 → Polynomial ℤ) (A B : ι),
      abstractFamilyStrictMonge entry ∧
      (∀ j, entry A j = abstractFamilyM 1 j) ∧
      (∀ j, entry B j = abstractFamilyN 1 j) := by
  rintro ⟨entry, A, B, hstrict, hM, hN⟩
  have hsA : ∀ j, entry A j ≠ 0 := by
    intro j
    rw [hM]
    exact abstractFamily_entry_nonzero 1 (by norm_num) 1 j
  have hsB : ∀ j, entry B j ≠ 0 := by
    intro j
    rw [hN]
    exact abstractFamily_entry_nonzero 2 (by norm_num) 1 j
  have hvA : ∀ j, (entry A j).natTrailingDegree = abstractFamilyEntryOrders 1 j := by
    intro j
    rw [hM]
    exact abstractFamily_entry_order 1 (by norm_num) 1 j
  have hvB : ∀ j, (entry B j).natTrailingDegree = abstractFamilyEntryOrders 1 j := by
    intro j
    rw [hN]
    exact abstractFamily_entry_order 2 (by norm_num) 1 j
  obtain hAB | hAB | hAB := lt_trichotomy A B
  · have h := hstrict A B hAB 0 1 (by decide) (hsA 0) (hsB 1) (hsA 1) (hsB 0)
    simp only [hvA, hvB] at h
    norm_num [abstractFamilyEntryOrders] at h
  · apply abstractFamily_rows.2
    funext j
    exact (hM j).symm.trans ((congrArg (fun a => entry a j) hAB).trans (hN j))
  · have h := hstrict B A hAB 0 1 (by decide) (hsB 0) (hsA 1) (hsB 1) (hsA 0)
    simp only [hvA, hvB] at h
    norm_num [abstractFamilyEntryOrders] at h

end SkewSchurReconstruction
