/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueHigherPolynomial

/-!
# Recovering original high indices from an actual linear response

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). A linear
expression in distinct surviving higher generators, with nonzero coefficients
in the actual selected lower field, determines its entire finite index set.
Evaluation is the existing injective map into the unchanged original residue
field, not a replacement by independent response values. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial
open scoped BigOperators

private theorem linear_inventory_coeff {ι σ R : Type*} [Fintype ι] [CommSemiring R]
    (index : ι → σ) (hindex : Function.Injective index) (a : ι → R) (i : ι) :
    (∑ j, MvPolynomial.C (a j) * MvPolynomial.X (index j)).coeff
      (Finsupp.single (index i) 1) = a i := by
  classical
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single i]
  · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_same, mul_one]
  · intro j _ hji
    have hs : Finsupp.single (index j) (1 : ℕ) ≠ Finsupp.single (index i) 1 := by
      intro h
      exact hji (hindex (Finsupp.single_left_injective one_ne_zero h))
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, ite_eq_right hs, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private theorem linear_inventory_coeff_absent {ι σ R : Type*} [Fintype ι] [CommSemiring R]
    (index : ι → σ) (a : ι → R) (j : σ) (hj : ∀ i, index i ≠ j) :
    (∑ i, MvPolynomial.C (a i) * MvPolynomial.X (index i)).coeff
      (Finsupp.single j 1) = 0 := by
  classical
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hs : Finsupp.single (index i) (1 : ℕ) ≠ Finsupp.single j 1 :=
    fun h => hj i (Finsupp.single_left_injective one_ne_zero h)
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, ite_eq_right hs, mul_zero]

/-- An actual linear high-coordinate inventory with nonzero lower coefficients
uniquely determines all its original indices. Both inventories may have different
finite indexing types, so equality includes equality of their cardinalities. -/
theorem residue_higher_linear_support_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N : ℕ+) (left : ι → ResidueHigherIndex N) (right : κ → ResidueHigherIndex N)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (a : ι → residueLowerField N N) (b : κ → residueLowerField N N)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (hvalue :
      (∑ i, (a i : OtherField N) * residueGenerator N ⟨(left i).val, ne_of_gt (left i).prop⟩) =
        ∑ j, (b j : OtherField N) * residueGenerator N ⟨(right j).val, ne_of_gt (right j).prop⟩) :
    Finset.univ.image left = Finset.univ.image right := by
  classical
  have hpoly : (∑ i, MvPolynomial.C (a i) * MvPolynomial.X (left i)) =
      ∑ j, MvPolynomial.C (b j) * MvPolynomial.X (right j) := by
    apply residueHigherEval_injective N
    simpa only [residueHigherEval, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X, Subfield.algebraMap_ofSubfield, Subfield.subtype_apply] using hvalue
  apply Finset.Subset.antisymm
  · intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    by_contra hnot
    have hcoeff := congrArg (fun p => p.coeff (Finsupp.single (left i) 1)) hpoly
    rw [linear_inventory_coeff left hleft a i,
      linear_inventory_coeff_absent right b (left i) (fun j he =>
        hnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, he⟩))] at hcoeff
    exact ha i hcoeff
  · intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    by_contra hnot
    have hcoeff := congrArg (fun p => p.coeff (Finsupp.single (right i) 1)) hpoly.symm
    rw [linear_inventory_coeff right hright b i,
      linear_inventory_coeff_absent left a (right i) (fun j he =>
        hnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, he⟩))] at hcoeff
    exact hb i hcoeff

end SkewCornerDescent.Matrix
