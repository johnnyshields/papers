/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalAffineJets
import SkewCornerDescent.Matrix.HessenbergPermutationCost

/-!
# Affineness at the full Hessenberg cost frontier

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). Exact
permutation displacement excludes two first-fresh upper entries in one frontier
term. Every other upper factor stays in the lower field. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F]

/-- A complete frontier product contains at most one first-fresh upper response,
so it is affine over the lower field. No whole upper product is replaced by a residue. -/
theorem hessenberg_frontier_product_affine {n : ℕ} (S : Subfield F) (x : F)
    (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1)
    (m : ℕ) (hm : 0 < m)
    (hcost : (Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))).card ≤ m)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      PowerSeries.constantCoeff (A i j) ∈ S)
    (hlong : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) ≤ m →
      affineOver S x (PowerSeries.constantCoeff (A i j))) :
    affineOver S x (∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ)),
      PowerSeries.constantCoeff (A i (σ i))) := by
  classical
  let upper := Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ))
  change affineOver S x (∏ i ∈ upper, PowerSeries.constantCoeff (A i (σ i)))
  by_cases hlarge : ∃ i : Fin n, m ≤ (σ i : ℕ) - (i : ℕ)
  · obtain ⟨i, hi⟩ := hlarge
    have hupi : (i : ℕ) ≤ (σ i : ℕ) := by omega
    have himem : i ∈ upper := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hia := hlong i (σ i) hupi
      ((hessenberg_permutation_interval_cost σ hσ i hupi).trans hcost)
    rw [← Finset.mul_prod_erase upper _ himem]
    apply affineOver_mul_of_right_mem S x hia
    apply S.prod_mem
    intro j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    have hupj : (j : ℕ) ≤ (σ j : ℕ) := by have := (Finset.mem_filter.mp hj).2; omega
    apply hshort j (σ j) hupj
    by_contra hnot
    have hjlong : m ≤ (σ j : ℕ) - (j : ℕ) := by omega
    exact hne (hessenberg_permutation_long_unique σ hσ m hm hcost j i hjlong hi)
  · apply affineOver_of_mem S x
    apply S.prod_mem
    intro i hi
    have hupi : (i : ℕ) ≤ (σ i : ℕ) := by have := (Finset.mem_filter.mp hi).2; omega
    apply hshort i (σ i) hupi
    by_contra hnot
    exact hlarge ⟨i, by omega⟩

private theorem prod_series_coeff_mem {ι : Type*} (S : Subfield F) (s : Finset ι)
    (p : ι → PowerSeries F) (hp : ∀ i ∈ s, ∀ k, PowerSeries.coeff k (p i) ∈ S) :
    ∀ k, PowerSeries.coeff k (∏ i ∈ s, p i) ∈ S := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty =>
    intro _ k
    simp only [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs <;> simp
  | @insert i s hi ih =>
    intro hp k
    rw [Finset.prod_insert hi]
    exact series_coeff_mul_mem_subfield S _ _ (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))) k

/-- Each complete admissible permutation term has lower earlier coefficients and
an affine first-fresh coefficient. Long intervals are excluded by their exact cost. -/
theorem hessenberg_permutation_jets_affine {n : ℕ} (S : Subfield F) (x : F)
    (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1) (a : F) (ha : a ∈ S)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ) (hm : 0 < m)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      ∀ k, PowerSeries.coeff k (A i j) ∈ S)
    (hlong : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) ≤ m →
      affineOver S x (PowerSeries.constantCoeff (A i j))) :
    jetsAffineOver S x (∏ i : Fin n, A i (σ i)) m := by
  classical
  let lower := Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))
  let upper := Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ))
  have hproduct := hessenberg_permutation_product A σ hσ
    (PowerSeries.X * PowerSeries.C a) hsub
  change (∏ i : Fin n, A i (σ i)) =
    (PowerSeries.X * PowerSeries.C a) ^ lower.card * ∏ i ∈ upper, A i (σ i) at hproduct
  have hcoeff (k : ℕ) : PowerSeries.coeff k (∏ i : Fin n, A i (σ i)) =
      if lower.card ≤ k then a ^ lower.card *
        PowerSeries.coeff (k - lower.card) (∏ i ∈ upper, A i (σ i)) else 0 := by
    rw [hproduct, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul']
    simp only [← map_pow, PowerSeries.coeff_C_mul]
  have hlow (hcost : lower.card < m) :
      ∀ k, PowerSeries.coeff k (∏ i ∈ upper, A i (σ i)) ∈ S := by
    apply prod_series_coeff_mem
    intro i hi k
    have hupi : (i : ℕ) ≤ (σ i : ℕ) := by have := (Finset.mem_filter.mp hi).2; omega
    apply hshort i (σ i) hupi
    exact (hessenberg_permutation_interval_cost σ hσ i hupi).trans_lt hcost
  constructor
  · intro k hk
    rw [hcoeff k]
    split_ifs with hcost
    · exact S.mul_mem (S.pow_mem ha _) (hlow (by omega) _)
    · exact S.zero_mem
  · rw [hcoeff m]
    by_cases hcost : lower.card ≤ m
    · rw [ite_eq_left hcost]
      by_cases he : lower.card = m
      · simp only [he, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
        apply affineOver_mul_of_left_mem S x (S.pow_mem ha _)
        exact hessenberg_frontier_product_affine S x A σ hσ m hm hcost
          (fun i j hij hlen => by
            simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hshort i j hij hlen 0)
          hlong
      · exact affineOver_of_mem S x (S.mul_mem (S.pow_mem ha _) (hlow (by omega) _))
    · rw [ite_eq_right hcost]
      exact affineOver_of_mem S x S.zero_mem

/-- The complete original Hessenberg determinant has the affine first-fresh jet,
with all signs, admissible permutations, and full shorter-response jets retained. -/
theorem hessenberg_jets_affine {n : ℕ} (S : Subfield F) (x : F)
    (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (hA : IsUpperHessenberg A)
    (a : F) (ha : a ∈ S)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ) (hm : 0 < m)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      ∀ k, PowerSeries.coeff k (A i j) ∈ S)
    (hlong : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) ≤ m →
      affineOver S x (PowerSeries.constantCoeff (A i j))) :
    jetsAffineOver S x A.det m := by
  classical
  have hterms (σ : Equiv.Perm (Fin n)) : jetsAffineOver S x
      ((Equiv.Perm.sign σ : ℤ) • ∏ i : Fin n, A i (σ i)) m := by
    apply jetsAffineOver_zsmul
    by_cases hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1
    · exact hessenberg_permutation_jets_affine S x A σ hσ a ha hsub m hm hshort hlong
    · have hz : (∏ i : Fin n, A i (σ i)) = 0 := by
        obtain ⟨i, hi⟩ := not_forall.mp hσ
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact hA i (σ i) (by omega)
      rw [hz]
      exact ⟨fun k _ => by simp, affineOver_of_mem S x (by simp)⟩
  rw [← Matrix.det_transpose A, Matrix.det_apply]
  constructor
  · intro k hk
    rw [map_sum]
    apply S.sum_mem
    intro σ _
    simpa only [Matrix.transpose_apply, Units.smul_def] using (hterms σ).1 k hk
  · rw [map_sum]
    apply affineOver_sum
    intro σ _
    simpa only [Matrix.transpose_apply, Units.smul_def] using (hterms σ).2

end SkewCornerDescent.Matrix
