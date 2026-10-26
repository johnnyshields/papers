/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.Hessenberg
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Minimum selected-subdiagonal cost of a permutation term

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
A nonzero Hessenberg permutation term containing a long upper interval must
contain at least that many selected subdiagonals. This is the geometric cost
constraint behind exclusion of longer intervals at an earlier normal order.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The total forward displacement equals the number of subdiagonal steps in a
Hessenberg permutation. No interval of the determinant expansion is discarded. -/
theorem hessenberg_permutation_forward_sum {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) ≤ (σ i : ℕ)),
      (((σ i : ℕ) : ℤ) - (i : ℕ)) =
        ((Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))).card : ℤ) := by
  classical
  have htotal : ∑ i : Fin n, (((σ i : ℕ) : ℤ) - (i : ℕ)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have he := Equiv.sum_comp σ (fun i : Fin n => ((i : ℕ) : ℤ))
    rw [he]
    exact sub_self _
  have hneg : ∑ i ∈ Finset.univ.filter (fun i => (σ i : ℕ) < (i : ℕ)),
      (((σ i : ℕ) : ℤ) - (i : ℕ)) =
        -((Finset.univ.filter (fun i => (σ i : ℕ) < (i : ℕ))).card : ℤ) := by
    calc
      _ = ∑ _i ∈ Finset.univ.filter (fun i => (σ i : ℕ) < (i : ℕ)), (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        have := hσ i
        omega
      _ = _ := by simp
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin n => (i : ℕ) ≤ (σ i : ℕ))
    (fun i => (((σ i : ℕ) : ℤ) - (i : ℕ)))
  simp only [not_le] at hsplit
  rw [htotal, hneg] at hsplit
  omega

/-- An upper interval's displacement is bounded by the exact number of selected
subdiagonals in its whole permutation term, including steps outside that interval. -/
theorem hessenberg_permutation_interval_cost {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1) (i : Fin n)
    (hi : (i : ℕ) ≤ (σ i : ℕ)) :
    (σ i : ℕ) - (i : ℕ) ≤
      (Finset.univ.filter (fun k => (σ k : ℕ) < (k : ℕ))).card := by
  classical
  have hle : (((σ i : ℕ) : ℤ) - (i : ℕ)) ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) ≤ (σ k : ℕ)),
        (((σ k : ℕ) : ℤ) - (k : ℕ)) := by
    apply Finset.single_le_sum
      (f := fun k : Fin n => (((σ k : ℕ) : ℤ) - (k : ℕ))) (a := i)
    · intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      omega
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  rw [hessenberg_permutation_forward_sum σ hσ] at hle
  omega

/-- At positive total cost at most `m`, at most one upper interval can have
length at least `m`. This excludes products of two first-fresh generator entries. -/
theorem hessenberg_permutation_long_unique {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1)
    (m : ℕ) (hm : 0 < m)
    (hcost : (Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))).card ≤ m)
    (i j : Fin n) (hi : m ≤ (σ i : ℕ) - (i : ℕ))
    (hj : m ≤ (σ j : ℕ) - (j : ℕ)) : i = j := by
  classical
  by_contra hne
  let upper := Finset.univ.filter (fun k : Fin n => (k : ℕ) ≤ (σ k : ℕ))
  let f := fun k : Fin n => (((σ k : ℕ) : ℤ) - (k : ℕ))
  have hupi : (i : ℕ) ≤ (σ i : ℕ) := by omega
  have hupj : (j : ℕ) ≤ (σ j : ℕ) := by omega
  have himem : i ∈ upper := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hupi⟩
  have hjmem : j ∈ upper.erase i :=
    Finset.mem_erase.mpr ⟨(fun h => hne h.symm), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hupj⟩⟩
  have hsum := hessenberg_permutation_forward_sum σ hσ
  change ∑ k ∈ upper, f k = _ at hsum
  have herase := Finset.add_sum_erase upper f himem
  have hle : f j ≤ ∑ k ∈ upper.erase i, f k := by
    apply Finset.single_le_sum
    · intro k hk
      have h := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hk)).2
      dsimp only [f]
      omega
    · exact hjmem
  have hfi : (m : ℤ) ≤ f i := by dsimp only [f]; omega
  have hfj : (m : ℤ) ≤ f j := by dsimp only [f]; omega
  omega

/-- All selected subdiagonal occurrences factor out with their exact cardinal multiplicity.
The remaining upper entries are complete entries, not their residues. -/
theorem hessenberg_permutation_product {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1) (t : R)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 → A i j = t) :
    (∏ i : Fin n, A i (σ i)) =
      t ^ (Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))).card *
        ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ)), A i (σ i) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i : Fin n => (σ i : ℕ) < (i : ℕ)) (fun i => A i (σ i))]
  congr 1
  calc
    _ = ∏ _i ∈ Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ)), t := by
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      apply hsub
      have := hσ i
      omega
    _ = _ := by simp

end SkewCornerDescent.Matrix
