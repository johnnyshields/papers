/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergOneShyIntervals
import SkewCornerDescent.Matrix.HessenbergIntervalProducts
import SkewCornerDescent.Matrix.HessenbergIntervalPermutation

/-!
# Exact complete activities on both determinant cost frontiers

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every original signed permutation term with a cost-exhausting interval retains
that whole activity. A one-shy interval leaves one actual disjoint adjacent pair.
All inverse diagonal weights remain intact, including their normal-dependent jets.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- A cost-exhausting interval leaves only genuine singleton activities, each
equal to one through the supplied diagonal inverse identity. -/
theorem hessenberg_single_interval_weighted_product {R : Type*} [CommRing R] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ j : Fin N, j.val ≤ (σ j).val + 1) (t : R)
    (hsub : ∀ j k : Fin N, j.val = k.val + 1 → A j k = t)
    (w : Fin N → R) (hdiag : ∀ j, A j j * w j = 1)
    (i : Fin N) (hi : i.val ≤ (σ i).val)
    (hcost : (σ i).val - i.val =
      (Finset.univ.filter (fun j : Fin N => (σ j).val < j.val)).card) :
    (Equiv.Perm.sign σ : ℤ) • (∏ j, A j (σ j)) * (∏ j, w j) =
      (-1 : R) ^ ((σ i).val - i.val) * t ^ ((σ i).val - i.val) *
        (A i (σ i) * ∏ l ∈ Finset.Icc i (σ i), w l) := by
  classical
  let upper := Finset.univ.filter (fun j : Fin N => j.val ≤ (σ j).val)
  let activity := fun j : Fin N => A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l
  have himem : i ∈ upper := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hprod : (∏ j ∈ upper, activity j) = activity i := by
    apply Finset.prod_eq_single i
    · intro j hj hji
      have hb := hessenberg_permutation_unique_forward σ hσ i hi hcost j hji
      have hjup : j.val ≤ (σ j).val := (Finset.mem_filter.mp hj).2
      have heq : σ j = j := Fin.ext (Nat.le_antisymm hb hjup)
      simpa only [activity, heq, Finset.Icc_self, Finset.prod_singleton] using hdiag j
    · intro hnot
      exact False.elim (hnot himem)
  rw [hessenberg_signed_weighted_product A σ hσ t hsub w, ← hcost]
  change (-1 : R) ^ ((σ i).val - i.val) * t ^ ((σ i).val - i.val) *
    (∏ j ∈ upper, activity j) = _
  rw [hprod]

/-- A complete one-shy signed term retains exactly the long interval and its
actual disjoint adjacent pair after genuine diagonal normalization. -/
theorem hessenberg_one_shy_weighted_product {R : Type*} [CommRing R] {N m : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i : Fin N, i.val ≤ (σ i).val + 1) (t : R)
    (hsub : ∀ i j : Fin N, i.val = j.val + 1 → A i j = t)
    (w : Fin N → R) (hdiag : ∀ j, A j j * w j = 1)
    (hm : 2 ≤ m)
    (hcost : (Finset.univ.filter (fun j : Fin N => (σ j).val < j.val)).card = m)
    (i : Fin N) (hi : (σ i).val - i.val = m - 1) :
    ∃ k : Fin N, k ≠ i ∧ (σ k).val = k.val + 1 ∧
      Disjoint (Finset.Icc i (σ i)) (Finset.Icc k (σ k)) ∧
      (Equiv.Perm.sign σ : ℤ) • (∏ j, A j (σ j)) * (∏ j, w j) =
        (-1 : R) ^ m * t ^ m *
          (A i (σ i) * ∏ l ∈ Finset.Icc i (σ i), w l) *
          (A k (σ k) * ∏ l ∈ Finset.Icc k (σ k), w l) := by
  classical
  obtain ⟨k, hki, hkadj, hdisjoint, hrest⟩ :=
    hessenberg_one_shy_disjoint_pair σ hσ hm hcost i hi
  refine ⟨k, hki, hkadj, hdisjoint, ?_⟩
  rw [hessenberg_signed_weighted_product A σ hσ t hsub w, hcost]
  let upper := Finset.univ.filter (fun j : Fin N => j.val ≤ (σ j).val)
  let activity := fun j : Fin N => A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l
  have hiup : i ∈ upper := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hkup : k ∈ upper := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hprod : (∏ j ∈ upper, activity j) = activity i * activity k := by
    calc
      _ = ∏ j ∈ ({i, k} : Finset (Fin N)), activity j := by
        symm
        apply Finset.prod_subset
          (Finset.insert_subset_iff.mpr ⟨hiup, Finset.singleton_subset_iff.mpr hkup⟩)
        intro j hj hnot
        have hji : j ≠ i := by intro he; apply hnot; simp [he]
        have hjk : j ≠ k := by intro he; apply hnot; simp [he]
        have hjup : j.val ≤ (σ j).val := (Finset.mem_filter.mp hj).2
        have heq : σ j = j := by
          rcases hrest j hji hjk with he | hdown
          · exact he
          · omega
        simpa only [activity, heq, Finset.Icc_self, Finset.prod_singleton] using hdiag j
      _ = _ := by simp [hki.symm]
  change (-1 : R) ^ m * t ^ m * (∏ j ∈ upper, activity j) = _
  rw [hprod]
  exact (mul_assoc _ _ _).symm

end SkewCornerDescent.Matrix
