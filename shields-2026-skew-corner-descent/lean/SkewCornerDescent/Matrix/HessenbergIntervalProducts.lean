/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergPermutationSign

/-!
# Full original permutation products as complete disjoint interval activities

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every original state is covered exactly once by the produced upper intervals.
The full signed permutation product retains each original upper entry and
arbitrary complete diagonal weights. No interval partition is an input.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Products over the complete produced upper intervals include every original
state exactly once, including singleton diagonals and the empty source. -/
theorem hessenberg_interval_prod {R : Type*} [CommMonoid R] {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ i : Fin N, i.val ≤ (σ i).val + 1)
    (f : Fin N → R) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val),
      ∏ k ∈ Finset.Icc i (σ i), f k) = ∏ k, f k := by
  classical
  let U := Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val)
  have hd : Set.PairwiseDisjoint (↑U) (fun i => Finset.Icc i (σ i)) := by
    intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro k hik hjk
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have hki : i ≤ k ∧ k ≤ σ i := Finset.mem_Icc.mp hik
    have hkj : j ≤ k ∧ k ≤ σ j := Finset.mem_Icc.mp hjk
    exact hessenberg_upper_intervals_disjoint σ hσ i j hi' hj' hne k
      ⟨⟨hki.1, hki.2⟩, hkj.1, hkj.2⟩
  have hu : U.biUnion (fun i => Finset.Icc i (σ i)) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro k
    obtain ⟨i, hi, _⟩ := hessenberg_interval_partition σ hσ k
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.1⟩,
        Finset.mem_Icc.mpr ⟨hi.2.1, hi.2.2⟩⟩
  change (∏ i ∈ U, ∏ k ∈ Finset.Icc i (σ i), f k) = _
  rw [← Finset.prod_biUnion hd, hu]

/-- The complete signed permutation term factors into its exact selected-cost sign,
exact subdiagonal power, and full interval activities. Complete inverse diagonal
series may be used as weights; nothing is replaced by a residue in this identity. -/
theorem hessenberg_signed_weighted_product {R : Type*} [CommRing R] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i : Fin N, i.val ≤ (σ i).val + 1) (t : R)
    (hsub : ∀ i j : Fin N, i.val = j.val + 1 → A i j = t) (w : Fin N → R) :
    (Equiv.Perm.sign σ : ℤ) • (∏ i, A i (σ i)) * (∏ i, w i) =
      (-1 : R) ^ (Finset.univ.filter (fun i : Fin N => (σ i).val < i.val)).card *
        t ^ (Finset.univ.filter (fun i : Fin N => (σ i).val < i.val)).card *
          ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val),
            A i (σ i) * ∏ k ∈ Finset.Icc i (σ i), w k := by
  rw [hessenberg_permutation_sign σ hσ,
    hessenberg_permutation_product A σ hσ t hsub]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, not_lt]
  have hi := hessenberg_interval_prod σ hσ w
  simp only [Finset.prod_mul_distrib]
  rw [hi]
  ring

/-- The whole original determinant has the complete signed disjoint-interval expansion.
Every nonadmissible term vanishes by actual support, and every admissible term
retains its complete entry and all original diagonal weights. -/
theorem hessenberg_det_weighted_intervals {R : Type*} [CommRing R] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (hA : IsUpperHessenberg A) (t : R)
    (hsub : ∀ i j : Fin N, i.val = j.val + 1 → A i j = t) (w : Fin N → R) :
    A.det * (∏ i, w i) =
      ∑ σ : Equiv.Perm (Fin N),
        if (∀ i : Fin N, i.val ≤ (σ i).val + 1) then
          (-1 : R) ^ (Finset.univ.filter (fun i : Fin N => (σ i).val < i.val)).card *
            t ^ (Finset.univ.filter (fun i : Fin N => (σ i).val < i.val)).card *
              ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val),
                A i (σ i) * ∏ k ∈ Finset.Icc i (σ i), w k
        else 0 := by
  classical
  rw [← Matrix.det_transpose A, Matrix.det_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply]
  by_cases hσ : ∀ i : Fin N, i.val ≤ (σ i).val + 1
  · rw [ite_eq_left hσ]
    exact hessenberg_signed_weighted_product A σ hσ t hsub w
  · rw [ite_eq_right hσ]
    push Not at hσ
    obtain ⟨i, hi⟩ := hσ
    have hz : (∏ k : Fin N, A k (σ k)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hA i (σ i) (by omega)
    rw [hz, smul_zero, zero_mul]

end SkewCornerDescent.Matrix
