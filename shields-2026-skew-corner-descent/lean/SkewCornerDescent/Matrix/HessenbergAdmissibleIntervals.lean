/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.HessenbergPermutationCost

/-!
# Forced complete intervals of upper-Hessenberg permutations

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every admissible full permutation produces its own invariant prefix, exact
forced subdiagonal interval and disjoint upper arcs. No interval partition
is supplied. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- At an upper endpoint `i ≤ σ i`, every row `p < i` is sent by `σ` to a column `< i`.
The preimage of each column `c < i` lies strictly before `i`, since `σ i ≥ i > c` and the
Hessenberg bound gives `σ⁻¹ c ≤ c + 1 ≤ i`. Finite injectivity then makes this prefix
invariant. -/
theorem hessenberg_prefix_below_upper_endpoint {N : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ k : Fin N, (k : ℕ) ≤ (σ k : ℕ) + 1) (i : Fin N)
    (hi : (i : ℕ) ≤ (σ i : ℕ)) :
    ∀ p : Fin N, (p : ℕ) < (i : ℕ) → (σ p : ℕ) < (i : ℕ) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin N),
      S = Finset.univ.filter (fun c : Fin N => (c : ℕ) < (i : ℕ)) := ⟨_, rfl⟩
  have hmemS : ∀ c : Fin N, c ∈ S ↔ (c : ℕ) < (i : ℕ) := by
    intro c
    rw [hS]
    simp
  have hmap : ∀ c ∈ S, σ.symm c ∈ S := by
    intro c hc
    have hc' : (c : ℕ) < (i : ℕ) := (hmemS c).mp hc
    have hp := hσ (σ.symm c)
    rw [Equiv.apply_symm_apply] at hp
    have hne : σ.symm c ≠ i := by
      intro h
      have h2 : c = σ i := by
        rw [← h, Equiv.apply_symm_apply]
      have h3 := congrArg Fin.val h2
      omega
    have hne' := Fin.val_ne_of_ne hne
    exact (hmemS _).mpr (by omega)
  have hsub : S.image (⇑σ.symm) ⊆ S := Finset.image_subset_iff.mpr hmap
  have hcard : S.card ≤ (S.image (⇑σ.symm)).card :=
    (Finset.card_image_of_injective S σ.symm.injective).ge
  have himg : S.image (⇑σ.symm) = S := Finset.eq_of_subset_of_card_le hsub hcard
  intro p hp
  have hp' : p ∈ S.image (⇑σ.symm) := by
    rw [himg]
    exact (hmemS p).mpr hp
  obtain ⟨c, hc, hcp⟩ := Finset.mem_image.mp hp'
  rw [← hcp, Equiv.apply_symm_apply]
  exact (hmemS c).mp hc

/-- Forced interval: if `i ≤ σ i`, then every `k` with `i < k ≤ σ i` satisfies `σ k = k - 1`.
Induction on the distance from `i`. For the step `k = i + t + 1`, the preimage `p` of
`k - 1` satisfies `p ≤ k`. It cannot be below `i` (prefix invariance), cannot be `i`
(since `σ i ≥ k`), and cannot lie strictly between `i` and `k` (the induction hypothesis
makes those rows map to their predecessors). Hence `p = k`. -/
theorem hessenberg_forced_subdiagonals {N : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ k : Fin N, (k : ℕ) ≤ (σ k : ℕ) + 1) (i : Fin N)
    (hi : (i : ℕ) ≤ (σ i : ℕ)) :
    ∀ k : Fin N, (i : ℕ) < (k : ℕ) → (k : ℕ) ≤ (σ i : ℕ) → (σ k : ℕ) = (k : ℕ) - 1 := by
  classical
  have key : ∀ t : ℕ, ∀ k : Fin N, (i : ℕ) < (k : ℕ) → (k : ℕ) ≤ (i : ℕ) + t →
      (k : ℕ) ≤ (σ i : ℕ) → (σ k : ℕ) = (k : ℕ) - 1 := by
    intro t
    induction t with
    | zero =>
      intro k h1 h2 _
      omega
    | succ t ih =>
      intro k h1 h2 h3
      by_cases hk : (k : ℕ) ≤ (i : ℕ) + t
      · exact ih k h1 hk h3
      have hkv : (k : ℕ) = (i : ℕ) + t + 1 := by omega
      have hkN : (k : ℕ) < N := k.isLt
      obtain ⟨c, hcv⟩ : ∃ c : Fin N, (c : ℕ) = (k : ℕ) - 1 :=
        ⟨⟨(k : ℕ) - 1, by omega⟩, rfl⟩
      obtain ⟨p, hpdef⟩ : ∃ p : Fin N, σ.symm c = p := ⟨_, rfl⟩
      have hpc : σ p = c := by
        rw [← hpdef]
        exact σ.apply_symm_apply c
      have hpv : (σ p : ℕ) = (k : ℕ) - 1 := by
        rw [hpc, hcv]
      have hpk : (p : ℕ) ≤ (k : ℕ) := by
        have := hσ p
        omega
      have hpeq : (p : ℕ) = (k : ℕ) := by
        by_contra hne
        rcases lt_trichotomy (p : ℕ) (i : ℕ) with hpi | hpi | hpi
        · have hlt := hessenberg_prefix_below_upper_endpoint σ hσ i hi p hpi
          omega
        · have hpi' : σ p = σ i := congrArg σ (Fin.ext hpi)
          have h4 := congrArg Fin.val hpi'
          omega
        · have hrec := ih p hpi (by omega) (by omega)
          omega
      have hkp : k = p := Fin.ext hpeq.symm
      have hsk : σ k = c := by
        rw [hkp, hpc]
      rw [hsk, hcv]
  intro k h1 h2
  exact key ((k : ℕ) - (i : ℕ)) k h1 (by omega) h2

/-- Distinct complete upper intervals `[i, σ i]` and `[i', σ i']` share no position.
If `i < i' ≤ k`, the forced interval for `i` makes `σ i' = i' - 1`,
contradicting `i' ≤ σ i'`. Singleton diagonal intervals are included. -/
theorem hessenberg_upper_intervals_disjoint {N : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ k : Fin N, (k : ℕ) ≤ (σ k : ℕ) + 1) (i i' : Fin N)
    (hi : (i : ℕ) ≤ (σ i : ℕ)) (hi' : (i' : ℕ) ≤ (σ i' : ℕ)) (hne : i ≠ i')
    (k : Fin N) :
    ¬ (((i : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) ≤ (σ i : ℕ)) ∧
      ((i' : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) ≤ (σ i' : ℕ))) := by
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hv : (i : ℕ) ≠ (i' : ℕ) := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · have hf := hessenberg_forced_subdiagonals σ hσ i hi i' h (by omega)
    omega
  · have hf := hessenberg_forced_subdiagonals σ hσ i' hi' i h (by omega)
    omega

/-- Any lower occurrence of a finite permutation forces an upper crossing of the
same cut. This is a finite bijection fact, requiring no interval or cost hypothesis. -/
theorem permutation_lower_crossing {N : ℕ} (σ : Equiv.Perm (Fin N)) (k : Fin N)
    (hk : (σ k : ℕ) < (k : ℕ)) :
    ∃ i : Fin N, (i : ℕ) < (k : ℕ) ∧ (k : ℕ) ≤ (σ i : ℕ) := by
  classical
  by_contra! hnone
  let S := Finset.univ.filter (fun i : Fin N => i.val < k.val)
  have hsub : S.image σ ⊆ S := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone i (Finset.mem_filter.mp hi).2⟩
  have hcard : S.card ≤ (S.image σ).card := (Finset.card_image_of_injective S σ.injective).ge
  have he : S.image σ = S := Finset.eq_of_subset_of_card_le hsub hcard
  have hkin : σ k ∈ S.image σ := by
    rw [he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hkin
  have hik' : i = k := σ.injective hik
  subst i
  exact lt_irrefl k.val (Finset.mem_filter.mp hi).2

/-- Every actual selected subdiagonal belongs to exactly one forced upper interval.
Existence comes from the whole permutation; uniqueness comes from forced disjointness. -/
theorem hessenberg_lower_interval_unique {N : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i : Fin N, i.val ≤ (σ i).val + 1) (k : Fin N)
    (hk : (σ k).val < k.val) :
    ∃! i : Fin N, i.val < k.val ∧ k.val ≤ (σ i).val := by
  obtain ⟨i, hi, hik⟩ := permutation_lower_crossing σ k hk
  refine ⟨i, ⟨hi, hik⟩, ?_⟩
  intro j hj
  by_contra hne
  have h := hessenberg_upper_intervals_disjoint σ hσ j i
    (by omega) (by omega) hne k
  exact h ⟨⟨hj.1.le, hj.2⟩, hi.le, hik⟩

/-- Every original state belongs to exactly one complete upper interval, including
singleton diagonals. The entire disjoint interval partition is produced by the permutation. -/
theorem hessenberg_interval_partition {N : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i : Fin N, i.val ≤ (σ i).val + 1) (k : Fin N) :
    ∃! i : Fin N, i.val ≤ (σ i).val ∧ i.val ≤ k.val ∧ k.val ≤ (σ i).val := by
  have hex : ∃ i : Fin N, i.val ≤ (σ i).val ∧ i.val ≤ k.val ∧ k.val ≤ (σ i).val := by
    by_cases hk : k.val ≤ (σ k).val
    · exact ⟨k, hk, le_rfl, hk⟩
    · obtain ⟨i, hi, hik⟩ := permutation_lower_crossing σ k (lt_of_not_ge hk)
      exact ⟨i, by omega, hi.le, hik⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hne
  exact hessenberg_upper_intervals_disjoint σ hσ j i hj.1 hi.1 hne k
    ⟨hj.2, hi.2⟩

end SkewCornerDescent.Matrix
