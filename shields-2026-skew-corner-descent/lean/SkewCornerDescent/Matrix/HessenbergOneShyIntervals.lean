/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergAdmissibleIntervals
import SkewCornerDescent.Matrix.HessenbergPermutationCost

/-!
# One-shy complete Hessenberg intervals leave exactly one disjoint pair

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact actual permutation cost and forced interval partition classify the
remaining positive activity. No independent interval inventory or pair-count
assumption replaces the original permutation.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- The complete natural forward displacement equals the actual lower-step cost. -/
theorem hessenberg_forward_cost_nat {N : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i : Fin N, i.val ≤ (σ i).val + 1) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val),
      ((σ i).val - i.val)) =
      (Finset.univ.filter (fun i : Fin N => (σ i).val < i.val)).card := by
  have hz := hessenberg_permutation_forward_sum σ hσ
  have hc : ((∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val),
      ((σ i).val - i.val) : ℕ) : ℤ) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val),
        (((σ i).val : ℤ) - (i.val : ℤ)) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_sub (Finset.mem_filter.mp hi).2]
  exact_mod_cast hc.trans hz

/-- At total cost `m`, an actual upper interval of cost `m-1` leaves exactly
one other positive upper interval: an adjacent pair disjoint from the first.
Every other original occurrence is fixed or a forced single lower step. -/
theorem hessenberg_one_shy_disjoint_pair {N m : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i : Fin N, i.val ≤ (σ i).val + 1) (hm : 2 ≤ m)
    (hcost : (Finset.univ.filter (fun i : Fin N => (σ i).val < i.val)).card = m)
    (i : Fin N) (hi : (σ i).val - i.val = m - 1) :
    ∃ k : Fin N, k ≠ i ∧ (σ k).val = k.val + 1 ∧
      Disjoint (Finset.Icc i (σ i)) (Finset.Icc k (σ k)) ∧
      ∀ j : Fin N, j ≠ i → j ≠ k → σ j = j ∨ j.val = (σ j).val + 1 := by
  classical
  let upper := Finset.univ.filter (fun j : Fin N => j.val ≤ (σ j).val)
  let f := fun j : Fin N => (σ j).val - j.val
  have himem : i ∈ upper := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hs : (∑ j ∈ upper, f j) = m := by
    rw [hessenberg_forward_cost_nat σ hσ]
    exact hcost
  have he := Finset.add_sum_erase upper f himem
  have hrest : (∑ j ∈ upper.erase i, f j) = 1 := by
    change f i + (∑ j ∈ upper.erase i, f j) = _ at he
    change f i = m - 1 at hi
    omega
  have hex : ∃ k ∈ upper.erase i, 0 < f k := by
    by_contra hn
    push Not at hn
    have hz : (∑ k ∈ upper.erase i, f k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact Nat.eq_zero_of_le_zero (hn k hk)
    omega
  obtain ⟨k, hk, hkp⟩ := hex
  have hki : k ≠ i := (Finset.mem_erase.mp hk).1
  have hkupper : k.val ≤ (σ k).val :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hk)).2
  have hkf : f k = 1 := by
    have hle := Finset.single_le_sum (fun j (_ : j ∈ upper.erase i) => Nat.zero_le (f j)) hk
    omega
  have hkadj : (σ k).val = k.val + 1 := by
    change (σ k).val - k.val = 1 at hkf
    omega
  have he' := Finset.add_sum_erase (upper.erase i) f hk
  have hzero : (∑ j ∈ (upper.erase i).erase k, f j) = 0 := by
    omega
  refine ⟨k, hki, hkadj, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro j hji hjk
    have hiup : i.val ≤ (σ i).val := by omega
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hji
    obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp hjk
    change i.val ≤ j.val at h1
    change j.val ≤ (σ i).val at h2
    change k.val ≤ j.val at h3
    change j.val ≤ (σ k).val at h4
    exact hessenberg_upper_intervals_disjoint σ hσ i k hiup hkupper hki.symm j
      ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  · intro j hji hjk
    by_cases hjup : j.val ≤ (σ j).val
    · have hjmem : j ∈ (upper.erase i).erase k :=
        Finset.mem_erase.mpr ⟨hjk, Finset.mem_erase.mpr
          ⟨hji, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjup⟩⟩⟩
      have hle := Finset.single_le_sum
        (fun l (_ : l ∈ (upper.erase i).erase k) => Nat.zero_le (f l)) hjmem
      have hjf : f j = 0 := by omega
      change (σ j).val - j.val = 0 at hjf
      exact Or.inl (Fin.ext (by omega))
    · exact Or.inr (by have h := hσ j; omega)

/-- Two admissible original permutations with the same two possible upper
activities and endpoints coincide, including all forced lower occurrences. -/
theorem hessenberg_two_upper_positions_unique {N : ℕ} (σ τ : Equiv.Perm (Fin N))
    (hσ : ∀ j : Fin N, j.val ≤ (σ j).val + 1)
    (hτ : ∀ j : Fin N, j.val ≤ (τ j).val + 1)
    (i k : Fin N) (hi : σ i = τ i) (hk : σ k = τ k)
    (hotherσ : ∀ j : Fin N, j ≠ i → j ≠ k → (σ j).val ≤ j.val)
    (hotherτ : ∀ j : Fin N, j ≠ i → j ≠ k → (τ j).val ≤ j.val) : σ = τ := by
  have transfer (ρ θ : Equiv.Perm (Fin N))
      (hθ : ∀ j : Fin N, j.val ≤ (θ j).val + 1)
      (he1 : ρ i = θ i) (he2 : ρ k = θ k)
      (hother : ∀ j : Fin N, j ≠ i → j ≠ k → (ρ j).val ≤ j.val)
      (j : Fin N) (hj : (ρ j).val < j.val) : (θ j).val = j.val - 1 := by
    obtain ⟨a, haj, hja⟩ := permutation_lower_crossing ρ j hj
    have ha : a = i ∨ a = k := by
      by_cases hai : a = i
      · exact Or.inl hai
      · by_cases hak : a = k
        · exact Or.inr hak
        · have hle := hother a hai hak
          omega
    rcases ha with ha | ha
    · subst a
      have hbound : j.val ≤ (θ i).val := by rw [← he1]; exact hja
      exact hessenberg_forced_subdiagonals θ hθ i (by omega) j haj hbound
    · subst a
      have hbound : j.val ≤ (θ k).val := by rw [← he2]; exact hja
      exact hessenberg_forced_subdiagonals θ hθ k (by omega) j haj hbound
  apply Equiv.ext
  intro j
  by_cases hji : j = i
  · subst j
    exact hi
  by_cases hjk : j = k
  · subst j
    exact hk
  have hsle := hotherσ j hji hjk
  have htle := hotherτ j hji hjk
  have hsstep := hσ j
  have htstep := hτ j
  apply Fin.ext
  by_cases hs : (σ j).val < j.val
  · have ht := transfer σ τ hτ hi hk hotherσ j hs
    omega
  · by_cases ht : (τ j).val < j.val
    · have hs' := transfer τ σ hσ hi.symm hk.symm hotherτ j ht
      omega
    · omega

end SkewCornerDescent.Matrix
