/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.HessenbergPermutationCost
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Interval.Finset.Fin

/-!
# The unique forward interval at the first-fresh cost

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
A forward jump spending the entire selected-subdiagonal cost leaves no other
forward jump. This turns the full permutation frontier into interval terms.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Once a Hessenberg permutation spends its entire cost on one forward interval,
every other upper entry is diagonal. No multiplicity or permutation is removed by assumption. -/
theorem hessenberg_permutation_unique_forward {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1)
    (i : Fin n) (hi : (i : ℕ) ≤ (σ i : ℕ))
    (hcost : (σ i : ℕ) - (i : ℕ) =
      (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card)
    (k : Fin n) (hki : k ≠ i) : (σ k : ℕ) ≤ (k : ℕ) := by
  classical
  let s := Finset.univ.filter (fun k : Fin n => (k : ℕ) ≤ (σ k : ℕ))
  let f := fun k : Fin n => (((σ k : ℕ) : ℤ) - (k : ℕ))
  have his : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hsum := hessenberg_permutation_forward_sum σ hσ
  have hsplit := Finset.sum_erase_add s f his
  have hzero : ∑ l ∈ s.erase i, f l = 0 := by
    change (∑ l ∈ s.erase i, f l) + f i = ∑ l ∈ s, f l at hsplit
    change (∑ l ∈ s, f l) = _ at hsum
    have hfi : f i =
        ((Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card : ℤ) := by
      dsimp only [f]
      omega
    rw [← hfi] at hsum
    omega
  by_cases hk : (k : ℕ) ≤ (σ k : ℕ)
  · have hks : k ∈ s.erase i :=
      Finset.mem_erase.mpr ⟨hki, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    have hle : f k ≤ ∑ l ∈ s.erase i, f l := by
      apply Finset.single_le_sum (f := f) (a := k)
      · intro l hl
        have hl' := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hl)).2
        dsimp only [f]
        omega
      · exact hks
    rw [hzero] at hle
    dsimp only [f] at hle
    omega
  · omega

/-- A cost-exhausting forward jump determines every original position of the interval cycle.
Positions outside the interval are fixed, and every position inside steps down exactly once. -/
theorem hessenberg_permutation_interval_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1)
    (i : Fin n) (hi : (i : ℕ) ≤ (σ i : ℕ))
    (hcost : (σ i : ℕ) - (i : ℕ) =
      (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card)
    (k : Fin n) :
    (σ k : ℕ) = if k = i then (σ i : ℕ) else
      if (i : ℕ) < (k : ℕ) ∧ (k : ℕ) ≤ (σ i : ℕ) then (k : ℕ) - 1 else (k : ℕ) := by
  classical
  have hother := hessenberg_permutation_unique_forward σ hσ i hi hcost
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction k using Fin.induction with
    | zero =>
      by_cases hki : (0 : Fin (n + 1)) = i
      · simp [hki]
      · have hk := hother 0 hki
        simp only [Fin.val_zero] at hk
        simp only [hki, ↓reduceIte, Fin.val_zero, Nat.not_lt_zero, false_and]
        omega
    | succ k ih =>
      by_cases hki : k.succ = i
      · simp [hki]
      · have hk := hother k.succ hki
        have hk' := hσ k.succ
        rw [ite_eq_right hki]
        by_cases hwin : (i : ℕ) < (k.succ : ℕ) ∧ (k.succ : ℕ) ≤ (σ i : ℕ)
        · rw [ite_eq_left hwin]
          obtain ⟨y, hy⟩ := σ.surjective k.castSucc
          have hyi : y ≠ i := by
            intro he
            subst y
            have hv := congrArg Fin.val hy
            simp only [Fin.val_castSucc, Fin.val_succ] at hv hwin
            omega
          have hybound := hother y hyi
          have hybound' := hσ y
          have hyv := congrArg Fin.val hy
          have hyp : y ≠ k.castSucc := by
            intro he
            subst y
            have hp := congrArg Fin.val hy
            split_ifs at ih with hpi hprev
            · rw [hpi] at hp
              simp only [Fin.val_succ] at hp hwin
              omega
            · simp only [Fin.val_castSucc] at ih hp
              omega
            · simp only [Fin.val_castSucc, Fin.val_succ] at hprev hwin
              have hne := Fin.val_ne_of_ne hpi
              simp only [Fin.val_castSucc] at hne
              omega
          have hey : y = k.succ := by
            apply Fin.ext
            have hne := Fin.val_ne_of_ne hyp
            simp only [Fin.val_castSucc, Fin.val_succ] at hyv hne ⊢
            omega
          rw [hey] at hy
          have hv := congrArg Fin.val hy
          simp only [Fin.val_castSucc, Fin.val_succ] at hv ⊢
          omega
        · rw [ite_eq_right hwin]
          by_contra hne
          have hdown : (σ k.succ : ℕ) = (k.castSucc : ℕ) := by
            simp only [Fin.val_castSucc, Fin.val_succ] at hk hk' hne ⊢
            omega
          by_cases hj : (σ i : ℕ) = (k.castSucc : ℕ)
          · have he : σ k.succ = σ i := Fin.ext (hdown.trans hj.symm)
            exact hki (σ.injective he)
          · have hpi : k.castSucc ≠ i := by
              intro he
              have hv := congrArg Fin.val he
              simp only [Fin.val_castSucc, Fin.val_succ] at hv hwin hj
              omega
            have hpwin : ¬ ((i : ℕ) < (k.castSucc : ℕ) ∧
                (k.castSucc : ℕ) ≤ (σ i : ℕ)) := by
              simp only [Fin.val_castSucc, Fin.val_succ] at hwin hj ⊢
              omega
            rw [ite_eq_right hpi, ite_eq_right hpwin] at ih
            have he : σ k.succ = σ k.castSucc := Fin.ext (hdown.trans ih.symm)
            have hv := congrArg Fin.val (σ.injective he)
            simp only [Fin.val_castSucc, Fin.val_succ] at hv
            omega

/-- The first-fresh interval permutation is Mathlib's inverse literal interval cycle. -/
theorem hessenberg_permutation_eq_interval_cycle {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1)
    (i : Fin n) (hi : (i : ℕ) ≤ (σ i : ℕ))
    (hcost : (σ i : ℕ) - (i : ℕ) =
      (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card) :
    σ = (Fin.cycleIcc i (σ i)).symm := by
  classical
  let _ : NeZero n := ⟨by have := i.isLt; omega⟩
  apply Equiv.ext
  intro k
  apply (Fin.cycleIcc i (σ i)).injective
  rw [Equiv.apply_symm_apply]
  by_cases hki : k = i
  · subst k
    exact Fin.cycleIcc_of_last hi
  · have hv := hessenberg_permutation_interval_apply σ hσ i hi hcost k
    rw [ite_eq_right hki] at hv
    by_cases hwin : (i : ℕ) < (k : ℕ) ∧ (k : ℕ) ≤ (σ i : ℕ)
    · rw [ite_eq_left hwin] at hv
      have hleft : i ≤ σ k := by change (i : ℕ) ≤ (σ k : ℕ); omega
      have hright : σ k < σ i := by change (σ k : ℕ) < (σ i : ℕ); omega
      rw [Fin.cycleIcc_of_ge_of_lt hleft hright]
      apply Fin.ext
      rw [Fin.val_add_one_of_lt' (by have := k.isLt; omega)]
      omega
    · rw [ite_eq_right hwin] at hv
      rw [show σ k = k from Fin.ext hv]
      by_cases hleft : k < i
      · exact Fin.cycleIcc_of_lt hleft
      · have hright : σ i < k := by
          have hne := Fin.val_ne_of_ne hki
          change ¬ (k : ℕ) < (i : ℕ) at hleft
          change (σ i : ℕ) < (k : ℕ)
          omega
        exact Fin.cycleIcc_of_gt hright

/-- The first-fresh contraction has exactly the paper's selected-subdiagonal sign. -/
theorem hessenberg_permutation_interval_sign {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1)
    (i : Fin n) (hi : (i : ℕ) ≤ (σ i : ℕ))
    (hcost : (σ i : ℕ) - (i : ℕ) =
      (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card) :
    Equiv.Perm.sign σ = (-1) ^ ((σ i : ℕ) - (i : ℕ)) := by
  calc
    _ = Equiv.Perm.sign ((Fin.cycleIcc i (σ i))⁻¹) :=
      congrArg Equiv.Perm.sign (hessenberg_permutation_eq_interval_cycle σ hσ i hi hcost)
    _ = Equiv.Perm.sign (Fin.cycleIcc i (σ i)) := Equiv.Perm.sign_inv _
    _ = _ := Fin.sign_cycleIcc_of_le hi

/-- The inverse literal interval cycle makes one forward jump and otherwise steps down
inside the interval. This also covers the zero-length identity cycle. -/
theorem inverse_interval_cycle_apply {n : ℕ} (i j : Fin n) (hij : i ≤ j)
    (k : Fin n) :
    ((Fin.cycleIcc i j).symm k : ℕ) =
      if k = i then (j : ℕ) else
        if (i : ℕ) < (k : ℕ) ∧ (k : ℕ) ≤ (j : ℕ) then (k : ℕ) - 1 else (k : ℕ) := by
  classical
  let _ : NeZero n := ⟨by have := i.isLt; omega⟩
  by_cases hki : k = i
  · subst k
    rw [ite_eq_left rfl]
    have he : (Fin.cycleIcc i j).symm i = j := by
      apply (Fin.cycleIcc i j).injective
      rw [Equiv.apply_symm_apply, Fin.cycleIcc_of_last hij]
    exact congrArg Fin.val he
  · rw [ite_eq_right hki]
    by_cases hwin : (i : ℕ) < (k : ℕ) ∧ (k : ℕ) ≤ (j : ℕ)
    · rw [ite_eq_left hwin]
      let p : Fin n := ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩
      have hp : Fin.cycleIcc i j p = k := by
        rw [Fin.cycleIcc_of_ge_of_lt
          (show i ≤ p by change (i : ℕ) ≤ (p : ℕ); dsimp [p]; omega)
          (show p < j by change (p : ℕ) < (j : ℕ); dsimp [p]; omega)]
        apply Fin.ext
        rw [Fin.val_add_one_of_lt' (by dsimp [p]; have := k.isLt; omega)]
        dsimp [p]
        omega
      have he : (Fin.cycleIcc i j).symm k = p := by
        apply (Fin.cycleIcc i j).injective
        rw [Equiv.apply_symm_apply, hp]
      exact congrArg Fin.val he
    · rw [ite_eq_right hwin]
      have hp : Fin.cycleIcc i j k = k := by
        by_cases hk : k < i
        · exact Fin.cycleIcc_of_lt hk
        · apply Fin.cycleIcc_of_gt
          have hne := Fin.val_ne_of_ne hki
          change ¬ (k : ℕ) < (i : ℕ) at hk
          change (j : ℕ) < (k : ℕ)
          omega
      have he : (Fin.cycleIcc i j).symm k = k := by
        apply (Fin.cycleIcc i j).injective
        rw [Equiv.apply_symm_apply, hp]
      exact congrArg Fin.val he

/-- Every literal interval supplies a valid Hessenberg permutation. -/
theorem inverse_interval_cycle_hessenberg {n : ℕ} (i j : Fin n) (hij : i ≤ j) :
    ∀ k : Fin n, (k : ℕ) ≤ ((Fin.cycleIcc i j).symm k : ℕ) + 1 := by
  intro k
  rw [inverse_interval_cycle_apply i j hij k]
  split_ifs with hki hwin
  · subst k
    exact Nat.le_succ_of_le hij
  · omega
  · omega

/-- The selected-subdiagonal cost of an inverse interval cycle is its literal length,
so every eligible interval occurs on the complete permutation frontier. -/
theorem inverse_interval_cycle_cost {n : ℕ} (i j : Fin n) (hij : i ≤ j) :
    (Finset.univ.filter (fun k : Fin n =>
      ((Fin.cycleIcc i j).symm k : ℕ) < (k : ℕ))).card = (j : ℕ) - (i : ℕ) := by
  classical
  have hs : Finset.univ.filter (fun k : Fin n =>
      ((Fin.cycleIcc i j).symm k : ℕ) < (k : ℕ)) = Finset.Ioc i j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc]
    rw [inverse_interval_cycle_apply i j hij k]
    split_ifs with hki hwin
    · subst k
      simp [not_lt_of_ge hij]
    · change _ ↔ (i : ℕ) < (k : ℕ) ∧ (k : ℕ) ≤ (j : ℕ)
      omega
    · change _ ↔ (i : ℕ) < (k : ℕ) ∧ (k : ℕ) ≤ (j : ℕ)
      omega
  rw [hs, Fin.card_Ioc]

end SkewCornerDescent.Matrix
