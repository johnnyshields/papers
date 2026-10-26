/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergIntervalPermutation
import SkewCornerDescent.Matrix.HessenbergOneShyIntervals

/-!
# Actual Hessenberg permutations from two disjoint complete intervals

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The product of the held inverse interval cycles supplies every original position.
Closed interval disjointness prevents a second update of either interval's states.
No existence or permutation correspondence is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Two disjoint complete interval cycles act on their actual separate states. -/
theorem two_interval_cycle_apply {N : ℕ} (i j k l : Fin N) (hij : i ≤ j) (hkl : k ≤ l)
    (hd : Disjoint (Finset.Icc i j) (Finset.Icc k l)) (x : Fin N) :
    ((Fin.cycleIcc i j).symm * (Fin.cycleIcc k l).symm) x =
      if x ∈ Finset.Icc k l then (Fin.cycleIcc k l).symm x else (Fin.cycleIcc i j).symm x := by
  classical
  have fixed (a b x : Fin N) (hab : a ≤ b) (hx : x ∉ Finset.Icc a b) :
      (Fin.cycleIcc a b).symm x = x := by
    have hxa : x ≠ a := by
      intro he
      apply hx
      rw [he]
      exact Finset.mem_Icc.mpr ⟨le_rfl, hab⟩
    have hout : ¬ (a.val < x.val ∧ x.val ≤ b.val) := by
      intro he
      exact hx (Finset.mem_Icc.mpr ⟨he.1.le, he.2⟩)
    apply Fin.ext
    rw [inverse_interval_cycle_apply a b hab x, ite_eq_right hxa, ite_eq_right hout]
  let ρ := (Fin.cycleIcc i j).symm
  let θ := (Fin.cycleIcc k l).symm
  change ρ (θ x) = if x ∈ Finset.Icc k l then θ x else ρ x
  by_cases hx : x ∈ Finset.Icc k l
  · rw [ite_eq_left hx]
    obtain ⟨hx0, hx1⟩ := Finset.mem_Icc.mp hx
    change k.val ≤ x.val at hx0
    change x.val ≤ l.val at hx1
    have hcalc := inverse_interval_cycle_apply k l hkl x
    change (θ x).val = _ at hcalc
    have hmem : θ x ∈ Finset.Icc k l := by
      apply Finset.mem_Icc.mpr
      change k.val ≤ (θ x).val ∧ (θ x).val ≤ l.val
      by_cases he : x = k
      · rw [ite_eq_left he] at hcalc
        have hle : k.val ≤ l.val := hkl
        omega
      · have hin : k.val < x.val ∧ x.val ≤ l.val := by
          have hne : x.val ≠ k.val := fun hv => he (Fin.ext hv)
          omega
        rw [ite_eq_right he, ite_eq_left hin] at hcalc
        omega
    have hnot : θ x ∉ Finset.Icc i j := by
      intro hm
      exact Finset.disjoint_left.mp hd hm hmem
    exact fixed i j (θ x) hij hnot
  · rw [ite_eq_right hx, fixed k l x hkl hx]

/-- Every constructed two-interval permutation obeys actual Hessenberg support. -/
theorem two_interval_cycle_hessenberg {N : ℕ} (i j k l : Fin N)
    (hij : i ≤ j) (hkl : k ≤ l) (hd : Disjoint (Finset.Icc i j) (Finset.Icc k l)) :
    ∀ x : Fin N, x.val ≤
      (((Fin.cycleIcc i j).symm * (Fin.cycleIcc k l).symm) x).val + 1 := by
  intro x
  rw [two_interval_cycle_apply i j k l hij hkl hd x]
  split_ifs with hx
  · exact inverse_interval_cycle_hessenberg k l hkl x
  · exact inverse_interval_cycle_hessenberg i j hij x

/-- The two literal upper starts attain exactly their supplied endpoints, and
all other original rows are diagonal or lower steps, never extra upper activities. -/
theorem two_interval_cycle_upper_data {N : ℕ} (i j k l : Fin N)
    (hij : i ≤ j) (hkl : k ≤ l) (hd : Disjoint (Finset.Icc i j) (Finset.Icc k l)) :
    let σ := (Fin.cycleIcc i j).symm * (Fin.cycleIcc k l).symm
    σ i = j ∧ σ k = l ∧ ∀ x : Fin N, x ≠ i → x ≠ k → (σ x).val ≤ x.val := by
  classical
  have hi : i ∈ Finset.Icc i j := Finset.mem_Icc.mpr ⟨le_rfl, hij⟩
  have hk : k ∈ Finset.Icc k l := Finset.mem_Icc.mpr ⟨le_rfl, hkl⟩
  have hiout : i ∉ Finset.Icc k l := fun h => Finset.disjoint_left.mp hd hi h
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [two_interval_cycle_apply i j k l hij hkl hd i, ite_eq_right hiout]
    apply Fin.ext
    rw [inverse_interval_cycle_apply i j hij i, ite_eq_left rfl]
  · rw [two_interval_cycle_apply i j k l hij hkl hd k, ite_eq_left hk]
    apply Fin.ext
    rw [inverse_interval_cycle_apply k l hkl k, ite_eq_left rfl]
  · intro x hxi hxk
    rw [two_interval_cycle_apply i j k l hij hkl hd x]
    split_ifs with hx
    · have hv := inverse_interval_cycle_apply k l hkl x
      rw [ite_eq_right hxk] at hv
      split_ifs at hv <;> omega
    · have hv := inverse_interval_cycle_apply i j hij x
      rw [ite_eq_right hxi] at hv
      split_ifs at hv <;> omega

/-- Every pair of disjoint complete intervals occurs with its exact combined
selected cost, including zero-length intervals without deleting any position. -/
theorem two_interval_cycle_cost {N : ℕ} (i j k l : Fin N)
    (hij : i ≤ j) (hkl : k ≤ l) (hd : Disjoint (Finset.Icc i j) (Finset.Icc k l)) :
    (Finset.univ.filter (fun x : Fin N =>
      (((Fin.cycleIcc i j).symm * (Fin.cycleIcc k l).symm) x).val < x.val)).card =
      j.val - i.val + (l.val - k.val) := by
  classical
  let σ := (Fin.cycleIcc i j).symm * (Fin.cycleIcc k l).symm
  have hσ := two_interval_cycle_hessenberg i j k l hij hkl hd
  obtain ⟨hfirst, hsecond, hother⟩ := two_interval_cycle_upper_data i j k l hij hkl hd
  have hne : i ≠ k := by
    intro he
    have hi : i ∈ Finset.Icc i j := Finset.mem_Icc.mpr ⟨le_rfl, hij⟩
    have hk : i ∈ Finset.Icc k l := by rw [he]; exact Finset.mem_Icc.mpr ⟨le_rfl, hkl⟩
    exact Finset.disjoint_left.mp hd hi hk
  let U := Finset.univ.filter (fun x : Fin N => x.val ≤ (σ x).val)
  let f := fun x : Fin N => (σ x).val - x.val
  have hiU : i ∈ U := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [hfirst]; exact hij⟩
  have hkU : k ∈ U := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [hsecond]; exact hkl⟩
  have hs : (∑ x ∈ U, f x) = f i + f k := by
    calc
      _ = ∑ x ∈ ({i, k} : Finset (Fin N)), f x := by
        symm
        apply Finset.sum_subset
          (Finset.insert_subset_iff.mpr ⟨hiU, Finset.singleton_subset_iff.mpr hkU⟩)
        intro x _ hx
        have hxi : x ≠ i := by intro he; apply hx; simp [he]
        have hxk : x ≠ k := by intro he; apply hx; simp [he]
        exact Nat.sub_eq_zero_of_le (hother x hxi hxk)
      _ = _ := by simp [hne]
  have hcost := hessenberg_forward_cost_nat σ hσ
  change (∑ x ∈ U, f x) = _ at hcost
  rw [hs] at hcost
  change _ = _
  rw [← hcost]
  simp only [f, σ, hfirst, hsecond]

/-- Every actual marked one-shy frontier permutation is the product of its
complete long cycle and the one actual disjoint adjacent-pair cycle. -/
theorem hessenberg_one_shy_eq_two_cycles {N m : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ x : Fin N, x.val ≤ (σ x).val + 1) (hm : 2 ≤ m)
    (hcost : (Finset.univ.filter (fun x : Fin N => (σ x).val < x.val)).card = m)
    (i : Fin N) (hi : (σ i).val - i.val = m - 1) :
    ∃ k : Fin N, k ≠ i ∧ (σ k).val = k.val + 1 ∧
      Disjoint (Finset.Icc i (σ i)) (Finset.Icc k (σ k)) ∧
      σ = (Fin.cycleIcc i (σ i)).symm * (Fin.cycleIcc k (σ k)).symm := by
  obtain ⟨k, hki, hkadj, hdis, hrest⟩ := hessenberg_one_shy_disjoint_pair σ hσ hm hcost i hi
  have hij : i ≤ σ i := by change i.val ≤ (σ i).val; omega
  have hkl : k ≤ σ k := by change k.val ≤ (σ k).val; omega
  let ρ := (Fin.cycleIcc i (σ i)).symm * (Fin.cycleIcc k (σ k)).symm
  have hρ := two_interval_cycle_hessenberg i (σ i) k (σ k) hij hkl hdis
  obtain ⟨hfirst, hsecond, hother⟩ :=
    two_interval_cycle_upper_data i (σ i) k (σ k) hij hkl hdis
  refine ⟨k, hki, hkadj, hdis, ?_⟩
  apply hessenberg_two_upper_positions_unique σ ρ hσ hρ i k hfirst.symm hsecond.symm
  · intro x hxi hxk
    rcases hrest x hxi hxk with he | hdown
    · rw [he]
    · omega
  · exact hother

/-- Conversely, every genuine long interval and disjoint adjacent pair produces
an actual marked one-shy determinant-frontier permutation at the exact cost. -/
theorem two_interval_cycle_one_shy {N m : ℕ} (i j k l : Fin N) (hm : 2 ≤ m)
    (hlen : j.val - i.val = m - 1) (hpair : l.val = k.val + 1)
    (hd : Disjoint (Finset.Icc i j) (Finset.Icc k l)) :
    let σ := (Fin.cycleIcc i j).symm * (Fin.cycleIcc k l).symm
    (∀ x : Fin N, x.val ≤ (σ x).val + 1) ∧
      (Finset.univ.filter (fun x : Fin N => (σ x).val < x.val)).card = m ∧
      (σ i).val - i.val = m - 1 ∧ σ i = j ∧ σ k = l := by
  have hij : i ≤ j := by change i.val ≤ j.val; omega
  have hkl : k ≤ l := by change k.val ≤ l.val; omega
  obtain ⟨hfirst, hsecond, _⟩ := two_interval_cycle_upper_data i j k l hij hkl hd
  refine ⟨two_interval_cycle_hessenberg i j k l hij hkl hd, ?_, ?_, hfirst, hsecond⟩
  · rw [two_interval_cycle_cost i j k l hij hkl hd, hlen]
    omega
  · rw [hfirst]
    exact hlen

end SkewCornerDescent.Matrix
