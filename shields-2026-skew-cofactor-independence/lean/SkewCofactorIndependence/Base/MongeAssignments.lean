/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/MongeAssignments.lean
import SkewCofactorIndependence.Base.ConvexWeights

/-!
# Strict-Monge assignments

The matching layer of “Strict-Monge uncrossing” in “Strict-Monge geometry
of cofactor actions” (`sec:geometry`): `lem:feasible-uncrossing` and
`thm:monge-minor`.  Swapping an inversion preserves feasibility and lowers
cost.  A minimum over the finite feasible set is therefore the identity.
Determinants and initial forms are not defined here.  Sorry-free.
-/

namespace SkewCofactorIndependence.Base

open scoped BigOperators

/-- Every selected column lies weakly to the right of its matched row. -/
def matchingFeasible {n : ℕ} (A d : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, A i ≤ d (σ i)

/-- The total convex weight of a permutation matching. -/
def matchingCost {n : ℕ} (w : ConvexWeight) (A d : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, w.weight (d (σ i) - A i).toNat

/-- Swap the columns assigned to two rows. -/
def uncrossMatching {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    Equiv.Perm (Fin n) := (Equiv.swap i j).trans σ

@[simp] theorem uncrossMatching_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i j k : Fin n) : uncrossMatching σ i j k = σ (Equiv.swap i j k) := rfl

/-- A nonidentity permutation of an ordered finite set has an inversion. -/
theorem exists_matching_inversion {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hne : σ ≠ Equiv.refl (Fin n)) : ∃ i j, i < j ∧ σ j < σ i := by
  by_contra h
  have hm : StrictMono σ := by
    intro i j hij
    have hn : ¬ σ j < σ i := by
      intro hji
      exact h ⟨i, j, hij, hji⟩
    have hle : σ i ≤ σ j := le_of_not_gt hn
    exact lt_of_le_of_ne hle (fun he => (ne_of_lt hij) (σ.injective he))
  apply hne
  apply Equiv.ext
  intro i
  exact hm.apply_eq

/-- The feasibility part of `lem:feasible-uncrossing`. -/
theorem uncrossMatching_feasible {n : ℕ} {A d : Fin n → ℤ}
    (hA : StrictMono A) (hd : StrictMono d) {σ : Equiv.Perm (Fin n)}
    (hf : matchingFeasible A d σ) {i j : Fin n} (hij : i < j)
    (hinv : σ j < σ i) : matchingFeasible A d (uncrossMatching σ i j) := by
  intro k
  by_cases hki : k = i
  · subst k
    simpa using (hA hij).le.trans (hf j)
  by_cases hkj : k = j
  · subst k
    simpa using (hf j).trans (hd hinv).le
  simpa only [uncrossMatching_apply, Equiv.swap_apply_of_ne_of_ne hki hkj] using hf k

private theorem sum_two_rows {n : ℕ} (f : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) :
    (∑ k, f k) = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
    simp [hij.symm]
  rw [← Finset.add_sum_erase Finset.univ f hi,
    ← Finset.add_sum_erase (Finset.univ.erase i) f hj]
  ring

/-- Uncrossing strictly decreases the cost, by `lem:strict-monge`. -/
theorem uncrossMatching_cost_lt {n : ℕ} (w : ConvexWeight) {A d : Fin n → ℤ}
    (hA : StrictMono A) (hd : StrictMono d) {σ : Equiv.Perm (Fin n)}
    (hf : matchingFeasible A d σ) {i j : Fin n} (hij : i < j)
    (hinv : σ j < σ i) :
    matchingCost w A d (uncrossMatching σ i j) < matchingCost w A d σ := by
  have hpair := w.strict_monge_int (hA hij) (hd hinv) (hf j)
  have hrest :
      (∑ k ∈ (Finset.univ.erase i).erase j,
        w.weight (d (uncrossMatching σ i j k) - A k).toNat) =
      ∑ k ∈ (Finset.univ.erase i).erase j, w.weight (d (σ k) - A k).toNat := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp only [uncrossMatching_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  unfold matchingCost
  rw [sum_two_rows (fun k => w.weight (d (uncrossMatching σ i j k) - A k).toNat)
      (ne_of_lt hij),
    sum_two_rows (fun k => w.weight (d (σ k) - A k).toNat) (ne_of_lt hij)]
  simp only [uncrossMatching_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  simp only [uncrossMatching_apply] at hrest
  rw [hrest]
  linarith

/-- Every feasible cost minimizer is the increasing matching. -/
theorem matching_minimizer_eq_refl {n : ℕ} (w : ConvexWeight) {A d : Fin n → ℤ}
    (hA : StrictMono A) (hd : StrictMono d) {σ : Equiv.Perm (Fin n)}
    (hf : matchingFeasible A d σ)
    (hmin : ∀ τ, matchingFeasible A d τ → matchingCost w A d σ ≤ matchingCost w A d τ) :
    σ = Equiv.refl (Fin n) := by
  by_contra hne
  obtain ⟨i, j, hij, hinv⟩ := exists_matching_inversion σ hne
  have hswap := uncrossMatching_feasible hA hd hf hij hinv
  have hlower := uncrossMatching_cost_lt w hA hd hf hij hinv
  exact (not_lt_of_ge (hmin _ hswap)) hlower

/-- The increasing matching is feasible and minimizes cost whenever any matching is feasible. -/
theorem feasible_identity_minimizes {n : ℕ} (w : ConvexWeight) {A d : Fin n → ℤ}
    (hA : StrictMono A) (hd : StrictMono d)
    (hex : ∃ σ, matchingFeasible A d σ) :
    matchingFeasible A d (Equiv.refl (Fin n)) ∧
      ∀ τ, matchingFeasible A d τ →
        matchingCost w A d (Equiv.refl (Fin n)) ≤ matchingCost w A d τ := by
  classical
  let S : Set (Equiv.Perm (Fin n)) := {σ | matchingFeasible A d σ}
  have hs : S.Nonempty := hex
  obtain ⟨σ, hf, hmin⟩ := Set.exists_min_image S (matchingCost w A d) (Set.toFinite S) hs
  have he : σ = Equiv.refl (Fin n) := matching_minimizer_eq_refl w hA hd hf hmin
  subst σ
  exact ⟨hf, hmin⟩

/-- The feasibility equivalence in the matching layer of `thm:monge-minor`. -/
theorem matching_feasible_iff_identity {n : ℕ} (w : ConvexWeight)
    {A d : Fin n → ℤ} (hA : StrictMono A) (hd : StrictMono d) :
    (∃ σ, matchingFeasible A d σ) ↔ matchingFeasible A d (Equiv.refl (Fin n)) := by
  constructor
  · intro hex
    exact (feasible_identity_minimizes w hA hd hex).1
  · intro hf
    exact ⟨_, hf⟩

/-- Every nonidentity feasible matching has strictly higher cost than the identity. -/
theorem identity_cost_lt_matching {n : ℕ} (w : ConvexWeight) {A d : Fin n → ℤ}
    (hA : StrictMono A) (hd : StrictMono d)
    {σ : Equiv.Perm (Fin n)} (hf : matchingFeasible A d σ)
    (hne : σ ≠ Equiv.refl (Fin n)) :
    matchingCost w A d (Equiv.refl (Fin n)) < matchingCost w A d σ := by
  obtain ⟨i, j, hij, hinv⟩ := exists_matching_inversion σ hne
  have hmin := (feasible_identity_minimizes w hA hd ⟨σ, hf⟩).2
  exact lt_of_le_of_lt
    (hmin _ (uncrossMatching_feasible hA hd hf hij hinv))
    (uncrossMatching_cost_lt w hA hd hf hij hinv)

end SkewCofactorIndependence.Base
