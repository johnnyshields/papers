/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergTwoIntervalCycles

/-!
# Exact finite indexing of marked one-shy determinant activities

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The marked long upper occurrence remains part of the index. At cost two the two
possible marks on a disjoint pair product are distinct, as required by Leibniz's
rule; equal response values never merge original positions.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Actual finite positions of a complete long interval and a disjoint adjacent pair. -/
@[ext]
structure OneShyIntervalPair (N m : ℕ) where
  longStart : Fin N
  longEnd : Fin N
  pairStart : Fin N
  pairEnd : Fin N
  longLength : longEnd.val - longStart.val = m - 1
  pairLength : pairEnd.val = pairStart.val + 1
  disjoint : Disjoint (Finset.Icc longStart longEnd) (Finset.Icc pairStart pairEnd)

instance {N m : ℕ} : Fintype (OneShyIntervalPair N m) := by
  classical
  apply Fintype.ofInjective
    (fun p : OneShyIntervalPair N m => (p.longStart, p.longEnd, p.pairStart, p.pairEnd))
  intro p q he
  have hc : p.longStart = q.longStart ∧ p.longEnd = q.longEnd ∧
      p.pairStart = q.pairStart ∧ p.pairEnd = q.pairEnd := by
    simpa only [Prod.mk.injEq] using he
  exact OneShyIntervalPair.ext hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

/-- A whole original admissible permutation and its marked one-shy upper occurrence. -/
abbrev MarkedOneShyPermutation (N m : ℕ) :=
  {p : Equiv.Perm (Fin N) × Fin N //
    (∀ x : Fin N, x.val ≤ (p.1 x).val + 1) ∧
      (Finset.univ.filter (fun x : Fin N => (p.1 x).val < x.val)).card = m ∧
      (p.1 p.2).val - p.2.val = m - 1}

/-- The complete two-cycle construction supplies every predicate of the marked
original permutation, rather than assuming a permutation correspondence. -/
def oneShyPairToPermutation {N m : ℕ} (hm : 2 ≤ m) (p : OneShyIntervalPair N m) :
    MarkedOneShyPermutation N m := by
  let σ := (Fin.cycleIcc p.longStart p.longEnd).symm *
    (Fin.cycleIcc p.pairStart p.pairEnd).symm
  refine ⟨(σ, p.longStart), ?_⟩
  obtain ⟨hσ, hcost, hlen, _, _⟩ := two_interval_cycle_one_shy
    p.longStart p.longEnd p.pairStart p.pairEnd hm p.longLength p.pairLength p.disjoint
  exact ⟨hσ, hcost, hlen⟩

/-- The constructed whole permutation attains both literal endpoints and has
no further upper activity. The long and pair lengths produce their ordering. -/
theorem oneShyPairToPermutation_positions {N m : ℕ} (hm : 2 ≤ m)
    (p : OneShyIntervalPair N m) :
    let σ := (oneShyPairToPermutation hm p).val.1
    σ p.longStart = p.longEnd ∧ σ p.pairStart = p.pairEnd ∧
      ∀ x : Fin N, x ≠ p.longStart → x ≠ p.pairStart → (σ x).val ≤ x.val := by
  have hij : p.longStart ≤ p.longEnd := by
    change p.longStart.val ≤ p.longEnd.val
    have h := p.longLength
    omega
  have hkl : p.pairStart ≤ p.pairEnd := by
    change p.pairStart.val ≤ p.pairEnd.val
    have h := p.pairLength
    omega
  exact two_interval_cycle_upper_data _ _ _ _ hij hkl p.disjoint

/-- The disjoint actual pair cannot start at the marked long interval's start. -/
theorem oneShyPair_starts_ne {N m : ℕ} (hm : 2 ≤ m) (p : OneShyIntervalPair N m) :
    p.pairStart ≠ p.longStart := by
  intro he
  have hij : p.longStart ≤ p.longEnd := by
    change p.longStart.val ≤ p.longEnd.val
    have h := p.longLength
    omega
  have hkl : p.pairStart ≤ p.pairEnd := by
    change p.pairStart.val ≤ p.pairEnd.val
    have h := p.pairLength
    omega
  have hi : p.longStart ∈ Finset.Icc p.longStart p.longEnd :=
    Finset.mem_Icc.mpr ⟨le_rfl, hij⟩
  have hk : p.longStart ∈ Finset.Icc p.pairStart p.pairEnd := by
    rw [← he]
    exact Finset.mem_Icc.mpr ⟨le_rfl, hkl⟩
  exact Finset.disjoint_left.mp p.disjoint hi hk

/-- The marked occurrence keeps the two possible cost-two marks distinct;
no two different literal interval pairs represent the same marked permutation. -/
theorem oneShyPairToPermutation_injective {N m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (oneShyPairToPermutation (N := N) hm) := by
  intro p q he
  let σ := (oneShyPairToPermutation hm p).val.1
  let τ := (oneShyPairToPermutation hm q).val.1
  have hv := congrArg Subtype.val he
  have hword : σ = τ := congrArg Prod.fst hv
  have hstart : p.longStart = q.longStart := congrArg Prod.snd hv
  obtain ⟨hpi, hpk, _⟩ := oneShyPairToPermutation_positions hm p
  obtain ⟨hqi, hqk, hotherq⟩ := oneShyPairToPermutation_positions hm q
  have hend : p.longEnd = q.longEnd := by
    calc
      _ = σ p.longStart := hpi.symm
      _ = τ q.longStart := by rw [hword, hstart]
      _ = _ := hqi
  have hpair : p.pairStart = q.pairStart := by
    by_contra hne
    have hsep := oneShyPair_starts_ne hm p
    have hnot : p.pairStart ≠ q.longStart := by rw [← hstart]; exact hsep
    have hbound := hotherq p.pairStart hnot hne
    change (τ p.pairStart).val ≤ p.pairStart.val at hbound
    have hpval : (τ p.pairStart).val = p.pairEnd.val := by
      rw [← hword]
      exact congrArg Fin.val hpk
    have hpnext := p.pairLength
    omega
  have hlast : p.pairEnd = q.pairEnd := by
    calc
      _ = σ p.pairStart := hpk.symm
      _ = τ q.pairStart := by rw [hword, hpair]
      _ = _ := hqk
  exact OneShyIntervalPair.ext hstart hend hpair hlast

/-- Every actual marked original permutation has its complete literal interval
pair representation, supplied by the cost classification and whole-cycle reconstruction. -/
theorem oneShyPairToPermutation_surjective {N m : ℕ} (hm : 2 ≤ m) :
    Function.Surjective (oneShyPairToPermutation (N := N) hm) := by
  rintro ⟨⟨σ, i⟩, hσ, hcost, hlen⟩
  obtain ⟨k, _, hpair, hdis, heq⟩ := hessenberg_one_shy_eq_two_cycles σ hσ hm hcost i hlen
  let p : OneShyIntervalPair N m :=
    ⟨i, σ i, k, σ k, hlen, hpair, hdis⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  change (((Fin.cycleIcc i (σ i)).symm * (Fin.cycleIcc k (σ k)).symm), i) = (σ, i)
  exact Prod.ext heq.symm rfl

/-- Actual marked original permutation occurrences and complete literal interval
pairs have a proved finite bijection, without identifying equal response values. -/
def oneShyPairEquivMarkedPermutation {N m : ℕ} (hm : 2 ≤ m) :
    OneShyIntervalPair N m ≃ MarkedOneShyPermutation N m :=
  Equiv.ofBijective (oneShyPairToPermutation hm)
    ⟨oneShyPairToPermutation_injective hm, oneShyPairToPermutation_surjective hm⟩

/-- Reindexing the complete marked frontier preserves every original occurrence.
In particular the two marks at cost two remain separate summands. -/
theorem one_shy_marked_sum_eq_interval_pairs {N m : ℕ} (hm : 2 ≤ m)
    {R : Type*} [AddCommMonoid R] (G : MarkedOneShyPermutation N m → R) :
    (∑ p : MarkedOneShyPermutation N m, G p) =
      ∑ p : OneShyIntervalPair N m, G (oneShyPairToPermutation hm p) := by
  classical
  exact (Equiv.sum_comp (oneShyPairEquivMarkedPermutation hm) G).symm

/-- The smallest two-pair determinant term really has two distinct marked
occurrences, although its whole original permutation is the same.

**No consumer here:** this witnesses the multiplicity that a cost-two
frontier reindexing must retain. -/
theorem one_shy_cost_two_retains_two_marks :
    ∃ p q : OneShyIntervalPair 4 2, p ≠ q ∧
      (oneShyPairToPermutation (by decide) p).val.1 =
        (oneShyPairToPermutation (by decide) q).val.1 ∧
      oneShyPairToPermutation (by decide) p ≠ oneShyPairToPermutation (by decide) q := by
  let p : OneShyIntervalPair 4 2 := ⟨0, 1, 2, 3, by decide, by decide, by decide⟩
  let q : OneShyIntervalPair 4 2 := ⟨2, 3, 0, 1, by decide, by decide, by decide⟩
  have hpq : p ≠ q := by
    intro he
    have hv := congrArg (fun z : OneShyIntervalPair 4 2 => z.longStart.val) he
    change (0 : ℕ) = 2 at hv
    omega
  obtain ⟨hpi, hpk, hpo⟩ := oneShyPairToPermutation_positions (by decide) p
  obtain ⟨hqi, hqk, hqo⟩ := oneShyPairToPermutation_positions (by decide) q
  have hword : (oneShyPairToPermutation (by decide) p).val.1 =
      (oneShyPairToPermutation (by decide) q).val.1 := by
    apply hessenberg_two_upper_positions_unique _ _
      (oneShyPairToPermutation (by decide) p).property.1
      (oneShyPairToPermutation (by decide) q).property.1 (0 : Fin 4) (2 : Fin 4)
      (hpi.trans hqk.symm) (hpk.trans hqi.symm)
    · exact hpo
    · intro x hx0 hx2
      exact hqo x hx2 hx0
  refine ⟨p, q, hpq, hword, ?_⟩
  intro he
  exact hpq (oneShyPairToPermutation_injective (by decide) he)

/-- The raw whole-permutation and upper-position filters give precisely the
actual marked permutation family, with no assumed counting correspondence. -/
theorem one_shy_marked_sum_eq_filtered {N m : ℕ} (hm : 2 ≤ m)
    {R : Type*} [AddCommMonoid R] (F : Equiv.Perm (Fin N) → Fin N → R) :
    (∑ p : MarkedOneShyPermutation N m, F p.val.1 p.val.2) =
      ∑ σ : Equiv.Perm (Fin N),
        if (∀ j : Fin N, j.val ≤ (σ j).val + 1) ∧
            (Finset.univ.filter (fun j : Fin N => (σ j).val < j.val)).card = m then
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val),
            if (σ i).val - i.val = m - 1 then F σ i else 0
        else 0 := by
  classical
  let pred := fun p : Equiv.Perm (Fin N) × Fin N =>
    (∀ j : Fin N, j.val ≤ (p.1 j).val + 1) ∧
      (Finset.univ.filter (fun j : Fin N => (p.1 j).val < j.val)).card = m ∧
      (p.1 p.2).val - p.2.val = m - 1
  have hsub : (∑ p : MarkedOneShyPermutation N m, F p.val.1 p.val.2) =
      ∑ p ∈ Finset.univ.filter pred, F p.1 p.2 := by
    exact (Finset.sum_subtype (p := pred) (Finset.univ.filter pred)
      (fun p => by simp) (fun p => F p.1 p.2)).symm
  rw [hsub, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hc : (∀ j : Fin N, j.val ≤ (σ j).val + 1) ∧
      (Finset.univ.filter (fun j : Fin N => (σ j).val < j.val)).card = m
  · rw [ite_eq_left hc, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hlen : (σ i).val - i.val = m - 1
    · have hiup : i.val ≤ (σ i).val := by omega
      have hpi : pred (σ, i) := ⟨hc.1, hc.2, hlen⟩
      rw [ite_eq_left hpi, ite_eq_left hiup, ite_eq_left hlen]
    · have hpi : ¬ pred (σ, i) := fun he => hlen he.2.2
      rw [ite_eq_right hpi]
      by_cases hiup : i.val ≤ (σ i).val
      · rw [ite_eq_left hiup, ite_eq_right hlen]
      · rw [ite_eq_right hiup]
  · rw [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro i _
    have hn : ¬ pred (σ, i) := by
      intro he
      exact hc ⟨he.1, he.2.1⟩
    rw [ite_eq_right hn]

/-- The complete filtered marked sum reindexes to actual disjoint interval
pairs. No original position or cost-two marker is removed. -/
theorem one_shy_filtered_sum_eq_interval_pairs {N m : ℕ} (hm : 2 ≤ m)
    {R : Type*} [AddCommMonoid R] (F : Equiv.Perm (Fin N) → Fin N → R) :
    (∑ σ : Equiv.Perm (Fin N),
      if (∀ j : Fin N, j.val ≤ (σ j).val + 1) ∧
          (Finset.univ.filter (fun j : Fin N => (σ j).val < j.val)).card = m then
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val),
          if (σ i).val - i.val = m - 1 then F σ i else 0
      else 0) =
      ∑ p : OneShyIntervalPair N m,
        F (oneShyPairToPermutation hm p).val.1 p.longStart := by
  rw [← one_shy_marked_sum_eq_filtered hm F]
  exact one_shy_marked_sum_eq_interval_pairs hm (fun p => F p.val.1 p.val.2)

/-- Removing the marked long occurrence leaves its full actual adjacent-pair
activity, without dividing by the long activity or assuming it nonzero. -/
theorem oneShyPair_remaining_activity {N m : ℕ} (hm : 2 ≤ m)
    (p : OneShyIntervalPair N m) {R : Type*} [CommRing R]
    (A : Matrix (Fin N) (Fin N) R) (w : Fin N → R) (hdiag : ∀ j, A j j * w j = 1) :
    let σ := (oneShyPairToPermutation hm p).val.1
    let upper := Finset.univ.filter (fun j => j.val ≤ (σ j).val)
    (∏ j ∈ upper.erase p.longStart, A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l) =
      A p.pairStart p.pairEnd * ∏ l ∈ Finset.Icc p.pairStart p.pairEnd, w l := by
  classical
  let σ := (oneShyPairToPermutation hm p).val.1
  let upper := Finset.univ.filter (fun j => j.val ≤ (σ j).val)
  obtain ⟨_, hpair, hother⟩ := oneShyPairToPermutation_positions hm p
  have hk : p.pairStart ∈ upper.erase p.longStart := by
    apply Finset.mem_erase.mpr
    refine ⟨oneShyPair_starts_ne hm p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hpair]
    have h := p.pairLength
    omega
  change (∏ j ∈ upper.erase p.longStart, A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l) = _
  rw [Finset.prod_eq_single p.pairStart]
  · rw [hpair]
  · intro j hj hjk
    have hji := (Finset.mem_erase.mp hj).1
    have hjup : j.val ≤ (σ j).val :=
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2
    have hbound := hother j hji hjk
    change (σ j).val ≤ j.val at hbound
    have he : σ j = j := Fin.ext (Nat.le_antisymm hbound hjup)
    simpa only [he, Finset.Icc_self, Finset.prod_singleton] using hdiag j
  · intro hnot
    exact False.elim (hnot hk)

/-- The complete filtered original marked activity sum is precisely the sum of
its long payload times its genuine disjoint pair activity, with all weights retained. -/
theorem one_shy_filtered_activity_sum {N m : ℕ} (hm : 2 ≤ m)
    {R : Type*} [CommRing R] (A G : Matrix (Fin N) (Fin N) R)
    (w : Fin N → R) (hdiag : ∀ j, A j j * w j = 1) :
    let activity := fun (σ : Equiv.Perm (Fin N)) j =>
      A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l
    (∑ σ : Equiv.Perm (Fin N),
      if (∀ j : Fin N, j.val ≤ (σ j).val + 1) ∧
          (Finset.univ.filter (fun j : Fin N => (σ j).val < j.val)).card = m then
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val),
          if (σ i).val - i.val = m - 1 then
            (G i (σ i) * ∏ l ∈ Finset.Icc i (σ i), w l) *
              ∏ j ∈ (Finset.univ.filter (fun j => j.val ≤ (σ j).val)).erase i, activity σ j
          else 0
      else 0) =
      ∑ p : OneShyIntervalPair N m,
        (G p.longStart p.longEnd * ∏ l ∈ Finset.Icc p.longStart p.longEnd, w l) *
          (A p.pairStart p.pairEnd * ∏ l ∈ Finset.Icc p.pairStart p.pairEnd, w l) := by
  classical
  dsimp only
  let f := fun (σ : Equiv.Perm (Fin N)) (i : Fin N) =>
    (G i (σ i) * ∏ l ∈ Finset.Icc i (σ i), w l) *
      ∏ j ∈ (Finset.univ.filter (fun j => j.val ≤ (σ j).val)).erase i,
        A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l
  change (∑ σ : Equiv.Perm (Fin N),
    if (∀ j : Fin N, j.val ≤ (σ j).val + 1) ∧
        (Finset.univ.filter (fun j : Fin N => (σ j).val < j.val)).card = m then
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ (σ i).val),
        if (σ i).val - i.val = m - 1 then f σ i else 0
    else 0) = _
  rw [one_shy_filtered_sum_eq_interval_pairs (N := N) (m := m) (R := R) hm f]
  apply Finset.sum_congr rfl
  intro p _
  dsimp only [f]
  rw [oneShyPair_remaining_activity hm p A w hdiag]
  have hp := (oneShyPairToPermutation_positions hm p).1
  rw [hp]

end SkewCornerDescent.Matrix
