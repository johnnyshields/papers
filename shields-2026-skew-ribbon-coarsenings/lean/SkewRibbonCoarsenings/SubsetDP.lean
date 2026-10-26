/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Defs

/-!
# The subset recurrence for the ordinary coarsening coefficient

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:recognition`, subsection
"Checking a short certificate" (`eq:subset-dp`).

For distinct positive part values `t₁, …, t_s` with multiplicities `ν`, the states are the
vectors `a : Fin s → ℕ`, `s(a) = ∑ aᵢ tᵢ`, and `D(0) = 1`,
`D(a) = η(a) ∑_{i : aᵢ > 0} D(a - eᵢ)` with `η(ν) = 1` and `η(a) = b(s(a))` otherwise.
`dpCount` is `D`; `dpCount_zero` and `dpCount_ne_zero` are its defining recurrence.
`subset_dp` proves `m_β(λ) = D(ν)`, and `partition_subset_dp` states it for an arbitrary
partition of `n` into positive parts.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-! ### Block lengths of a coarsening, peeled from the right -/

theorem gaps_empty (n : ℕ) : gaps n ∅ = {n} := by
  simp [gaps]

/-- Removing the last cut `x` of a coarsening removes the last block `n - x`. -/
theorem gaps_insert {n x : ℕ} {T : Finset ℕ} (hx : x < n) (hT : ∀ z ∈ T, z < x) :
    gaps n (insert x T) = (n - x) ::ₘ gaps x T := by
  have hxT : x ∉ T := fun h => lt_irrefl _ (hT x h)
  have hsupT : T.sup id ≤ x := Finset.sup_le fun z hz => (hT z hz).le
  have hnT : n ∉ insert x T := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · have := hT n h; omega
  unfold gaps
  have h1 : ((insert x T).filter (· < n)).sup id = x := by
    rw [Finset.filter_true_of_mem (fun z hz => by
      rcases Finset.mem_insert.1 hz with h | h
      · omega
      · have := hT z h; omega)]
    rw [Finset.sup_insert]
    simp only [id]
    exact max_eq_left hsupT
  have h2 : ((insert x T).filter (· < x)) = T.filter (· < x) := by
    rw [Finset.filter_insert, if_neg (lt_irrefl x)]
  have h3 : ∀ y ∈ T, ((insert x T).filter (· < y)) = T.filter (· < y) := by
    intro y hy
    rw [Finset.filter_insert, if_neg (by have := hT y hy; omega)]
  rw [Finset.insert_val_of_notMem hnT, Finset.insert_val_of_notMem hxT]
  simp only [Multiset.map_cons, h1, h2]
  congr 2
  exact Multiset.map_congr rfl fun y hy => by simp only [h3 y hy]

/-! ### The count of retained subsets, with the weight as a parameter -/

/-- The number of cut subsets of `S` strictly inside `(0, m)` whose blocks, for the weight
`m`, are the multiset `P`.  For `S ⊆ (0, n)` and `m = n` this is `mult n S P`. -/
def cutCount (S : Finset ℕ) (m : ℕ) (P : Multiset ℕ) : ℕ :=
  (((S.filter fun x => 0 < x ∧ x < m).powerset).filter fun T => gaps m T = P).card

theorem mult_eq_cutCount {n : ℕ} {S : Finset ℕ} (hS : IsCutSet n S) (P : Multiset ℕ) :
    mult n S P = cutCount S n P := by
  unfold mult cutCount
  have : S.filter (fun x => 0 < x ∧ x < n) = S := by
    refine Finset.filter_true_of_mem fun x hx => ?_
    have := Finset.mem_Ioo.1 (hS hx)
    exact ⟨this.1, this.2⟩
  rw [this]

theorem mem_cutSubsets {S : Finset ℕ} {m : ℕ} {P : Multiset ℕ} {T : Finset ℕ} :
    T ∈ ((S.filter fun x => 0 < x ∧ x < m).powerset).filter (fun T => gaps m T = P) ↔
      (∀ z ∈ T, z ∈ S ∧ 0 < z ∧ z < m) ∧ gaps m T = P := by
  rw [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun z hz => by have := Finset.mem_filter.1 (h1 hz); tauto, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun z hz => Finset.mem_filter.2 ⟨(h1 z hz).1, (h1 z hz).2⟩, h2⟩

theorem sup_id_mem {T : Finset ℕ} (h : T.Nonempty) : T.sup id ∈ T := by
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup T h id
  rw [hsup]; exact hi

theorem le_sup_id {T : Finset ℕ} {z : ℕ} (h : z ∈ T) : z ≤ T.sup id := Finset.le_sup (f := id) h

/-- Last-block recurrence for `cutCount`: partition the retained subsets by the length of the
last block. -/
theorem cutCount_rec (S : Finset ℕ) {m : ℕ} (hm : 0 < m) (P : Multiset ℕ) :
    cutCount S m P = ∑ v ∈ P.toFinset,
      if v = m then (if P = {m} then 1 else 0)
      else if 0 < v ∧ v < m ∧ m - v ∈ S then cutCount S (m - v) (P.erase v) else 0 := by
  set A : Finset (Finset ℕ) :=
    ((S.filter fun x => 0 < x ∧ x < m).powerset).filter fun T => gaps m T = P with hA
  have hmemA : ∀ T, T ∈ A ↔ (∀ z ∈ T, z ∈ S ∧ 0 < z ∧ z < m) ∧ gaps m T = P := by
    intro T
    rw [hA, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun z hz => by have := Finset.mem_filter.1 (h1 hz); tauto, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun z hz => Finset.mem_filter.2 ⟨(h1 z hz).1, (h1 z hz).2⟩, h2⟩
  -- the last block lies in `P`
  have hmaps : Set.MapsTo (fun T : Finset ℕ => m - T.sup id) (A : Set (Finset ℕ))
      (P.toFinset : Set ℕ) := by
    intro T hT
    have hT := (hmemA T).1 hT
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    by_cases hne : T.Nonempty
    · set x := T.sup id with hx
      have hxT : x ∈ T := sup_id_mem hne
      have hxm : x < m := (hT.1 x hxT).2.2
      have hlt : ∀ z ∈ T.erase x, z < x := fun z hz =>
        lt_of_le_of_ne (le_sup_id (Finset.mem_of_mem_erase hz)) (Finset.ne_of_mem_erase hz)
      have := gaps_insert hxm hlt
      rw [Finset.insert_erase hxT] at this
      rw [← hT.2, this]
      exact Multiset.mem_cons_self _ _
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      rw [← hT.2, gaps_empty]
      simp
  rw [cutCount, ← hA, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hvP : v ∈ P := Multiset.mem_toFinset.1 hv
  by_cases hvm : v = m
  · subst hvm
    rw [if_pos rfl]
    have key : ∀ T ∈ A.filter (fun T => v - T.sup id = v), T = ∅ := by
      intro T hT
      rw [Finset.mem_filter] at hT
      have h1 := (hmemA T).1 hT.1
      by_contra hne
      have hne' : T.Nonempty := Finset.nonempty_iff_ne_empty.2 hne
      have := (h1.1 _ (sup_id_mem hne')).2.1
      omega
    by_cases hP : P = {v}
    · rw [if_pos hP]
      rw [Finset.card_eq_one]
      refine ⟨∅, ?_⟩
      ext T
      simp only [Finset.mem_singleton]
      constructor
      · exact key T
      · rintro rfl
        rw [Finset.mem_filter, hmemA]
        refine ⟨⟨by simp, by rw [gaps_empty, hP]⟩, by simp⟩
    · rw [if_neg hP, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro T hT
      have := key T hT
      subst this
      have h1 := ((hmemA _).1 (Finset.mem_filter.1 hT).1).2
      rw [gaps_empty] at h1
      exact hP h1.symm
  · rw [if_neg hvm]
    by_cases hcond : 0 < v ∧ v < m ∧ m - v ∈ S
    · rw [if_pos hcond]
      obtain ⟨hv0, hvm', hxS⟩ := hcond
      set x := m - v with hx
      rw [cutCount]
      refine Finset.card_nbij' (fun T => T.erase x) (fun T => insert x T) ?_ ?_ ?_ ?_
      · intro T hT
        simp only [Finset.mem_coe, Finset.mem_filter] at hT ⊢
        have h1 := (hmemA T).1 hT.1
        have hne : T.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          rintro rfl
          simp at hT
          omega
        have hsup : T.sup id = x := by
          have := (h1.1 _ (sup_id_mem hne)).2.2
          omega
        have hxT : x ∈ T := hsup ▸ sup_id_mem hne
        have hlt : ∀ z ∈ T.erase x, z < x := fun z hz => by
          have := le_sup_id (Finset.mem_of_mem_erase hz)
          have := Finset.ne_of_mem_erase hz
          omega
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_powerset, Finset.subset_iff]
          intro z hz
          rw [Finset.mem_filter]
          have := h1.1 z (Finset.mem_of_mem_erase hz)
          exact ⟨this.1, this.2.1, hlt z hz⟩
        · have hg := gaps_insert (n := m) (x := x) (by omega) hlt
          rw [Finset.insert_erase hxT, h1.2] at hg
          have hv' : m - x = v := by omega
          rw [hv'] at hg
          rw [hg, Multiset.erase_cons_head]
      · intro T hT
        rw [Finset.mem_coe, mem_cutSubsets] at hT
        rw [Finset.mem_coe, Finset.mem_filter, hmemA]
        have hlt : ∀ z ∈ T, z < x := fun z hz => (hT.1 z hz).2.2
        have hsupT : T.sup id ≤ x := Finset.sup_le fun z hz => (hlt z hz).le
        have hg := gaps_insert (n := m) (x := x) (by omega) hlt
        have hv' : m - x = v := by omega
        rw [hv', hT.2, Multiset.cons_erase hvP] at hg
        refine ⟨⟨?_, hg⟩, ?_⟩
        · intro z hz
          rcases Finset.mem_insert.1 hz with rfl | hz
          · exact ⟨hxS, by omega, by omega⟩
          · exact ⟨(hT.1 z hz).1, (hT.1 z hz).2.1, by have := hlt z hz; omega⟩
        · rw [Finset.sup_insert]
          simp only [id]
          rw [max_eq_left hsupT]
          omega
      · intro T hT
        simp only [Finset.mem_coe, Finset.mem_filter] at hT
        have h1 := (hmemA T).1 hT.1
        have hne : T.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          rintro rfl
          simp at hT
          omega
        have hsup : T.sup id = x := by
          have := (h1.1 _ (sup_id_mem hne)).2.2
          omega
        exact Finset.insert_erase (hsup ▸ sup_id_mem hne)
      · intro T hT
        rw [Finset.mem_coe, mem_cutSubsets] at hT
        exact Finset.erase_insert (fun h => lt_irrefl _ (hT.1 _ h).2.2)
    · rw [if_neg hcond, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro T hT
      rw [Finset.mem_filter] at hT
      have h1 := (hmemA T).1 hT.1
      apply hcond
      by_cases hne : T.Nonempty
      · have hx := h1.1 _ (sup_id_mem hne)
        have := hT.2
        refine ⟨by omega, by omega, ?_⟩
        have : m - v = T.sup id := by omega
        rw [this]; exact hx.1
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        subst hne
        simp at hT
        exact absurd hT.2.symm hvm

/-! ### The state recurrence -/

section States

variable {s : ℕ}

/-- `s(a) = ∑ᵢ aᵢ tᵢ`, the weight of the state `a`. -/
def stateSum (t a : Fin s → ℕ) : ℕ := ∑ i, a i * t i

/-- The multiset of parts selected by the state `a`: `aᵢ` copies of `tᵢ`. -/
def stateParts (t a : Fin s → ℕ) : Multiset ℕ := ∑ i, a i • ({t i} : Multiset ℕ)

/-- The predecessor `a - eᵢ`. -/
def predState (a : Fin s → ℕ) (i : Fin s) : Fin s → ℕ := Function.update a i (a i - 1)

theorem sum_predState_lt (a : Fin s → ℕ) {i : Fin s} (h : 0 < a i) :
    ∑ j, predState a i j < ∑ j, a j := by
  have h1 := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
  have h2 : ∑ j, predState a i j = (a i - 1) + ∑ j ∈ Finset.univ.erase i, a j := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp [predState]
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp [predState, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  omega

/-- The recurrence `D` of `eq:subset-dp`, by well-founded recursion on `∑ aᵢ`:
`D(0) = 1` and, for `a ≠ 0`, `D(a) = η_b(a) ∑_{i : aᵢ > 0} D(a - eᵢ)` with `η_b(ν) = 1` and
`η_b(a) = b(s(a))` for `a ≠ ν`, where `b` is the indicator of the cut set `S`. -/
def dpCount (S : Finset ℕ) (t ν : Fin s → ℕ) (a : Fin s → ℕ) : ℕ :=
  if ∑ j, a j = 0 then 1 else
    (if a = ν then 1 else if stateSum t a ∈ S then 1 else 0) *
      ∑ i ∈ (Finset.univ.filter fun i => 0 < a i).attach,
        dpCount S t ν (predState a i.1)
termination_by ∑ j, a j
decreasing_by exact sum_predState_lt a (Finset.mem_filter.1 i.2).2

/-- `eq:subset-dp`, base case of the recurrence: `D(0) = 1`. -/
theorem dpCount_zero (S : Finset ℕ) (t ν : Fin s → ℕ) : dpCount S t ν 0 = 1 := by
  rw [dpCount]; simp

/-- `eq:subset-dp`, the recurrence: for `a ≠ 0`,
`D(a) = η_b(a) ∑_{i : aᵢ > 0} D(a - eᵢ)`. -/
theorem dpCount_of_ne_zero (S : Finset ℕ) (t ν a : Fin s → ℕ) (ha : a ≠ 0) :
    dpCount S t ν a = (if a = ν then 1 else if stateSum t a ∈ S then 1 else 0) *
      ∑ i ∈ Finset.univ.filter fun i => 0 < a i, dpCount S t ν (predState a i) := by
  have : ∑ j, a j ≠ 0 := by
    intro h
    exact ha (funext fun j => (Finset.sum_eq_zero_iff.1 h) j (Finset.mem_univ j))
  rw [dpCount, if_neg this, Finset.sum_attach (Finset.univ.filter fun i => 0 < a i)
    (fun i => dpCount S t ν (predState a i))]

theorem stateParts_pred_add (t a : Fin s → ℕ) {i : Fin s} (h : 0 < a i) :
    stateParts t (predState a i) + {t i} = stateParts t a := by
  unfold stateParts
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j => a j • ({t j} : Multiset ℕ)) (Finset.mem_univ i)]
  have h1 : ∑ j ∈ Finset.univ.erase i, predState a i j • ({t j} : Multiset ℕ) =
      ∑ j ∈ Finset.univ.erase i, a j • ({t j} : Multiset ℕ) :=
    Finset.sum_congr rfl fun j hj => by
      simp [predState, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h1]
  have h2 : predState a i i = a i - 1 := by simp [predState]
  rw [h2]
  obtain ⟨k, hk⟩ : ∃ k, a i = k + 1 := ⟨a i - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, succ_nsmul]
  abel

theorem stateSum_pred_add (t a : Fin s → ℕ) {i : Fin s} (h : 0 < a i) :
    stateSum t (predState a i) + t i = stateSum t a := by
  have := congrArg Multiset.sum (stateParts_pred_add t a h)
  have key : ∀ b : Fin s → ℕ, (stateParts t b).sum = stateSum t b := by
    intro b
    unfold stateParts stateSum
    rw [Multiset.sum_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Multiset.sum_nsmul]; simp
  rw [Multiset.sum_add, key, key] at this
  simpa using this

theorem mem_stateParts {t a : Fin s → ℕ} {v : ℕ} :
    v ∈ stateParts t a ↔ ∃ i, 0 < a i ∧ t i = v := by
  unfold stateParts
  rw [Multiset.mem_sum]
  constructor
  · rintro ⟨i, _, hi⟩
    rw [Multiset.mem_nsmul] at hi
    have h3 : v = t i := by simpa using hi.2
    exact ⟨i, Nat.pos_of_ne_zero hi.1, h3.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_univ _, (Multiset.mem_nsmul).2 ⟨by omega, by simp⟩⟩

theorem stateParts_eq_zero_iff {t a : Fin s → ℕ} : stateParts t a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext i
    by_contra hne
    have : t i ∈ stateParts t a := mem_stateParts.2 ⟨i, Nat.pos_of_ne_zero hne, rfl⟩
    rw [h] at this; simp at this
  · rintro rfl; simp [stateParts]

variable {S : Finset ℕ} {t ν : Fin s → ℕ}

/-- Core identity: for `0 ≠ a ≤ ν`, `D(a) = η_b(a) · cutCount S s(a) (parts a)`, for distinct
positive part values `t`. -/
theorem dpCount_eq (ht : Function.Injective t) (hpos : ∀ i, 0 < t i) :
    ∀ (N : ℕ) (a : Fin s → ℕ), ∑ j, a j = N → a ≠ 0 → a ≤ ν →
      dpCount S t ν a = (if a = ν then 1 else if stateSum t a ∈ S then 1 else 0) *
        cutCount S (stateSum t a) (stateParts t a) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a hN ha haν
  classical
  rw [dpCount_of_ne_zero S t ν a ha]
  congr 1
  have hex : ∃ i, 0 < a i := by
    by_contra h; push_neg at h
    exact ha (funext fun i => by have := h i; simp; omega)
  obtain ⟨i0, hi0⟩ := hex
  have hm : 0 < stateSum t a := by
    have := stateSum_pred_add t a hi0
    have := hpos i0; omega
  rw [cutCount_rec S hm]
  have himg : (stateParts t a).toFinset = (Finset.univ.filter fun i => 0 < a i).image t := by
    ext v
    simp only [Multiset.mem_toFinset, mem_stateParts, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [himg, Finset.sum_image (fun x _ y _ h => ht h)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : 0 < a i := (Finset.mem_filter.1 hi).2
  have hsum := stateSum_pred_add t a hi
  have hparts : (stateParts t a).erase (t i) = stateParts t (predState a i) := by
    rw [← stateParts_pred_add t a hi, add_comm, Multiset.singleton_add,
      Multiset.erase_cons_head]
  have hlt : ∑ j, predState a i j < N := hN ▸ sum_predState_lt a hi
  have hpa : predState a i ≤ a := fun j => by
    unfold predState
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  have hpν : predState a i ≠ ν := by
    intro h
    have h1 : predState a i i = ν i := by rw [h]
    have h2 : a i ≤ ν i := haν i
    simp only [predState, Function.update_self] at h1
    omega
  have hmv : stateSum t a - t i = stateSum t (predState a i) := by omega
  by_cases hpz : predState a i = 0
  · have hs0 : stateSum t (predState a i) = 0 := by rw [hpz]; simp [stateSum]
    have hv : t i = stateSum t a := by omega
    have hP : stateParts t a = {t i} := by
      rw [← stateParts_pred_add t a hi, hpz]; simp [stateParts]
    have hP' : stateParts t a = {stateSum t a} := hv ▸ hP
    rw [hpz, dpCount_zero, if_pos hv, if_pos hP']
  · have hspos : 0 < stateSum t (predState a i) := by
      obtain ⟨j, hj⟩ : ∃ j, predState a i j ≠ 0 := by
        by_contra h; push_neg at h; exact hpz (funext h)
      have := Finset.single_le_sum (f := fun j => predState a i j * t j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h3 : 0 < predState a i j * t j := Nat.mul_pos (Nat.pos_of_ne_zero hj) (hpos j)
      exact lt_of_lt_of_le h3 this
    have hvm : t i ≠ stateSum t a := by omega
    have hcond : (0 < t i ∧ t i < stateSum t a ∧ stateSum t (predState a i) ∈ S) ↔
        stateSum t (predState a i) ∈ S :=
      ⟨fun h => h.2.2, fun h => ⟨hpos i, by omega, h⟩⟩
    rw [ih _ hlt (predState a i) rfl hpz (hpa.trans haν), if_neg hpν, if_neg hvm, hmv, hparts]
    by_cases hS : stateSum t (predState a i) ∈ S
    · rw [if_pos hS, if_pos (hcond.2 hS), one_mul]
    · rw [if_neg hS, if_neg (fun h => hS (hcond.1 h)), zero_mul]

/-- `eq:subset-dp`: `m_β(λ) = D(ν)`, for a nonempty partition `λ` of `n` with distinct part
values `t` and multiplicities `ν` (`λ = ∑ νᵢ {tᵢ}`, `n = s(ν)`), and a cut set `S` of weight
`n`. -/
theorem subset_dp (ht : Function.Injective t) (hpos : ∀ i, 0 < t i) (hν : ν ≠ 0)
    (hS : IsCutSet (stateSum t ν) S) :
    mult (stateSum t ν) S (stateParts t ν) = dpCount S t ν ν := by
  rw [mult_eq_cutCount hS, dpCount_eq ht hpos _ ν rfl hν le_rfl, if_pos rfl, one_mul]

end States

/-- `eq:subset-dp` for an arbitrary partition: a multiset `lam` of positive parts with sum `n`
is `∑ νᵢ {tᵢ}` for its distinct values `t` (enumerated increasingly) and multiplicities
`νᵢ = count tᵢ lam`; then `m_β(λ) = D(ν)`. -/
theorem partition_subset_dp {n : ℕ} {S : Finset ℕ} (hS : IsCutSet n S) {lam : Multiset ℕ}
    (hpos : ∀ x ∈ lam, 0 < x) (hsum : lam.sum = n) (hne : lam ≠ 0) :
    ∃ (s : ℕ) (t ν : Fin s → ℕ), Function.Injective t ∧ (∀ i, 0 < t i) ∧ ν ≠ 0 ∧
      stateParts t ν = lam ∧ stateSum t ν = n ∧ (∀ i, ν i = lam.count (t i)) ∧
      mult n S lam = dpCount S t ν ν := by
  classical
  set s := lam.toFinset.card with hs
  let t : Fin s → ℕ := lam.toFinset.orderEmbOfFin rfl
  let ν : Fin s → ℕ := fun i => lam.count (t i)
  have ht : Function.Injective t := (lam.toFinset.orderEmbOfFin rfl).injective
  have htm : ∀ i, t i ∈ lam := fun i =>
    Multiset.mem_toFinset.1 (lam.toFinset.orderEmbOfFin_mem rfl i)
  have hparts : stateParts t ν = lam := by
    unfold stateParts
    have : ∑ i : Fin s, ν i • ({t i} : Multiset ℕ) = ∑ x ∈ lam.toFinset, lam.count x • {x} := by
      refine Finset.sum_nbij t (fun i _ => Multiset.mem_toFinset.2 (htm i))
        (fun x _ y _ h => ht h) (fun x hx => ?_) (fun i _ => rfl)
      have := Finset.range_orderEmbOfFin lam.toFinset rfl
      have hx' : x ∈ Set.range (lam.toFinset.orderEmbOfFin rfl) := by
        rw [this]; exact hx
      obtain ⟨i, hi⟩ := hx'
      exact ⟨i, Finset.mem_univ _, hi⟩
    rw [this, Multiset.toFinset_sum_count_nsmul_eq]
  have hsum' : stateSum t ν = n := by
    have key := congrArg Multiset.sum hparts
    have : (stateParts t ν).sum = stateSum t ν := by
      unfold stateParts stateSum
      rw [Multiset.sum_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Multiset.sum_nsmul]; simp
    rw [this, hsum] at key
    exact key
  have hν : ν ≠ 0 := by
    intro h
    have : stateParts t ν = 0 := by rw [h]; simp [stateParts]
    exact hne (hparts ▸ this)
  refine ⟨s, t, ν, ht, fun i => hpos _ (htm i), hν, hparts, hsum', fun i => rfl, ?_⟩
  have := subset_dp (S := S) ht (fun i => hpos _ (htm i)) hν (hsum' ▸ hS)
  rwa [hsum', hparts] at this

section Fuel

variable {s : ℕ}

/-- `dpCount` by structural recursion on a fuel, so that it evaluates by `decide`. -/
def dpFuel (S : Finset ℕ) (t ν : Fin s → ℕ) : ℕ → (Fin s → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, a =>
    if ∑ j, a j = 0 then 1 else
      (if a = ν then 1 else if stateSum t a ∈ S then 1 else 0) *
        ∑ i ∈ Finset.univ.filter fun i => 0 < a i, dpFuel S t ν k (predState a i)

theorem dpFuel_eq (S : Finset ℕ) (t ν : Fin s → ℕ) :
    ∀ (k : ℕ) (a : Fin s → ℕ), ∑ j, a j < k → dpFuel S t ν k a = dpCount S t ν a := by
  intro k
  induction k with
  | zero => intro a h; omega
  | succ k ih =>
    intro a h
    by_cases h0 : ∑ j, a j = 0
    · have : a = 0 := funext fun j => (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_univ j)
      subst this
      rw [dpCount_zero]; simp [dpFuel]
    · have ha : a ≠ 0 := fun h' => h0 (by rw [h']; simp)
      rw [dpCount_of_ne_zero S t ν a ha, dpFuel, if_neg h0]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      exact ih _ (by have := sum_predState_lt a (Finset.mem_filter.1 hi).2; omega)

/-- `eq:subset-dp`, evaluable form: `m_β(λ) = D(ν)` computed by `dpFuel`. -/
theorem subset_dp_fuel {t ν : Fin s → ℕ} {S : Finset ℕ} (ht : Function.Injective t)
    (hpos : ∀ i, 0 < t i) (hν : ν ≠ 0) (hS : IsCutSet (stateSum t ν) S) :
    mult (stateSum t ν) S (stateParts t ν) = dpFuel S t ν (∑ j, ν j + 1) ν := by
  rw [subset_dp ht hpos hν hS, dpFuel_eq S t ν _ ν (Nat.lt_succ_self _)]

end Fuel

end SkewRibbonCoarsenings
