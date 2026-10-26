/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.FirstSplit
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.UnionInter

/-!
# Dominance of actual peel multisets

Formalizes "Majorization of the peel multisets, and its limits"
(`subsec:majorization`, `thm:first-split-majorization`, `prop:cap-fixed-comparability`).
Dominance is defined by decreasing sorted prefix sums and equal cardinality and
total sum.  Its selection characterization is proved, not assumed; it supplies
two-point dominance and preservation under adjoining common multisets.
Peel multisets retain index-zero entries.  Sorry-free.
-/

namespace SkewSchurReconstruction

/-- Sum of the `k` largest entries, retaining multiplicities. -/
def sortedPrefixSum (s : Multiset ℤ) (k : ℕ) : ℤ := (s.sort (· ≥ ·) |>.take k).sum

/-- Standard dominance with equal cardinality and total sum. -/
def Dominates (s t : Multiset ℤ) : Prop :=
  s.card = t.card ∧ s.sum = t.sum ∧ ∀ k, sortedPrefixSum t k ≤ sortedPrefixSum s k

/-- Strict dominance has at least one strictly larger sorted prefix. -/
def StrictlyDominates (s t : Multiset ℤ) : Prop :=
  Dominates s t ∧ ∃ k, sortedPrefixSum t k < sortedPrefixSum s k

private theorem selected_sum_le_sorted_take (L : List ℤ) (hL : L.Pairwise (· ≥ ·))
    (T : Multiset ℤ) (hT : T ≤ (L : Multiset ℤ)) (k : ℕ)
    (hc : T.card = k) (hk : k ≤ L.length) : T.sum ≤ (L.take k).sum := by
  classical
  induction L generalizing T k with
  | nil =>
    have hz : T = 0 := le_antisymm hT zero_le
    simp [hz]
  | cons a L ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hL
    cases k with
    | zero =>
      have hz := Multiset.card_eq_zero.mp hc
      simp [hz]
    | succ k =>
      have hex : ∃ b U, T = b ::ₘ U ∧ U ≤ (L : Multiset ℤ) ∧ b ≤ a := by
        by_cases ha : a ∈ T
        · refine ⟨a, T.erase a, (Multiset.cons_erase ha).symm, ?_, le_rfl⟩
          simpa using Multiset.erase_le_erase a hT
        · have hT' : T ≤ (L : Multiset ℤ) := (Multiset.le_cons_of_notMem ha).mp hT
          obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < T.card by omega)
          obtain ⟨U, hu⟩ := Multiset.exists_cons_of_mem hb
          refine ⟨b, U, hu, ?_, ?_⟩
          · exact (show U ≤ T by rw [hu]; exact Multiset.le_cons_self _ _).trans hT'
          · have hm := Multiset.mem_of_le hT' hb
            exact hhead b (by simpa using hm)
      obtain ⟨b, U, rfl, hU, hba⟩ := hex
      have hUc : U.card = k := by simpa using hc
      have hUk : k ≤ L.length := by simp only [List.length_cons] at hk; omega
      have hsum := ih htail U hU k hUc hUk
      simp only [Multiset.sum_cons, List.take_succ_cons, List.sum_cons]
      omega

/-- The sorted prefix is a genuine submultiset of the required cardinality. -/
def topSelection (s : Multiset ℤ) (k : ℕ) : Multiset ℤ :=
  (s.sort (· ≥ ·)).take k

theorem topSelection_le (s : Multiset ℤ) (k : ℕ) : topSelection s k ≤ s := by
  have h : ((s.sort (· ≥ ·)).take k : Multiset ℤ) ≤ (s.sort (· ≥ ·) : Multiset ℤ) :=
    (List.take_sublist k _).subperm
  simpa [topSelection] using h

theorem topSelection_card (s : Multiset ℤ) (k : ℕ) : (topSelection s k).card = min k s.card := by
  simp [topSelection]

theorem topSelection_sum (s : Multiset ℤ) (k : ℕ) :
    (topSelection s k).sum = sortedPrefixSum s k := rfl

theorem selection_sum_le_prefix (s T : Multiset ℤ) (hT : T ≤ s) (k : ℕ)
    (hc : T.card = k) (hk : k ≤ s.card) : T.sum ≤ sortedPrefixSum s k := by
  apply selected_sum_le_sorted_take (s.sort (· ≥ ·)) (Multiset.pairwise_sort _ _) T
  · simpa using hT
  · exact hc
  · simpa using hk

private theorem prefixSum_of_card_le (s : Multiset ℤ) (k : ℕ) (hk : s.card ≤ k) :
    sortedPrefixSum s k = s.sum := by
  unfold sortedPrefixSum
  rw [List.take_of_length_le (by simpa using hk)]
  change ((s.sort (· ≥ ·)) : Multiset ℤ).sum = s.sum
  rw [Multiset.sort_eq]

/-- Selection characterization, proved equivalent to the sorted-prefix definition. -/
theorem dominates_iff_selection (s t : Multiset ℤ) : Dominates s t ↔
    s.card = t.card ∧ s.sum = t.sum ∧
      ∀ T ≤ t, ∃ U ≤ s, U.card = T.card ∧ T.sum ≤ U.sum := by
  constructor
  · rintro ⟨hcard, hsum, hp⟩
    refine ⟨hcard, hsum, ?_⟩
    intro T hT
    have hc := Multiset.card_le_card hT
    refine ⟨topSelection s T.card, topSelection_le _ _, ?_, ?_⟩
    · rw [topSelection_card, hcard, min_eq_left hc]
    · exact (selection_sum_le_prefix t T hT T.card rfl hc).trans (hp T.card)
  · rintro ⟨hcard, hsum, hselect⟩
    refine ⟨hcard, hsum, ?_⟩
    intro k
    by_cases hk : k ≤ t.card
    · obtain ⟨U, hU, hc, hsu⟩ := hselect (topSelection t k) (topSelection_le _ _)
      rw [topSelection_card, min_eq_left hk] at hc
      exact hsu.trans (selection_sum_le_prefix s U hU k hc (by omega))
    · rw [prefixSum_of_card_le t k (by omega), prefixSum_of_card_le s k (by omega), hsum]

/-- Dominance is preserved by adjoining an arbitrary common multiset. -/
theorem Dominates.add_common {s t : Multiset ℤ} (h : Dominates s t) (W : Multiset ℤ) :
    Dominates (s + W) (t + W) := by
  classical
  obtain ⟨hc, hs, hsel⟩ := (dominates_iff_selection s t).mp h
  apply (dominates_iff_selection _ _).mpr
  refine ⟨by simp [hc], by simp [hs], ?_⟩
  intro T hT
  let A := T ∩ t
  let B := T - t
  have hA : A ≤ t := Multiset.inter_le_right
  have hB : B ≤ W := Multiset.sub_le_iff_le_add.mpr (by simpa [add_comm] using hT)
  have hdec : T = A + B := by
    dsimp [A, B]
    rw [add_comm, Multiset.sub_add_inter]
  obtain ⟨U, hU, hcard, hsum⟩ := hsel A hA
  refine ⟨U + B, add_le_add hU hB, ?_, ?_⟩
  · rw [hdec]
    simp [hcard]
  · rw [hdec]
    simp only [Multiset.sum_add]
    omega

/-- Equality of every sorted prefix recovers the multiset exactly. -/
theorem multiset_eq_of_prefix_eq {s t : Multiset ℤ} (hc : s.card = t.card)
    (h : ∀ k, sortedPrefixSum s k = sortedPrefixSum t k) : s = t := by
  have hl : s.sort (· ≥ ·) = t.sort (· ≥ ·) :=
    List.eq_of_sum_take_eq (by simpa using hc) (fun k _ => h k)
  have hm := congrArg (fun L : List ℤ => (L : Multiset ℤ)) hl
  simpa using hm

theorem strictlyDominates_of_ne {s t : Multiset ℤ} (h : Dominates s t) (hne : s ≠ t) :
    StrictlyDominates s t := by
  refine ⟨h, ?_⟩
  by_contra hstrict
  push Not at hstrict
  apply hne
  apply multiset_eq_of_prefix_eq h.1
  intro k
  exact le_antisymm (hstrict k) (h.2.2 k)

/-- Two equal-sum pairs are ordered by their largest entry. -/
theorem pair_dominates_of_max_le (a b c d : ℤ) (hs : a + b = c + d)
    (hm : max c d ≤ max a b) : Dominates (a ::ₘ b ::ₘ 0) (c ::ₘ d ::ₘ 0) := by
  classical
  apply (dominates_iff_selection _ _).mpr
  refine ⟨by simp, by simpa using hs, ?_⟩
  intro T hT
  have hc : T.card ≤ 2 := by simpa using Multiset.card_le_card hT
  by_cases h0 : T.card = 0
  · have hz := Multiset.card_eq_zero.mp h0
    subst T
    exact ⟨0, zero_le, rfl, le_rfl⟩
  · by_cases h1 : T.card = 1
    · obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp h1
      have hx : x = c ∨ x = d := by
        have hmem := Multiset.mem_of_le hT (show x ∈ ({x} : Multiset ℤ) by simp)
        simpa using hmem
      have hmax : max a b ∈ (a ::ₘ b ::ₘ (0 : Multiset ℤ)) := by
        by_cases hab : a ≤ b
        · simp [max_eq_right hab]
        · simp [max_eq_left (le_of_not_ge hab)]
      refine ⟨{max a b}, Multiset.singleton_le.mpr hmax, by simp, ?_⟩
      simp only [Multiset.sum_singleton]
      rcases hx with rfl | rfl
      · exact (le_max_left _ _).trans hm
      · exact (le_max_right _ _).trans hm
    · have hcard : T.card = 2 := by omega
      have he := Multiset.eq_of_le_of_card_le hT (by simpa using hcard.ge)
      subst T
      refine ⟨a ::ₘ b ::ₘ 0, le_rfl, by simp, ?_⟩
      simpa using hs.ge

theorem pair_comparable (a b c d : ℤ) (hs : a + b = c + d) :
    Dominates (a ::ₘ b ::ₘ 0) (c ::ₘ d ::ₘ 0) ∨
      Dominates (c ::ₘ d ::ₘ 0) (a ::ₘ b ::ₘ 0) := by
  rcases le_total (max c d) (max a b) with h | h
  · exact Or.inl (pair_dominates_of_max_le _ _ _ _ hs h)
  · exact Or.inr (pair_dominates_of_max_le _ _ _ _ hs.symm h)

/-- The first-split two-point exchange is strictly ordered in standard dominance. -/
theorem first_split_pair_dominates (x y Delta : ℤ) (hxy : x < y) (hD : 0 < Delta)
    (W : Multiset ℤ) : StrictlyDominates
    (W + (y ::ₘ (x - Delta) ::ₘ 0)) (W + (x ::ₘ (y - Delta) ::ₘ 0)) := by
  have hm : max x (y - Delta) ≤ max y (x - Delta) := by
    rw [show max y (x - Delta) = y from max_eq_left (by omega)]
    exact max_le (by omega) (by omega)
  have hd := pair_dominates_of_max_le y (x - Delta) x (y - Delta) (by omega) hm
  have hadd : Dominates (W + (y ::ₘ (x - Delta) ::ₘ 0))
      (W + (x ::ₘ (y - Delta) ::ₘ 0)) := by simpa [add_comm] using hd.add_common W
  apply strictlyDominates_of_ne hadd
  intro he
  have hp := add_left_cancel he
  have hy : y ∈ (y ::ₘ (x - Delta) ::ₘ (0 : Multiset ℤ)) := by simp
  rw [hp] at hy
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hy
  rcases hy with hy | hy <;> omega

namespace Diagram

variable {n : ℕ}

/-- Actual increasing-matching subscripts, retaining zeros and all multiplicities. -/
def peelMultiset (X : Diagram n) (j : Fin (n + 1)) : Multiset ℤ :=
  Finset.univ.val.map (X.peelIndex j)

theorem peelMultiset_card (X : Diagram n) (j : Fin (n + 1)) :
    (X.peelMultiset j).card = n := by simp [peelMultiset]

theorem peelMultiset_sum (X : Diagram n) (j : Fin (n + 1)) :
    (X.peelMultiset j).sum = X.peelDegree j := rfl

theorem peelIndex_mem_peelMultiset (X : Diagram n) (j : Fin (n + 1)) (i : Fin n) :
    X.peelIndex j i ∈ X.peelMultiset j :=
  Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

theorem peelMultiset_nonneg (X : Diagram n) (hX : X.Connected) (j : Fin (n + 1)) :
    ∀ a ∈ X.peelMultiset j, 0 ≤ a := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ha
  exact X.peelIndex_nonneg hX j i

theorem peelMultiset_zero (X : Diagram n) :
    X.peelMultiset 0 = X.rowLengthMultiset.map (fun k : ℕ => (k : ℤ)) := by
  unfold peelMultiset rowLengthMultiset
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  simpa [peelIndex] using (X.rowLength_eq_coordinates i).symm

/-- One adjacent omission exchanges exactly the row length for the shifted overlap index. -/
theorem peelMultiset_exchange (X : Diagram n) (j : Fin n) :
    X.peelMultiset j.succ =
      X.exchangeZero j ::ₘ (X.peelMultiset j.castSucc).erase (X.exchangeRow j) := by
  classical
  let U : Multiset (Fin n) := Finset.univ.val
  have hj : j ∈ U := by simp [U]
  have hu : U = j ::ₘ U.erase j := (Multiset.cons_erase hj).symm
  have hold : X.peelMultiset j.castSucc =
      X.exchangeRow j ::ₘ (U.erase j).map (X.peelIndex j.castSucc) := by
    have h := congrArg (Multiset.map (X.peelIndex j.castSucc)) hu
    simpa only [peelMultiset, U, Multiset.map_cons, peelIndex_castSucc_self] using h
  have hnew : X.peelMultiset j.succ =
      X.exchangeZero j ::ₘ (U.erase j).map (X.peelIndex j.succ) := by
    have h := congrArg (Multiset.map (X.peelIndex j.succ)) hu
    simpa only [peelMultiset, U, Multiset.map_cons, peelIndex_succ_self] using h
  have hrest : (U.erase j).map (X.peelIndex j.succ) =
      (U.erase j).map (X.peelIndex j.castSucc) := by
    apply Multiset.map_congr rfl
    intro i hi
    have hij : i ≠ j := by
      intro he
      subst i
      have hn : U.Nodup := (Finset.univ : Finset (Fin n)).nodup
      exact (hn.notMem_erase hi)
    exact (X.peelIndex_adjacent_eq j i hij).symm
  rw [hold, hnew, Multiset.erase_cons_head, hrest]

/-- Shared prefix exchanges propagate the initial row-length multiset equality. -/
theorem peelMultiset_eq_at_first_split (X Y : Diagram n)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i) :
    X.peelMultiset v.castSucc = Y.peelMultiset v.castSucc := by
  have hstep : ∀ t (ht : t < n + 1), t ≤ v.val →
      X.peelMultiset ⟨t, ht⟩ = Y.peelMultiset ⟨t, ht⟩ := by
    intro t
    induction t with
    | zero =>
      intro ht _
      have he : (⟨0, ht⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
      rw [he, peelMultiset_zero, peelMultiset_zero, hrows]
    | succ t ih =>
      intro ht hv
      have htb : t < n + 1 := by omega
      let i : Fin n := ⟨t, by have hb := v.isLt; omega⟩
      have hp := hprefix i (by dsimp [i]; omega)
      have hr : X.exchangeRow i = Y.exchangeRow i := by
        unfold exchangeRow
        rw [hgrid, hp]
      have hz : X.exchangeZero i = Y.exchangeZero i := by
        unfold exchangeZero
        rw [hgrid, hp]
      have he : (⟨t + 1, ht⟩ : Fin (n + 1)) = i.succ := by
        apply Fin.ext
        rfl
      rw [he, peelMultiset_exchange, peelMultiset_exchange, hz, hr]
      have hi := ih htb (by omega)
      change X.peelMultiset i.castSucc = Y.peelMultiset i.castSucc at hi
      rw [hi]
  exact hstep v.val (by have h := v.isLt; omega) le_rfl

theorem first_split_peel_pairs (X Y : Diagram n)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : Y.rowParam v < X.rowParam v) :
    let x := X.capShift v.succ - X.rowParam v
    let y := X.capShift v.succ - Y.rowParam v
    let Delta := X.capShift v.succ - X.capShift v.castSucc
    ∃ W : Multiset ℤ,
      X.peelMultiset v.succ = W + (y ::ₘ (x - Delta) ::ₘ 0) ∧
      Y.peelMultiset v.succ = W + (x ::ₘ (y - Delta) ::ₘ 0) := by
  classical
  let x := X.exchangeRow v
  let y := Y.exchangeRow v
  let C := X.peelMultiset v.castSucc
  have hCeq := peelMultiset_eq_at_first_split X Y hgrid hrows v hprefix
  have hxy : x < y := by
    dsimp [x, y, exchangeRow]
    rw [← hgrid v.succ]
    omega
  have hx : x ∈ C := by
    have h := X.peelIndex_mem_peelMultiset v.castSucc v
    simpa only [peelIndex_castSucc_self] using h
  have hy : y ∈ C := by
    have h := Y.peelIndex_mem_peelMultiset v.castSucc v
    rw [← hCeq] at h
    simpa only [peelIndex_castSucc_self] using h
  have hyrest : y ∈ C.erase x := (Multiset.mem_erase_of_ne hxy.ne').mpr hy
  let W := (C.erase x).erase y
  have hC : C = x ::ₘ y ::ₘ W := by
    calc
      C = x ::ₘ C.erase x := (Multiset.cons_erase hx).symm
      _ = x ::ₘ y ::ₘ W := congrArg (Multiset.cons x) (Multiset.cons_erase hyrest).symm
  have hzX : X.exchangeZero v = x - (X.capShift v.succ - X.capShift v.castSucc) := by
    dsimp [x, exchangeRow, exchangeZero]
    ring
  have hzY : Y.exchangeZero v = y - (X.capShift v.succ - X.capShift v.castSucc) := by
    dsimp [y, exchangeRow, exchangeZero]
    rw [← hgrid v.succ, ← hgrid v.castSucc]
    ring
  have hycoord : X.capShift v.succ - Y.rowParam v = y := by
    dsimp [y, exchangeRow]
    rw [hgrid]
  dsimp only
  rw [hycoord]
  change ∃ W, X.peelMultiset v.succ = W + (y ::ₘ (x - _) ::ₘ 0) ∧
    Y.peelMultiset v.succ = W + (x ::ₘ (y - _) ::ₘ 0)
  refine ⟨W, ?_, ?_⟩
  · rw [peelMultiset_exchange, hzX]
    change (x - _) ::ₘ C.erase x = _
    rw [hC, Multiset.erase_cons_head]
    simpa only [Multiset.add_cons, add_zero] using Multiset.cons_swap _ _ W
  · rw [peelMultiset_exchange, hzY, ← hCeq]
    change (y - _) ::ₘ C.erase y = _
    rw [hC, Multiset.erase_cons_tail _ hxy.ne, Multiset.erase_cons_head]
    simpa only [Multiset.add_cons, add_zero] using Multiset.cons_swap _ _ W

/-- `thm:first-split-majorization`, with standard sorted-prefix dominance and zeros retained. -/
theorem first_split_majorization (X Y : Diagram n)
    (hX : X.Connected) (_hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : Y.rowParam v < X.rowParam v) :
    StrictlyDominates (X.peelMultiset v.succ) (Y.peelMultiset v.succ) := by
  obtain ⟨W, hx, hy⟩ := first_split_peel_pairs X Y hgrid hrows v hprefix hchanged
  have hd := X.capShift_strictMono (show v.castSucc < v.succ by
    change v.val < v.val + 1
    omega)
  have hnonneg := X.diagonal_feasible hX v
  have hxD : X.capShift v.succ - X.capShift v.castSucc ≤
      X.capShift v.succ - X.rowParam v := by omega
  rw [hx, hy]
  exact first_split_pair_dominates _ _ _ (by omega) (by omega) W

theorem first_split_majorization_reverse (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v < Y.rowParam v) :
    StrictlyDominates (Y.peelMultiset v.succ) (X.peelMultiset v.succ) := by
  exact first_split_majorization Y X hY hX (fun j => (hgrid j).symm) hrows.symm v
    (fun i hi => (hprefix i hi).symm) hchanged

/-- A positive transfer between two distinct non-top outer rows; all other rows stay fixed. -/
def SingleNonTopTransfer (X Y : Diagram n) : Prop :=
  ∃ (r s : Fin n) (theta : ℕ),
    r ≠ s ∧ 0 < r.val ∧ 0 < s.val ∧ 0 < theta ∧
      Y.outer r = X.outer r + theta ∧ Y.outer s + theta = X.outer s ∧
      ∀ i, i ≠ r → i ≠ s → X.outer i = Y.outer i

/-- The transfer's cap alignment is produced from the unchanged top and common inner boundary. -/
theorem singleNonTopTransfer_cap_grid (X Y : Diagram n) (hinner : X.inner = Y.inner)
    (htrans : X.SingleNonTopTransfer Y) : X.top = Y.top ∧ ∀ j, X.capShift j = Y.capShift j := by
  obtain ⟨r, s, theta, hrs, hr0, hs0, htheta, hplus, hminus, hother⟩ := htrans
  have hrb := r.isLt
  have hn : 0 < n := by omega
  have h0r : (⟨0, hn⟩ : Fin n) ≠ r := by
    intro he
    have hval := congrArg Fin.val he
    change 0 = r.val at hval
    omega
  have h0s : (⟨0, hn⟩ : Fin n) ≠ s := by
    intro he
    have hval := congrArg Fin.val he
    change 0 = s.val at hval
    omega
  have ht : X.top = Y.top := by
    rw [top_of_pos X hn, top_of_pos Y hn]
    exact hother _ h0r h0s
  refine ⟨ht, ?_⟩
  intro j
  unfold capShift
  split_ifs <;> simp [ht, hinner]

/-- `prop:cap-fixed-comparability` for every actual increasing-matching peel. -/
theorem cap_fixed_comparability (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hinner : X.inner = Y.inner)
    (htrans : X.SingleNonTopTransfer Y) (j : Fin (n + 1)) :
    Dominates (X.peelMultiset j) (Y.peelMultiset j) ∨
      Dominates (Y.peelMultiset j) (X.peelMultiset j) := by
  classical
  obtain ⟨r, s, theta, hrs, hr0, hs0, htheta, hplus, hminus, hother⟩ := htrans
  have h0r : (⟨0, hX.1⟩ : Fin n) ≠ r := by
    intro he
    have hval := congrArg Fin.val he
    change 0 = r.val at hval
    omega
  have h0s : (⟨0, hX.1⟩ : Fin n) ≠ s := by
    intro he
    have hval := congrArg Fin.val he
    change 0 = s.val at hval
    omega
  have htop : X.top = Y.top := by
    rw [top_of_pos X hX.1, top_of_pos Y hY.1]
    exact hother _ h0r h0s
  have hgrid : ∀ k, X.capShift k = Y.capShift k := by
    intro k
    unfold capShift
    split_ifs <;> simp [htop, hinner]
  have hrowother : ∀ i, i ≠ r → i ≠ s → X.rowParam i = Y.rowParam i := by
    intro i hir his
    unfold rowParam
    rw [htop, hother i hir his]
  have hentryother : ∀ i, i ≠ r → i ≠ s → X.peelIndex j i = Y.peelIndex j i := by
    intro i hir his
    unfold peelIndex
    rw [hgrid, hrowother i hir his]
  have hrentry : Y.peelIndex j r = X.peelIndex j r + theta := by
    unfold peelIndex rowParam
    rw [hgrid, htop]
    omega
  have hsentry : Y.peelIndex j s = X.peelIndex j s - theta := by
    unfold peelIndex rowParam
    rw [hgrid, htop]
    omega
  let U : Multiset (Fin n) := Finset.univ.val
  have hU : U.Nodup := (Finset.univ : Finset (Fin n)).nodup
  have hr : r ∈ U := by simp [U]
  have hs : s ∈ U := by simp [U]
  have hsr : s ∈ U.erase r := (Multiset.mem_erase_of_ne hrs.symm).mpr hs
  let V := (U.erase r).erase s
  have hu : U = r ::ₘ s ::ₘ V := by
    calc
      U = r ::ₘ U.erase r := (Multiset.cons_erase hr).symm
      _ = r ::ₘ s ::ₘ V := congrArg (Multiset.cons r) (Multiset.cons_erase hsr).symm
  let W := V.map (X.peelIndex j)
  let x := X.peelIndex j r
  let y := X.peelIndex j s
  have hrest : V.map (Y.peelIndex j) = W := by
    apply Multiset.map_congr rfl
    intro i hi
    have hir : i ≠ r := by
      intro he
      subst i
      exact hU.notMem_erase (Multiset.mem_of_mem_erase hi)
    have his : i ≠ s := by
      intro he
      subst i
      exact (hU.erase r).notMem_erase hi
    exact (hentryother i hir his).symm
  have hx : X.peelMultiset j = W + (x ::ₘ y ::ₘ 0) := by
    have h := congrArg (Multiset.map (X.peelIndex j)) hu
    simpa only [peelMultiset, U, Multiset.map_cons, W, x, y,
      Multiset.add_cons, add_zero] using h
  have hy : Y.peelMultiset j = W + ((x + (theta : ℤ)) ::ₘ (y - (theta : ℤ)) ::ₘ 0) := by
    have h := congrArg (Multiset.map (Y.peelIndex j)) hu
    rw [Multiset.map_cons, Multiset.map_cons, hrentry, hsentry, hrest] at h
    simpa only [peelMultiset, U, x, y, Multiset.add_cons, add_zero] using h
  rw [hx, hy]
  rcases pair_comparable x y (x + theta) (y - theta) (by ring) with h | h
  · exact Or.inl (by simpa [add_comm] using h.add_common W)
  · exact Or.inr (by simpa [add_comm] using h.add_common W)

end Diagram

end SkewSchurReconstruction
