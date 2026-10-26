/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonCoarseningPartitions

/-!
# Row partitions recovered from actual coarsening inventories

The maximal-length coarsening data underlying `lem:ribbon-endpoints`
and the ribbon classification in `shields-2026-skew-class-inflation.tex`.
The unique decision retaining every boundary is identified literally;
no distinct numerical part labels are assumed.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

/-- No selected boundary means that every actual seam decision is false. -/
theorem selectedSeams_eq_zero_iff {n : ℕ} (S : Fin n → Bool) :
    selectedSeams S = 0 ↔ S = fun _ => false := by
  constructor
  · intro he
    funext i
    have hle : (if S i then (1 : ℕ) else 0) ≤ selectedSeams S :=
      Finset.single_le_sum (f := fun j : Fin n => if S j then (1 : ℕ) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [he] at hle
    cases hi : S i with
    | false => rfl
    | true =>
      have hh : (1 : ℕ) ≤ 0 := by simpa only [hi, ite_true] using hle
      omega
  · intro he
    rw [he]
    simp [selectedSeams]

/-- Retaining all adjacent boundaries recovers the full literal ordered row word. -/
theorem coarsenRows_false {n : ℕ} (r : Fin (n + 1) → ℕ) :
    coarsenRows r (fun _ => false) = List.ofFn r := by
  induction n with
  | zero => simp [coarsenRows, List.ofFn_succ]
  | succ n ih =>
    change r 0 :: coarsenRows (fun i : Fin (n + 1) => r i.succ) (fun _ => false) = _
    rw [ih]
    exact (List.ofFn_succ (f := r)).symm

/-- The original unordered positive row partition, before any boundary is removed. -/
def rowPartition {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) : Multiset ℕ+ :=
  coarseningPartition r hr (fun _ => false)

/-- Its natural values are exactly the original full row word. -/
theorem rowPartition_values {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    (rowPartition r hr).map PNat.val = (List.ofFn r : Multiset ℕ) := by
  rw [rowPartition, coarseningPartition_values, coarsenRows_false]

/-- The original partition retains every row, including repeated equal values. -/
theorem rowPartition_card {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    (rowPartition r hr).card = n + 1 := by
  rw [rowPartition, coarseningPartition_card, coarsenRows_false, List.length_ofFn]

/-- The all-retained row partition is present as an actual coarsening. -/
theorem rowPartition_mem {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    rowPartition r hr ∈ coarseningPartitions r hr :=
  coarseningPartition_mem r hr (fun _ => false)

/-- A coarsening with the original row count has retained every boundary literally. -/
theorem maximal_coarseningPartition {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    (μ : Multiset ℕ+) (hμ : μ ∈ coarseningPartitions r hr) (hcard : μ.card = n + 1) :
    μ = rowPartition r hr := by
  obtain ⟨S, _, rfl⟩ := Multiset.mem_map.mp hμ
  rw [coarseningPartition_card] at hcard
  have hl := coarsenRows_length r S
  have hz : selectedSeams S = 0 := by omega
  have he := (selectedSeams_eq_zero_iff S).mp hz
  rw [he]
  rfl

/-- Equality of full coarsening inventories determines the original unordered rows. -/
theorem coarseningPartitions_rowPartition {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (he : coarseningPartitions r hr = coarseningPartitions s hs) :
    rowPartition r hr = rowPartition s hs := by
  have hp := congrArg partitionPolynomial he
  rw [← unsignedCoarsening_eq_partitionPolynomial r hr,
    ← unsignedCoarsening_eq_partitionPolynomial s hs] at hp
  have hn := unsignedCoarsening_eq_row_count r s hp
  subst m
  have hm := rowPartition_mem r hr
  rw [he] at hm
  exact maximal_coarseningPartition s hs _ hm (rowPartition_card r hr)

/-- The full coarsening inventory also determines the actual total weight. -/
theorem coarseningPartitions_row_sum {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (he : coarseningPartitions r hr = coarseningPartitions s hs) :
    (∑ i, r i) = ∑ i, s i := by
  have hh := congrArg (Multiset.map PNat.val) (coarseningPartitions_rowPartition r s hr hs he)
  rw [rowPartition_values, rowPartition_values] at hh
  have hw := congrArg Multiset.sum hh
  simpa only [Multiset.sum_coe, List.sum_ofFn] using hw

/-- Equal complete row words give the identical actual coarsening inventory across row counts. -/
theorem coarseningPartitions_eq_of_row_word_eq {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) (he : List.ofFn r = List.ofFn s) :
    coarseningPartitions r hr = coarseningPartitions s hs := by
  have hn := congrArg List.length he
  simp only [List.length_ofFn] at hn
  have hnm : n = m := by omega
  subst m
  have hrs : r = s := List.ofFn_injective he
  subst s
  rfl

end SkewClassInflation
