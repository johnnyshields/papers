/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonCoarseningRows
import Mathlib.Data.Multiset.Bind

/-!
# Exact first-boundary recursion of coarsening partition data

The actual partition enumeration underlying `lem:ribbon-endpoints` and
the ribbon classification in `shields-2026-skew-class-inflation.tex`.
The first boundary is either retained or merged; maximal-length extraction
retains exactly the original unordered row partition.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

private theorem enum_multiset_sum {I α : Type*} [Fintype I] (f : I → α) :
    Finset.univ.val.map f = ∑ i : I, ({f i} : Multiset α) := by
  exact (Multiset.bind_singleton (s := Finset.univ.val) f).symm

/-- The row partition of positive-index rows is their literal unordered finite row word. -/
theorem rowPartition_positive {n : ℕ} (r : Fin (n + 1) → ℕ+) :
    rowPartition (PNat.val ∘ r) (fun i => (r i).pos) = (List.ofFn r : Multiset ℕ+) := by
  apply Multiset.map_injective PNat.coe_injective
  rw [rowPartition_values, Multiset.map_coe, List.map_ofFn]

/-- Retaining the first boundary prepends the first literal positive row to each coarsening. -/
theorem coarseningPartition_cons_false {n : ℕ} (r : Fin (n + 2) → ℕ+) (S : Fin n → Bool) :
    coarseningPartition (PNat.val ∘ r) (fun i => (r i).pos) (Fin.cons false S) =
      r 0 ::ₘ coarseningPartition (fun i : Fin (n + 1) => (r i.succ).val)
        (fun i => (r i.succ).pos) S := by
  apply Multiset.map_injective PNat.coe_injective
  rw [coarseningPartition_values, Multiset.map_cons, coarseningPartition_values]
  simp only [coarsenRows, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ite_false]
  rfl

/-- Merging the first boundary replaces its two positive rows by their actual sum. -/
theorem coarseningPartition_cons_true {n : ℕ} (r : Fin (n + 2) → ℕ+) (S : Fin n → Bool) :
    let merged : Fin (n + 1) → ℕ+ :=
      Fin.cons (r 0 + r (0 : Fin (n + 1)).succ) (fun i : Fin n => r i.succ.succ)
    coarseningPartition (PNat.val ∘ r) (fun i => (r i).pos) (Fin.cons true S) =
      coarseningPartition (PNat.val ∘ merged) (fun i => (merged i).pos) S := by
  intro merged
  apply Multiset.map_injective PNat.coe_injective
  rw [coarseningPartition_values, coarseningPartition_values]
  have he : (PNat.val ∘ merged) =
      Fin.cons ((r 0).val + (r (0 : Fin (n + 1)).succ).val)
        (fun i : Fin n => (r i.succ.succ).val) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [he]
  simp only [coarsenRows, Fin.cons_zero, Fin.cons_succ, ite_true]
  rfl

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/GeneralHessenberg.lean,
-- seam-mask sum reindexing, instantiated in the additive monoid of partition inventories.
/-- All actual coarsenings split into the merged-first and retained-first decisions. -/
theorem coarseningPartitions_positive_split {n : ℕ} (r : Fin (n + 2) → ℕ+) :
    let merged : Fin (n + 1) → ℕ+ :=
      Fin.cons (r 0 + r (0 : Fin (n + 1)).succ) (fun i : Fin n => r i.succ.succ)
    coarseningPartitions (PNat.val ∘ r) (fun i => (r i).pos) =
      coarseningPartitions (PNat.val ∘ merged) (fun i => (merged i).pos) +
        (coarseningPartitions (fun i : Fin (n + 1) => (r i.succ).val)
          (fun i => (r i.succ).pos)).map (fun μ => r 0 ::ₘ μ) := by
  intro merged
  have horig : coarseningPartitions (PNat.val ∘ r) (fun i => (r i).pos) =
      ∑ S : Fin (n + 1) → Bool,
        ({coarseningPartition (PNat.val ∘ r) (fun i => (r i).pos) S} : Multiset _) :=
    enum_multiset_sum _
  have hmerged : coarseningPartitions (PNat.val ∘ merged) (fun i => (merged i).pos) =
      ∑ S : Fin n → Bool,
        ({coarseningPartition (PNat.val ∘ merged) (fun i => (merged i).pos) S} : Multiset _) :=
    enum_multiset_sum _
  have htail : (coarseningPartitions (fun i : Fin (n + 1) => (r i.succ).val)
      (fun i => (r i.succ).pos)).map (fun μ => r 0 ::ₘ μ) =
      ∑ S : Fin n → Bool,
        ({r 0 ::ₘ coarseningPartition (fun i : Fin (n + 1) => (r i.succ).val)
          (fun i => (r i.succ).pos) S} : Multiset _) := by
    rw [coarseningPartitions, Multiset.map_map]
    exact enum_multiset_sum _
  rw [horig, hmerged, htail]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp
    (fun S : Fin (n + 1) → Bool =>
      ({coarseningPartition (PNat.val ∘ r) (fun i => (r i).pos) S} : Multiset _))]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  congr 1
  · apply Finset.sum_congr rfl
    intro S _
    exact congrArg (fun μ : Multiset ℕ+ => ({μ} : Multiset (Multiset ℕ+)))
      (coarseningPartition_cons_true r S)
  · apply Finset.sum_congr rfl
    intro S _
    exact congrArg (fun μ : Multiset ℕ+ => ({μ} : Multiset (Multiset ℕ+)))
      (coarseningPartition_cons_false r S)

/-- A one-row positive word has exactly its one actual singleton coarsening. -/
theorem coarseningPartitions_positive_one (r : Fin 1 → ℕ+) :
    coarseningPartitions (PNat.val ∘ r) (fun i => (r i).pos) =
      {({r 0} : Multiset ℕ+)} := by
  have he : coarseningPartitions (PNat.val ∘ r) (fun i => (r i).pos) =
      ∑ S : Fin 0 → Bool,
        ({coarseningPartition (PNat.val ∘ r) (fun i => (r i).pos) S} : Multiset _) :=
    enum_multiset_sum _
  rw [he]
  have hpart : ∀ S : Fin 0 → Bool,
      coarseningPartition (PNat.val ∘ r) (fun i => (r i).pos) S = {r 0} := by
    intro S
    have hs : S = fun _ => false := by funext i; exact Fin.elim0 i
    rw [hs]
    change rowPartition (PNat.val ∘ r) (fun i => (r i).pos) = _
    rw [rowPartition_positive]
    simp only [List.ofFn_succ, List.ofFn_zero]
    rfl
  simp only [hpart, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, pow_zero, one_nsmul]

/-- The maximal-cardinality layer consists of the one actual all-retained decision. -/
theorem sum_coarsening_top {A : Type*} [AddCommMonoid A] {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) (F : Multiset ℕ+ → A) :
    (∑ S : Fin n → Bool,
      if (coarseningPartition r hr S).card = n + 1 then F (coarseningPartition r hr S) else 0) =
        F (rowPartition r hr) := by
  classical
  calc
    _ = if (coarseningPartition r hr (fun _ => false)).card = n + 1 then
        F (coarseningPartition r hr (fun _ => false)) else 0 := by
      apply Finset.sum_eq_single (fun _ => false)
      · intro S _ hS
        have hcard : (coarseningPartition r hr S).card ≠ n + 1 := by
          intro he
          rw [coarseningPartition_card] at he
          have hl := coarsenRows_length r S
          have hz : selectedSeams S = 0 := by omega
          exact hS ((selectedSeams_eq_zero_iff S).mp hz)
        rw [ite_eq_right hcard]
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    _ = F (rowPartition r hr) := by
      change (if (rowPartition r hr).card = n + 1 then F (rowPartition r hr) else 0) = _
      rw [rowPartition_card, ite_eq_left rfl]

end SkewClassInflation
