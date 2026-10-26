/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.PartitionOrderCounts
import SkewClassInflation.ReflectedCutTypes

/-!
# Three-part coefficients determine single-cut agreement

The three-part coarsening relations used by the nonsymmetric ribbon
factorization input to `lem:overlap-power-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Every coefficient counts
actual distinct orders retaining the source cuts.  Repeated partition
parts are not replaced by six distinct orders.  Sorry-free.
-/

namespace SkewClassInflation

/-- A literal three-part word has exactly its two actual prefix cuts. -/
theorem wordProperCuts_three (a b c : ℕ) : wordProperCuts [a, b, c] = {a, a + b} := by
  change wordProperCuts ([a, b] ++ [c]) = _
  rw [wordProperCuts_append_single]
  simp [prefixEnds]

/-- The six possible orders form a finite set, so equal words remain deduplicated. -/
theorem partitionOrders_three (a b c : ℕ+) :
    partitionOrders [a, b, c] =
      {[a.val, b.val, c.val], [b.val, a.val, c.val], [b.val, c.val, a.val],
        [a.val, c.val, b.val], [c.val, a.val, b.val], [c.val, b.val, a.val]} := by
  change ([a.val, b.val, c.val] : List ℕ).permutations.toFinset = _
  rw [List.toFinset_eq_of_perm _ _ (List.permutations_perm_permutations' _)]
  simp only [List.permutations', List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.toFinset_cons,
    List.toFinset_nil, Finset.insert_empty]

/-- Retaining a three-part order reads its first cut and the reflection of its last part. -/
theorem threePart_retained_iff {N : ℕ} (α : Composition N) (a b c : ℕ+)
    (hsum : a.val + b.val + c.val = N) :
    wordProperCuts [a.val, b.val, c.val] ⊆ properCuts α ↔
      a.val ∈ properCuts α ∧ N - c.val ∈ properCuts α := by
  have he : a.val + b.val = N - c.val := by omega
  rw [wordProperCuts_three, he]
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-- Presence of a three-part partition is exactly one of its actual retained endpoint orders. -/
theorem threePart_partition_present {N : ℕ} (α : Composition N) (a b c : ℕ+)
    (hsum : a.val + b.val + c.val = N) :
    (a ::ₘ b ::ₘ c ::ₘ 0 : Multiset ℕ+) ∈ coarseningInventory α ↔
      (a.val ∈ properCuts α ∧ N - c.val ∈ properCuts α) ∨
      (b.val ∈ properCuts α ∧ N - c.val ∈ properCuts α) ∨
      (b.val ∈ properCuts α ∧ N - a.val ∈ properCuts α) ∨
      (a.val ∈ properCuts α ∧ N - b.val ∈ properCuts α) ∨
      (c.val ∈ properCuts α ∧ N - b.val ∈ properCuts α) ∨
      (c.val ∈ properCuts α ∧ N - a.val ∈ properCuts α) := by
  classical
  change (([a, b, c] : List ℕ+) : Multiset ℕ+) ∈ coarseningInventory α ↔ _
  rw [← Multiset.count_pos, coarseningInventory_count_orders α [a, b, c]
    (by simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, Nat.add_assoc] using hsum),
    Finset.card_pos, partitionOrders_three, Finset.filter_nonempty_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton, or_and_right, exists_or, exists_eq_left]
  rw [threePart_retained_iff α a b c hsum,
    threePart_retained_iff α b a c (by omega),
    threePart_retained_iff α b c a (by omega),
    threePart_retained_iff α a c b (by omega),
    threePart_retained_iff α c a b (by omega),
    threePart_retained_iff α c b a (by omega)]

/-- A type-one reflected cut is present precisely when its partner is absent. -/
theorem single_cut_reflect_iff_not {N : ℕ} (α : Composition N) (x : ℕ)
    (hx : compositionCutType α x = 1) : N - x ∈ properCuts α ↔ x ∉ properCuts α := by
  rcases (compositionCutType_one_iff α x).mp hx with ⟨h, hr⟩ | ⟨h, hr⟩ <;> simp [h, hr]

/-- Three single-type points agree exactly when their actual three-part partition is absent. -/
theorem three_single_agree_iff_absent {N : ℕ} (α : Composition N) (a b c : ℕ+)
    (hsum : a.val + b.val + c.val = N)
    (ha : compositionCutType α a.val = 1) (hb : compositionCutType α b.val = 1)
    (hc : compositionCutType α c.val = 1) :
    ((a.val ∈ properCuts α ↔ b.val ∈ properCuts α) ∧
      (b.val ∈ properCuts α ↔ c.val ∈ properCuts α)) ↔
      (a ::ₘ b ::ₘ c ::ₘ 0 : Multiset ℕ+) ∉ coarseningInventory α := by
  rw [threePart_partition_present α a b c hsum,
    single_cut_reflect_iff_not α a.val ha, single_cut_reflect_iff_not α b.val hb,
    single_cut_reflect_iff_not α c.val hc]
  have hlogic (P Q R : Prop) :
      ((P ↔ Q) ∧ (Q ↔ R)) ↔
        ¬((P ∧ ¬R) ∨ (Q ∧ ¬R) ∨ (Q ∧ ¬P) ∨
          (P ∧ ¬Q) ∨ (R ∧ ¬Q) ∨ (R ∧ ¬P)) := by
    tauto
  exact hlogic _ _ _

/-- Actual equal inventories preserve agreement of every three single-type points. -/
theorem three_single_agreement_invariant {N : ℕ} (α β : Composition N)
    (he : coarseningInventory α = coarseningInventory β) (a b c : ℕ+)
    (hsum : a.val + b.val + c.val = N)
    (ha : compositionCutType α a.val = 1) (hb : compositionCutType α b.val = 1)
    (hc : compositionCutType α c.val = 1) :
    (((a.val ∈ properCuts α ↔ b.val ∈ properCuts α) ∧
      (b.val ∈ properCuts α ↔ c.val ∈ properCuts α)) ↔
      ((a.val ∈ properCuts β ↔ b.val ∈ properCuts β) ∧
        (b.val ∈ properCuts β ↔ c.val ∈ properCuts β))) := by
  rw [three_single_agree_iff_absent α a b c hsum ha hb hc,
    three_single_agree_iff_absent β a b c hsum
      ((coarseningInventory_cut_type α β he a.val).symm.trans ha)
      ((coarseningInventory_cut_type α β he b.val).symm.trans hb)
      ((coarseningInventory_cut_type α β he c.val).symm.trans hc), he]

/-- Distinct parts give the exact sum of the six actual ordered prefix tests. -/
theorem threePart_count_distinct {N : ℕ} (α : Composition N) (a b c : ℕ+)
    (hsum : a.val + b.val + c.val = N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (coarseningInventory α).count (a ::ₘ b ::ₘ c ::ₘ 0) =
      (if a.val ∈ properCuts α ∧ N - c.val ∈ properCuts α then 1 else 0) +
      (if b.val ∈ properCuts α ∧ N - c.val ∈ properCuts α then 1 else 0) +
      (if b.val ∈ properCuts α ∧ N - a.val ∈ properCuts α then 1 else 0) +
      (if a.val ∈ properCuts α ∧ N - b.val ∈ properCuts α then 1 else 0) +
      (if c.val ∈ properCuts α ∧ N - b.val ∈ properCuts α then 1 else 0) +
      (if c.val ∈ properCuts α ∧ N - a.val ∈ properCuts α then 1 else 0) := by
  classical
  have habv : a.val ≠ b.val := fun h => hab (PNat.coe_injective h)
  have hacv : a.val ≠ c.val := fun h => hac (PNat.coe_injective h)
  have hbcv : b.val ≠ c.val := fun h => hbc (PNat.coe_injective h)
  change (coarseningInventory α).count (([a, b, c] : List ℕ+) : Multiset ℕ+) = _
  rw [coarseningInventory_count_orders α [a, b, c]
    (by simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, Nat.add_assoc] using hsum), partitionOrders_three, Finset.card_filter]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, List.cons.injEq,
    not_false_eq_true, habv, hacv, hbcv, Ne.symm habv, Ne.symm hacv,
    Ne.symm hbcv, false_and, true_and, or_false, Finset.sum_singleton]
  simp only [threePart_retained_iff α a b c hsum,
    threePart_retained_iff α b a c (by omega),
    threePart_retained_iff α b c a (by omega),
    threePart_retained_iff α a c b (by omega),
    threePart_retained_iff α c a b (by omega),
    threePart_retained_iff α c b a (by omega)]
  omega

/-- At an even-type coordinate, the reflected cut has identical membership. -/
theorem even_cut_reflect_iff {N : ℕ} (α : Composition N) (x : ℕ)
    (hx : compositionCutType α x ≠ 1) : N - x ∈ properCuts α ↔ x ∈ properCuts α := by
  classical
  by_cases h : x ∈ properCuts α <;> by_cases hr : N - x ∈ properCuts α <;>
    simp_all [compositionCutType]

/-- Two single-type points and one even-type point have invariant agreement in the actual data. -/
theorem two_single_agreement_invariant {N : ℕ} (α β : Composition N)
    (he : coarseningInventory α = coarseningInventory β) (a b c : ℕ+)
    (hsum : a.val + b.val + c.val = N)
    (ha : compositionCutType α a.val = 1) (hb : compositionCutType α b.val = 1)
    (hc : compositionCutType α c.val ≠ 1) :
    (a.val ∈ properCuts α ↔ b.val ∈ properCuts α) ↔
      (a.val ∈ properCuts β ↔ b.val ∈ properCuts β) := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  · have hac : a ≠ c := by
      intro h
      apply hc
      simpa only [← h] using ha
    have hbc : b ≠ c := by
      intro h
      apply hc
      simpa only [← h] using hb
    have hba : compositionCutType β a.val = 1 :=
      (coarseningInventory_cut_type α β he a.val).symm.trans ha
    have hbb : compositionCutType β b.val = 1 :=
      (coarseningInventory_cut_type α β he b.val).symm.trans hb
    have hbcType : compositionCutType β c.val ≠ 1 := by
      intro h
      exact hc ((coarseningInventory_cut_type α β he c.val).trans h)
    have hceq : (c.val ∈ properCuts β ↔ c.val ∈ properCuts α) :=
      (coarseningInventory_cut_membership_of_not_one α β he c.val hc).symm
    have hcount := congrArg (Multiset.count (a ::ₘ b ::ₘ c ::ₘ 0)) he
    rw [threePart_count_distinct α a b c hsum hab hac hbc,
      threePart_count_distinct β a b c hsum hab hac hbc] at hcount
    simp only [single_cut_reflect_iff_not α a.val ha, single_cut_reflect_iff_not α b.val hb,
      single_cut_reflect_iff_not β a.val hba, single_cut_reflect_iff_not β b.val hbb,
      even_cut_reflect_iff α c.val hc, even_cut_reflect_iff β c.val hbcType, hceq] at hcount
    by_cases hA : a.val ∈ properCuts α <;> by_cases hB : b.val ∈ properCuts α <;>
      by_cases hC : c.val ∈ properCuts α <;> by_cases hU : a.val ∈ properCuts β <;>
      by_cases hV : b.val ∈ properCuts β <;> simp [hA, hB, hC, hU, hV] at hcount ⊢

end SkewClassInflation
