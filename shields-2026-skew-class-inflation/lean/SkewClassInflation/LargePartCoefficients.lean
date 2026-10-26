/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.LargePartRanks

/-!
# Exact larger-part coefficients of ordinary products

The inner-inventory extraction step in factor transport for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The endpoint multiplier is the actual reflected cut type, so at a
repeated midpoint the two distinct endpoint orders are both retained.
Sorry-free.
-/

namespace SkewClassInflation

/-- Every ordering of a positive partition has its exact original part count. -/
theorem partitionOrders_length (l : List ℕ+) (w : List ℕ) (hw : w ∈ partitionOrders l) :
    w.length = l.length := by
  have hp := List.mem_permutations.mp (List.mem_toFinset.mp hw)
  simpa only [List.length_map] using hp.length_eq

/-- Every part of a genuine multipart order is smaller than its total weight. -/
theorem partitionOrders_part_lt (l : List ℕ+) (N : ℕ)
    (hsum : (l.map PNat.val).sum = N) (hl : 2 ≤ l.length)
    (w : List ℕ) (hw : w ∈ partitionOrders l) : ∀ a ∈ w, a < N := by
  let α : Composition N := ⟨w, fun {a} ha => partitionOrders_pos l w hw a ha,
    (partitionOrders_sum l w hw).trans hsum⟩
  have hlen : 2 ≤ α.length := by
    change 2 ≤ w.length
    rw [partitionOrders_length l w hw]
    exact hl
  exact fun a ha => composition_part_lt_of_multipart α hlen a ha

/-- Inserting a distinguished part gives an actual ordering of the augmented partition. -/
theorem insertLargePart_mem_partitionOrders (l : List ℕ+) (q : ℕ+)
    (w : List ℕ) (hw : w ∈ partitionOrders l) (k : ℕ) :
    insertLargePart w q.val k ∈ partitionOrders (q :: l) := by
  have hp := List.mem_permutations.mp (List.mem_toFinset.mp hw)
  have hm : (insertLargePart w q.val k).Perm (q.val :: w) := by
    simpa only [insertLargePart, List.take_append_drop] using
      (List.perm_middle : (w.take k ++ q.val :: w.drop k).Perm (q.val :: (w.take k ++ w.drop k)))
  exact List.mem_toFinset.mpr (List.mem_permutations.mpr (hm.trans (hp.cons q.val)))

/-- An augmented multipart coefficient is the inner coefficient times the exact rank multiplier. -/
theorem compositionProduct_largePart_count {M N : ℕ}
    (δ : Composition M) (ε : Composition N) (hM : 2 ≤ M) (hN : 0 < N)
    (l : List ℕ+) (hsum : (l.map PNat.val).sum = N) (hl : 2 ≤ l.length) :
    let q : ℕ+ := ⟨(M - 1) * N, Nat.mul_pos (by omega) hN⟩
    (coarseningInventory (compositionProduct δ ε)).count ((q :: l : List ℕ+) : Multiset ℕ+) =
      (l.length - 1 + compositionCutType δ 1) *
        (coarseningInventory ε).count (l : Multiset ℕ+) := by
  classical
  dsimp only
  let q : ℕ+ := ⟨(M - 1) * N, Nat.mul_pos (by omega) hN⟩
  have hq : N ≤ q.val := by
    change N ≤ (M - 1) * N
    have hh := Nat.mul_le_mul_right N (show 1 ≤ M - 1 by omega)
    simpa only [one_mul] using hh
  have hweight : ((q :: l).map PNat.val).sum = M * N := by
    rw [List.map_cons, List.sum_cons, hsum]
    change (M - 1) * N + N = M * N
    have he := congrArg (fun x => x * N) (show M - 1 + 1 = M by omega)
    simpa only [Nat.add_mul, one_mul] using he
  rw [coarseningInventory_count_orders (compositionProduct δ ε) (q :: l) hweight,
    coarseningInventory_count_orders ε l hsum]
  let A := (partitionOrders l).filter (fun w => wordProperCuts w ⊆ properCuts ε)
  let R := largePartRanks δ l.length
  let B := (partitionOrders (q :: l)).filter
    (fun w => wordProperCuts w ⊆ properCuts (compositionProduct δ ε))
  have hno (w : List ℕ) (hw : w ∈ partitionOrders l) : q.val ∉ w := by
    intro hmem
    have hh := partitionOrders_part_lt l N hsum hl w hw q.val hmem
    omega
  have hc : (A ×ˢ R).card = B.card := by
    refine Finset.card_bij (fun p _ => insertLargePart p.1 q.val p.2) ?_ ?_ ?_
    · intro p hp
      obtain ⟨hw, hr⟩ := Finset.mem_product.mp hp
      obtain ⟨ho, hcut⟩ := Finset.mem_filter.mp hw
      have hlen := partitionOrders_length l p.1 ho
      have hsumw := (partitionOrders_sum l p.1 ho).trans hsum
      have hpos := partitionOrders_pos l p.1 ho
      have hr' : p.2 ∈ largePartRanks δ p.1.length := by rwa [hlen]
      have hib := (mem_largePartRanks δ p.1.length p.2).mp hr' |>.1
      exact Finset.mem_filter.mpr ⟨insertLargePart_mem_partitionOrders l q p.1 ho p.2,
        (insertLargePart_retained_iff δ ε hM hN p.1 hsumw hpos (by omega) p.2 hib).mpr
          ⟨hcut, hr'⟩⟩
    · intro p hp r hr he
      have hwp := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).1
      have hwr := (Finset.mem_filter.mp (Finset.mem_product.mp hr).1).1
      have hpi := ((mem_largePartRanks δ l.length p.2).mp (Finset.mem_product.mp hp).2).1
      have hri := ((mem_largePartRanks δ l.length r.2).mp (Finset.mem_product.mp hr).2).1
      have hpl := partitionOrders_length l p.1 hwp
      have hrl := partitionOrders_length l r.1 hwr
      have hh := insertLargePart_injective q.val p.1 r.1 p.2 r.2
        (hno p.1 hwp) (hno r.1 hwr) (by omega) (by omega) he
      exact Prod.ext hh.1 hh.2
    · intro v hv
      obtain ⟨ho, hcut⟩ := Finset.mem_filter.mp hv
      obtain ⟨w, hw, i, hi, he⟩ := partitionOrders_cons_insert l q v ho
      have hlen := partitionOrders_length l w hw
      have hsumw := (partitionOrders_sum l w hw).trans hsum
      have hpos := partitionOrders_pos l w hw
      have hret := (insertLargePart_retained_iff δ ε hM hN w hsumw hpos
        (by omega) i hi).mp (by
          change wordProperCuts (insertLargePart w q.val i) ⊆ _
          rwa [he])
      refine ⟨(w, i), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hw, hret.1⟩, ?_⟩, he⟩
      change i ∈ largePartRanks δ l.length
      simpa only [hlen] using hret.2
  change B.card = (l.length - 1 + compositionCutType δ 1) * A.card
  rw [← hc, Finset.card_product]
  change A.card * (largePartRanks δ l.length).card = _
  rw [largePartRanks_card δ l.length (by omega), Nat.mul_comm]

end SkewClassInflation
