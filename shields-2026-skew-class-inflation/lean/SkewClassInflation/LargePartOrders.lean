/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FactorOuterInventory

/-!
# Distinct orders with one distinguished larger part

The inner-inventory extraction step in factor transport for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The inserted part is absent from every smaller word, so its position and
the remaining order are both recoverable without multiplicity loss.
Sorry-free.
-/

namespace SkewClassInflation

/-- Insert the distinguished part at a specified prefix rank. -/
def insertLargePart (w : List ℕ) (q k : ℕ) : List ℕ := w.take k ++ q :: w.drop k

/-- The unique distinguished part's actual position is its insertion rank. -/
theorem insertLargePart_idxOf (w : List ℕ) (q k : ℕ)
    (hq : q ∉ w) (hk : k ≤ w.length) : (insertLargePart w q k).idxOf q = k := by
  rw [insertLargePart, List.idxOf_append_of_notMem
    (fun hx => hq (List.mem_of_mem_take hx))]
  simp only [List.idxOf_cons_self, add_zero, List.length_take, Nat.min_eq_left hk]

/-- Removing the unique distinguished part recovers the complete original order. -/
theorem insertLargePart_erase (w : List ℕ) (q k : ℕ) (hq : q ∉ w) :
    (insertLargePart w q k).erase q = w := by
  rw [insertLargePart, List.erase_append_right (q :: w.drop k)
    (fun hx => hq (List.mem_of_mem_take hx)), List.erase_cons_head, List.take_append_drop]

/-- The original word and insertion rank are determined by the actual inserted order. -/
theorem insertLargePart_injective (q : ℕ) (u v : List ℕ) (i j : ℕ)
    (hu : q ∉ u) (hv : q ∉ v) (hi : i ≤ u.length) (hj : j ≤ v.length)
    (he : insertLargePart u q i = insertLargePart v q j) : u = v ∧ i = j := by
  have hword := congrArg (fun w : List ℕ => w.erase q) he
  rw [insertLargePart_erase u q i hu, insertLargePart_erase v q j hv] at hword
  have hindex := congrArg (fun w : List ℕ => w.idxOf q) he
  rw [insertLargePart_idxOf u q i hu hi, insertLargePart_idxOf v q j hv hj] at hindex
  exact ⟨hword, hindex⟩

/-- Every distinct ordering of an augmented partition has an actual insertion presentation. -/
theorem partitionOrders_cons_insert (l : List ℕ+) (q : ℕ+) (v : List ℕ)
    (hv : v ∈ partitionOrders (q :: l)) :
    ∃ w ∈ partitionOrders l, ∃ k ≤ w.length, insertLargePart w q.val k = v := by
  have hp : v.Perm (q.val :: l.map PNat.val) := by
    simpa only [partitionOrders, List.mem_toFinset, List.mem_permutations,
      List.map_cons] using hv
  have hq : q.val ∈ v := hp.symm.subset List.mem_cons_self
  obtain ⟨a, b, he⟩ := List.append_of_mem hq
  have hsmall : (a ++ b).Perm (l.map PNat.val) := by
    rw [he] at hp
    exact (List.perm_middle.symm.trans hp).cons_inv
  refine ⟨a ++ b, ?_, a.length, by simp, ?_⟩
  · exact List.mem_toFinset.mpr (List.mem_permutations.mpr hsmall)
  · simp only [insertLargePart, List.take_left, List.drop_left]
    exact he.symm

end SkewClassInflation
