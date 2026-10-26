/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinPowerBetas
import SkewClassInflation.JoinBetaSets
import SkewClassInflation.SuffixWords

/-!
# Full uncanceled beta sets of every thin composition

Formalizes `eq:thin-beta-lists` and the span reading in `eq:thin-readings`
of `shields-2026-skew-class-inflation.tex`.  All formulas are proved from
the actual ordered sequence of literal zero joins.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- A finite arithmetic grid, with no positivity or injectivity assumed. -/
def arithmeticGrid (z q : ℤ) (m : ℕ) : Finset ℤ :=
  (Finset.range m).image (fun j : ℕ => z + j * q)

/-- The shifted first grid and the second grid make exactly the full combined grid. -/
theorem arithmeticGrid_join (z q : ℤ) (a s : ℕ) :
    (arithmeticGrid z q a).image (fun x => x + s * q) ∪ arithmeticGrid z q s =
      arithmeticGrid z q (a + s) := by
  classical
  calc
    _ = arithmeticGrid z q s ∪
        (Finset.range a).image (fun j : ℕ => z + (s + j) * q) := by
      rw [Finset.union_comm]
      congr 1
      rw [arithmeticGrid, Finset.image_image]
      apply Finset.image_congr
      intro j _
      simp only [Function.comp_apply]
      ring
    _ = arithmeticGrid z q (s + a) := by
      unfold arithmeticGrid
      rw [Finset.range_add_eq_union, Finset.image_union,
        Finset.map_eq_image, Finset.image_image]
      congr 1
    _ = arithmeticGrid z q (a + s) := by rw [Nat.add_comm]

namespace ThinParameters

variable (B : ThinParameters)

/-- The total normalized span is the exact number of copies times the positive block span. -/
theorem chain_span (a : ℕ) (ha : 0 < a) (l : List ℕ) (h : ∀ k ∈ l, 0 < k) :
    (B.chain a ha l h).2.xi 0 = ((a + l.sum : ℕ) : ℤ) * B.boundary.q := by
  induction l generalizing a with
  | nil =>
    change (B.innerPower a ha).xi 0 = (a : ℤ) * B.boundary.q
    exact B.innerPower_span a ha
  | cons b l ih =>
    change (Profile.zeroJoin (B.innerPower a ha)
      (B.chain b (h b List.mem_cons_self) l
        (fun k hk => h k (List.mem_cons_of_mem _ hk))).2).xi 0 = _
    rw [Profile.zeroJoin, Profile.join_span, B.innerPower_span,
      ih b (h b List.mem_cons_self) (fun k hk => h k (List.mem_cons_of_mem _ hk))]
    simp only [List.sum_cons, Nat.cast_add]
    ring

/-- Full upper beta support of a literal ordered chain. -/
theorem chain_rowSet (a : ℕ) (ha : 0 < a) (l : List ℕ) (h : ∀ k ∈ l, 0 < k) :
    (B.chain a ha l h).2.toBetaDiagram.rowSet =
      arithmeticGrid B.b B.boundary.q (a + l.sum) ∪
        (insert (a + l.sum) (wordSuffixSet (a :: l))).image
          (fun k : ℕ => (k : ℤ) * B.boundary.q) := by
  classical
  induction l generalizing a with
  | nil =>
    simp only [chain, B.innerPower_rowSet, List.sum_nil, Nat.add_zero, wordSuffixSet_single,
      Finset.insert_empty, Finset.image_singleton, arithmeticGrid]
    exact Finset.union_comm _ _
  | cons b l ih =>
    change (Profile.zeroJoin (B.innerPower a ha)
      (B.chain b (h b List.mem_cons_self) l
        (fun k hk => h k (List.mem_cons_of_mem _ hk))).2).toBetaDiagram.rowSet = _
    rw [Profile.zeroJoin, Profile.join_rowSet, B.innerPower_rowSet,
      ih b (h b List.mem_cons_self) (fun k hk => h k (List.mem_cons_of_mem _ hk)),
      B.chain_span, wordSuffixSet_cons a (b :: l) (by simp)]
    simp only [Nat.cast_zero, sub_zero, Finset.image_union, Finset.image_singleton,
      Finset.image_insert, List.sum_cons]
    have ht : (a : ℤ) * B.boundary.q + ((b + l.sum : ℕ) : ℤ) * B.boundary.q =
        ((a + (b + l.sum) : ℕ) : ℤ) * B.boundary.q := by push_cast; ring
    rw [ht, ← arithmeticGrid_join B.b B.boundary.q a (b + l.sum)]
    simp only [Finset.insert_eq, arithmeticGrid]
    ac_rfl

/-- Full lower beta support of a literal ordered chain, with the terminal zero retained. -/
theorem chain_colSet (a : ℕ) (ha : 0 < a) (l : List ℕ) (h : ∀ k ∈ l, 0 < k) :
    (B.chain a ha l h).2.toBetaDiagram.colSet =
      arithmeticGrid ((B.b : ℤ) - B.c) B.boundary.q (a + l.sum) ∪
        (insert 0 (wordSuffixSet (a :: l))).image (fun k : ℕ => (k : ℤ) * B.boundary.q) := by
  classical
  induction l generalizing a with
  | nil =>
    simp only [chain, B.innerPower_colSet, List.sum_nil, Nat.add_zero, wordSuffixSet_single,
      Finset.insert_empty, Finset.image_singleton, Nat.cast_zero, zero_mul, arithmeticGrid]
    exact Finset.union_comm _ _
  | cons b l ih =>
    change (Profile.zeroJoin (B.innerPower a ha)
      (B.chain b (h b List.mem_cons_self) l
        (fun k hk => h k (List.mem_cons_of_mem _ hk))).2).toBetaDiagram.colSet = _
    rw [Profile.zeroJoin, Profile.join_colSet, B.innerPower_colSet,
      ih b (h b List.mem_cons_self) (fun k hk => h k (List.mem_cons_of_mem _ hk)),
      B.chain_span, wordSuffixSet_cons a (b :: l) (by simp)]
    simp only [Nat.cast_zero, sub_zero, Finset.image_union, Finset.image_singleton,
      Finset.image_insert, List.sum_cons, zero_mul, zero_add]
    rw [← arithmeticGrid_join ((B.b : ℤ) - B.c) B.boundary.q a (b + l.sum)]
    simp only [Finset.insert_eq, arithmeticGrid]
    ac_rfl

/-- The actual composite span in the full arbitrary-composition domain. -/
theorem diagram_span {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (B.diagram α hM).2.xi 0 = (M : ℤ) * B.boundary.q := by
  unfold diagram
  split
  · rename_i he
    have h := α.blocks_sum
    rw [he] at h
    simp only [List.sum_nil] at h
    omega
  · rename_i a l he
    have hs : a + l.sum = M := by simpa [he] using α.blocks_sum
    have hh := B.chain_span a
      (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
      (fun k hk => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hk))
    rw [hs] at hh
    exact hh

/-- The full upper beta list as the exact grid-plus-suffix set in the manuscript. -/
theorem diagram_rowSet {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (B.diagram α hM).2.toBetaDiagram.rowSet =
      arithmeticGrid B.b B.boundary.q M ∪
        (insert M (suffixSet α)).image (fun k : ℕ => (k : ℤ) * B.boundary.q) := by
  unfold diagram
  split
  · rename_i he
    have h := α.blocks_sum
    rw [he] at h
    simp only [List.sum_nil] at h
    omega
  · rename_i a l he
    have hs : a + l.sum = M := by simpa [he] using α.blocks_sum
    have hT : wordSuffixSet (a :: l) = suffixSet α := by
      rw [← he, wordSuffixSet_blocks]
    have hh := B.chain_rowSet a
      (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
      (fun k hk => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hk))
    rw [hs, hT] at hh
    exact hh

/-- The full lower beta list includes every proper suffix beta and its terminal zero. -/
theorem diagram_colSet {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (B.diagram α hM).2.toBetaDiagram.colSet =
      arithmeticGrid ((B.b : ℤ) - B.c) B.boundary.q M ∪
        (insert 0 (suffixSet α)).image (fun k : ℕ => (k : ℤ) * B.boundary.q) := by
  unfold diagram
  split
  · rename_i he
    have h := α.blocks_sum
    rw [he] at h
    simp only [List.sum_nil] at h
    omega
  · rename_i a l he
    have hs : a + l.sum = M := by simpa [he] using α.blocks_sum
    have hT : wordSuffixSet (a :: l) = suffixSet α := by
      rw [← he, wordSuffixSet_blocks]
    have hh := B.chain_colSet a
      (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
      (fun k hk => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hk))
    rw [hs, hT] at hh
    exact hh

end ThinParameters
end SkewClassInflation
