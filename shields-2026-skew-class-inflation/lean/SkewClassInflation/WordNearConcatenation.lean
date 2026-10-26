/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.WordPrefixCuts

/-!
# Ordinary near-concatenation of literal composition words

The word operation in `eq:ribbon-composition` of
`shields-2026-skew-class-inflation.tex`.  Only the incident endpoint
parts are added.  Its proper cuts are the old cuts translated by the
actual whole-word weight; the shared boundary itself is removed.
Sorry-free.
-/

namespace SkewClassInflation

/-- Proper prefix cuts of a literal word, in the same convention as `properCuts`. -/
def wordProperCuts (w : List ℕ) : Finset ℕ := wordSuffixSet w.reverse

/-- The terminal part is excluded from the proper prefix inventory. -/
theorem wordProperCuts_append_single (u : List ℕ) (a : ℕ) :
    wordProperCuts (u ++ [a]) = prefixEnds u :=
  wordSuffixSet_reverse_append_single u a

/-- The literal list encoding agrees with the existing composition boundary encoding. -/
theorem wordProperCuts_blocks {N : ℕ} (α : Composition N) :
    wordProperCuts α.blocks = properCuts α := by
  rw [wordProperCuts, ← Composition.reverse_blocks, wordSuffixSet_blocks,
    ← properCuts_eq_suffixSet]

/-- Ordinary near-concatenation adds the last and first parts, with empty words as units. -/
def wordNear (u v : List ℕ) : List ℕ :=
  match u.reverse, v with
  | [], _ => v
  | _, [] => u
  | a :: r, b :: s => r.reverse ++ ((a + b) :: s)

/-- Literal endpoint reconstruction gives the defining nonempty word formula. -/
theorem wordNear_append_cons (u : List ℕ) (a b : ℕ) (v : List ℕ) :
    wordNear (u ++ [a]) (b :: v) = u ++ ((a + b) :: v) := by
  simp only [wordNear, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.reverse_reverse]

/-- Near-concatenation preserves exactly the combined whole-word weight. -/
theorem wordNear_sum (u v : List ℕ) : (wordNear u v).sum = u.sum + v.sum := by
  rcases List.eq_nil_or_concat' u with rfl | ⟨u, a, rfl⟩
  · simp [wordNear]
  · cases v with
    | nil => simp [wordNear]
    | cons b v =>
      rw [wordNear_append_cons]
      simp only [List.sum_append, List.sum_cons, List.sum_nil]
      omega

/-- Positive words remain positive under the actual endpoint addition. -/
theorem wordNear_pos (u v : List ℕ) (hu : ∀ a ∈ u, 0 < a) (hv : ∀ a ∈ v, 0 < a) :
    ∀ a ∈ wordNear u v, 0 < a := by
  rcases List.eq_nil_or_concat' u with rfl | ⟨u, a, rfl⟩
  · simpa only [wordNear, List.reverse_nil] using hv
  · cases v with
    | nil => simpa only [wordNear, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.singleton_append] using hu
    | cons b v =>
      rw [wordNear_append_cons]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hu x (List.mem_append_left _ hx)
      · rcases List.mem_cons.mp hx with rfl | hx
        · have ha := hu a (List.mem_append_right _ (List.mem_singleton_self a))
          have hb := hv b List.mem_cons_self
          omega
        · exact hv x (List.mem_cons_of_mem _ hx)

/-- A literal concatenation retains its shared boundary as well as both proper cut sets. -/
theorem wordProperCuts_append (u v : List ℕ) (hu : u ≠ []) (hv : v ≠ []) :
    wordProperCuts (u ++ v) = wordProperCuts u ∪
      insert u.sum ((wordProperCuts v).image (fun x => u.sum + x)) := by
  classical
  obtain ⟨u, a, rfl⟩ := (List.eq_nil_or_concat' u).resolve_left hu
  obtain ⟨v, b, rfl⟩ := (List.eq_nil_or_concat' v).resolve_left hv
  rw [← List.append_assoc, wordProperCuts_append_single,
    wordProperCuts_append_single, wordProperCuts_append_single]
  rw [prefixEnds_append, prefixEnds_append]
  simp only [prefixEnds, Finset.image_empty, List.sum_append, List.sum_singleton]
  ext x
  simp

/-- Endpoint addition removes precisely the shared cut, including singleton input words. -/
theorem wordProperCuts_near (u v : List ℕ) (hu : u ≠ []) (hv : v ≠ []) :
    wordProperCuts (wordNear u v) = wordProperCuts u ∪
      (wordProperCuts v).image (fun x => u.sum + x) := by
  classical
  obtain ⟨u, a, rfl⟩ := (List.eq_nil_or_concat' u).resolve_left hu
  cases v with
  | nil => exact (hv rfl).elim
  | cons b v =>
    rw [wordNear_append_cons, wordProperCuts_append_single]
    rcases List.eq_nil_or_concat' v with rfl | ⟨v, c, rfl⟩
    · rw [wordProperCuts_append_single]
      have hz : wordProperCuts [b] = ∅ := wordProperCuts_append_single [] b
      simp only [hz, Finset.image_empty, Finset.union_empty]
    · have h1 : u ++ ((a + b) :: (v ++ [c])) = (u ++ ((a + b) :: v)) ++ [c] := by
        simp only [List.append_assoc, List.cons_append]
      have h2 : b :: (v ++ [c]) = (b :: v) ++ [c] := by rw [List.cons_append]
      rw [h1, h2, wordProperCuts_append_single, wordProperCuts_append_single,
        prefixEnds_append]
      have ha : a + b = b + a := Nat.add_comm _ _
      rw [ha, prefixEnds_head_add, Finset.image_image]
      simp only [List.sum_append, List.sum_singleton]
      congr 1
      apply Finset.image_congr
      intro x hx
      dsimp only [Function.comp_apply]
      omega

/-- The empty word has no proper cut. -/
theorem wordProperCuts_nil : wordProperCuts [] = ∅ := by
  simp [wordProperCuts, wordSuffixSet]

/-- A singleton word has no proper cut. -/
theorem wordProperCuts_single (a : ℕ) : wordProperCuts [a] = ∅ :=
  wordProperCuts_append_single [] a

/-- Empty words are the two units for ordinary near-concatenation. -/
theorem wordNear_nil (w : List ℕ) : wordNear w [] = w ∧ wordNear [] w = w := by
  rcases List.eq_nil_or_concat' w with rfl | ⟨u, a, rfl⟩
  · simp [wordNear]
  · simp [wordNear]

/-- Positive total weight excludes an empty word. -/
theorem word_ne_nil_of_sum_pos (w : List ℕ) (hw : 0 < w.sum) : w ≠ [] := by
  intro he
  subst w
  simp only [List.sum_nil] at hw
  omega

/-- Ordinary near powers, including the empty zeroth power. -/
def wordNearPower (w : List ℕ) : ℕ → List ℕ
  | 0 => []
  | m + 1 => wordNear w (wordNearPower w m)

/-- A near power has its actual copy-count times the original whole-word weight. -/
theorem wordNearPower_sum (w : List ℕ) (m : ℕ) : (wordNearPower w m).sum = m * w.sum := by
  induction m with
  | zero => simp [wordNearPower]
  | succ m ih =>
    rw [wordNearPower, wordNear_sum, ih]
    ring

/-- Ordinary near powers preserve positivity of every part. -/
theorem wordNearPower_pos (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) (m : ℕ) :
    ∀ a ∈ wordNearPower w m, 0 < a := by
  induction m with
  | zero => simp [wordNearPower]
  | succ m ih => exact wordNear_pos w (wordNearPower w m) hw ih

/-- The proper cuts are exactly the repeated inner cuts, with no cuts at whole-copy multiples. -/
theorem wordNearPower_cuts (w : List ℕ) (hw : 0 < w.sum) (m x : ℕ) :
    x ∈ wordProperCuts (wordNearPower w m) ↔
      ∃ j, j < m ∧ ∃ y ∈ wordProperCuts w, x = j * w.sum + y := by
  classical
  induction m generalizing x with
  | zero => simp only [wordNearPower, wordProperCuts_nil, Finset.notMem_empty,
      Nat.not_lt_zero, false_and, exists_false]
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      rw [wordNearPower, wordNearPower, (wordNear_nil w).1]
      simp only [Nat.lt_one_iff, zero_mul, zero_add, exists_eq_left]
      constructor
      · intro hx; exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact hy
    · have hp : 0 < m := by omega
      have hn := word_ne_nil_of_sum_pos (wordNearPower w m)
        (by rw [wordNearPower_sum]; exact Nat.mul_pos hp hw)
      rw [wordNearPower, wordProperCuts_near w _ (word_ne_nil_of_sum_pos w hw) hn]
      simp only [Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (hx | ⟨z, hz, rfl⟩)
        · exact ⟨0, by omega, x, hx, by simp⟩
        · obtain ⟨j, hj, y, hy, rfl⟩ := (ih z).mp hz
          exact ⟨j + 1, by omega, y, hy, by ring⟩
      · rintro ⟨j, hj, y, hy, rfl⟩
        cases j with
        | zero => exact Or.inl (by simpa only [zero_mul, zero_add] using hy)
        | succ j =>
          exact Or.inr ⟨j * w.sum + y, (ih _).mpr ⟨j, by omega, y, hy, rfl⟩, by ring⟩

/-- A nonempty final block shields every earlier block from the endpoint merger. -/
theorem wordNear_append_left (u v w : List ℕ) (hv : v ≠ []) :
    wordNear (u ++ v) w = u ++ wordNear v w := by
  obtain ⟨v, a, rfl⟩ := (List.eq_nil_or_concat' v).resolve_left hv
  cases w with
  | nil => rw [(wordNear_nil _).1, (wordNear_nil _).1]
  | cons b w =>
    rw [← List.append_assoc, wordNear_append_cons, wordNear_append_cons,
      List.append_assoc]

/-- Ordinary endpoint addition is associative, including the empty-word boundaries. -/
theorem wordNear_assoc (u v w : List ℕ) :
    wordNear (wordNear u v) w = wordNear u (wordNear v w) := by
  rcases List.eq_nil_or_concat' u with rfl | ⟨u, a, rfl⟩
  · rw [(wordNear_nil _).2, (wordNear_nil _).2]
  · cases v with
    | nil => rw [(wordNear_nil _).1, (wordNear_nil _).2]
    | cons b v =>
      cases w with
      | nil => rw [(wordNear_nil _).1, (wordNear_nil _).1]
      | cons c w =>
        rw [wordNear_append_cons, wordNear_append_left u ((a + b) :: v) (c :: w)
          (by simp)]
        rcases List.eq_nil_or_concat' v with rfl | ⟨v, d, rfl⟩
        · change u ++ ((a + b + c) :: w) = wordNear (u ++ [a]) ((b + c) :: w)
          rw [wordNear_append_cons, Nat.add_assoc]
        · have h1 : (a + b) :: (v ++ [d]) = ((a + b) :: v) ++ [d] := by
            rw [List.cons_append]
          have h2 : b :: (v ++ [d]) = (b :: v) ++ [d] := by rw [List.cons_append]
          rw [h1, h2, wordNear_append_cons, wordNear_append_cons]
          simp only [List.cons_append, wordNear_append_cons]

/-- The copy counts of two ordinary near powers add under one further endpoint merger. -/
theorem wordNearPower_add (w : List ℕ) (m n : ℕ) :
    wordNearPower w (m + n) = wordNear (wordNearPower w m) (wordNearPower w n) := by
  induction m with
  | zero => simp only [Nat.zero_add, wordNearPower, (wordNear_nil _).2]
  | succ m ih =>
    rw [Nat.succ_add, wordNearPower, ih, ← wordNear_assoc, wordNearPower]

/-- Merging two nonempty words never removes their merged endpoint. -/
theorem wordNear_ne_nil (u v : List ℕ) (hu : u ≠ []) (hv : v ≠ []) :
    wordNear u v ≠ [] := by
  obtain ⟨u, a, rfl⟩ := (List.eq_nil_or_concat' u).resolve_left hu
  cases v with
  | nil => exact (hv rfl).elim
  | cons b v => rw [wordNear_append_cons]; simp

/-- A retained leading word shields every later block from the endpoint merger. -/
theorem wordNear_append_right (u v w : List ℕ) (hv : v ≠ []) :
    wordNear u (v ++ w) = wordNear u v ++ w := by
  rcases List.eq_nil_or_concat' u with rfl | ⟨u, a, rfl⟩
  · rw [(wordNear_nil _).2, (wordNear_nil _).2]
  · cases v with
    | nil => exact (hv rfl).elim
    | cons b v =>
      rw [List.cons_append, wordNear_append_cons, wordNear_append_cons]
      simp only [List.append_assoc, List.cons_append]

/-- The first part of a word is retained whenever the endpoint merger occurs later. -/
theorem wordNear_cons (a : ℕ) (u v : List ℕ) (hu : u ≠ []) :
    wordNear (a :: u) v = a :: wordNear u v := by
  simpa only [List.singleton_append] using wordNear_append_left [a] u v hu

/-- Reversing an endpoint merger reverses the order of its two actual input words. -/
theorem wordNear_reverse (u v : List ℕ) :
    (wordNear u v).reverse = wordNear v.reverse u.reverse := by
  rcases List.eq_nil_or_concat' u with rfl | ⟨u, a, rfl⟩
  · simp only [(wordNear_nil _).2, List.reverse_nil, (wordNear_nil _).1]
  · cases v with
    | nil => simp only [(wordNear_nil _).1, List.reverse_nil, (wordNear_nil _).2]
    | cons b v =>
      rw [wordNear_append_cons]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.append_assoc, List.singleton_append, wordNear_append_cons, Nat.add_comm]

/-- Reversal commutes with every actual ordinary near power. -/
theorem wordNearPower_reverse (w : List ℕ) (m : ℕ) :
    (wordNearPower w m).reverse = wordNearPower w.reverse m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [wordNearPower, wordNear_reverse, ih]
    simpa only [wordNearPower, (wordNear_nil _).1] using
      (wordNearPower_add w.reverse m 1).symm

/-- Literal proper prefix positions enumerate exactly the nonterminal positive prefix lengths. -/
theorem wordProperCuts_mem_partial (w : List ℕ) (x : ℕ) :
    x ∈ wordProperCuts w ↔
      ∃ i : ℕ, 0 < i ∧ i < w.length ∧ (w.take i).sum = x := by
  simp only [wordProperCuts, wordSuffixSet, List.length_reverse, List.reverse_reverse,
    Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨i, ⟨hi, hl⟩, he⟩
    exact ⟨i, by omega, hl, he⟩
  · rintro ⟨i, hi, hl, he⟩
    exact ⟨i, ⟨by omega, hl⟩, he⟩

/-- Reversed prefix cuts are exactly the complementary original prefix sums. -/
theorem wordProperCuts_reverse_sum (w : List ℕ) (x : ℕ) :
    x ∈ wordProperCuts w.reverse ↔ ∃ y ∈ wordProperCuts w, y + x = w.sum := by
  rw [wordProperCuts_mem_partial]
  constructor
  · rintro ⟨i, hi, hl, he⟩
    have hilen : i < w.length := by simpa only [List.length_reverse] using hl
    have hs := List.sum_take_add_sum_drop w (w.length - i)
    have ht : (w.reverse.take i).sum = (w.drop (w.length - i)).sum := by
      rw [List.take_reverse, List.sum_reverse]
    refine ⟨(w.take (w.length - i)).sum, ?_, ?_⟩
    · exact (wordProperCuts_mem_partial w _).mpr
        ⟨w.length - i, by omega, by omega, rfl⟩
    · rw [ht] at he
      omega
  · rintro ⟨y, hy, he⟩
    obtain ⟨j, hj, hlen, hjy⟩ := (wordProperCuts_mem_partial w y).mp hy
    refine ⟨w.length - j, by omega, by simp only [List.length_reverse]; omega, ?_⟩
    rw [List.take_reverse, List.sum_reverse]
    have hjj : w.length - (w.length - j) = j := by omega
    rw [hjj]
    have hs := List.sum_take_add_sum_drop w j
    omega

/-- A reversed proper cut has the reflected original value throughout the true weight interval. -/
theorem wordProperCuts_reverse_reflect (w : List ℕ) (x : ℕ) (hx : x ≤ w.sum) :
    x ∈ wordProperCuts w.reverse ↔ w.sum - x ∈ wordProperCuts w := by
  rw [wordProperCuts_reverse_sum]
  constructor
  · rintro ⟨y, hy, he⟩
    have hh : y = w.sum - x := by omega
    exact hh ▸ hy
  · intro hy
    exact ⟨w.sum - x, hy, Nat.sub_add_cancel hx⟩

end SkewClassInflation
