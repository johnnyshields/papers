/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.WordNearConcatenation

/-!
# Ordinary composition product as a literal word

The concatenation of ordinary near powers in `eq:ribbon-composition`
of `shields-2026-skew-class-inflation.tex`.  Its actual cut set
retains the outer cuts at whole-inner multiples and repeats the
proper inner cuts at every copy position.  Sorry-free.
-/

namespace SkewClassInflation

/-- The literal concatenation of one ordinary near power for each outer part. -/
def wordCompose (inner : List ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: l => wordNearPower inner a ++ wordCompose inner l

/-- The recursive operation is exactly the paper's concatenated list of near powers. -/
theorem wordCompose_eq_flatten (inner outer : List ℕ) :
    wordCompose inner outer = (outer.map (wordNearPower inner)).flatten := by
  induction outer with
  | nil => rfl
  | cons a l ih => simp only [wordCompose, List.map_cons, List.flatten_cons, ih]

/-- The composition product has the actual product weight. -/
theorem wordCompose_sum (inner outer : List ℕ) :
    (wordCompose inner outer).sum = outer.sum * inner.sum := by
  induction outer with
  | nil => simp [wordCompose]
  | cons a l ih =>
    rw [wordCompose, List.sum_append, wordNearPower_sum, ih, List.sum_cons]
    ring

/-- Both genuine positive input words supply positivity of the composed word. -/
theorem wordCompose_pos (inner outer : List ℕ) (hi : ∀ a ∈ inner, 0 < a)
    (ho : ∀ a ∈ outer, 0 < a) : ∀ a ∈ wordCompose inner outer, 0 < a := by
  induction outer with
  | nil => simp [wordCompose]
  | cons a l ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact wordNearPower_pos inner hi a x hx
    · exact ih (fun b hb => ho b (List.mem_cons_of_mem _ hb)) x hx

/-- Prepending a part introduces its one new proper boundary and shifts the remaining ones. -/
theorem wordProperCuts_cons (a : ℕ) (l : List ℕ) (hl : l ≠ []) :
    wordProperCuts (a :: l) = insert a ((wordProperCuts l).image (fun x => a + x)) := by
  have he := wordProperCuts_append [a] l (by simp) hl
  simpa only [List.singleton_append, wordProperCuts_single,
    Finset.empty_union, List.sum_singleton] using he

/-- All proper cuts of a positive word lie strictly between its endpoints. -/
theorem wordProperCuts_bounds (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) :
    ∀ x ∈ wordProperCuts w, 0 < x ∧ x < w.sum := by
  let α : Composition w.sum := ⟨w, fun {a} ha => hw a ha, rfl⟩
  have he : wordProperCuts w = properCuts α := wordProperCuts_blocks α
  rw [he]
  exact properCuts_bounds α

/-- Cuts of the literal product separate into outer boundaries and repeated inner cuts. -/
theorem wordCompose_cuts (inner outer : List ℕ) (hi : 0 < inner.sum)
    (ho : ∀ a ∈ outer, 0 < a) (x : ℕ) :
    x ∈ wordProperCuts (wordCompose inner outer) ↔
      (∃ t ∈ wordProperCuts outer, x = t * inner.sum) ∨
        ∃ j, j < outer.sum ∧ ∃ y ∈ wordProperCuts inner, x = j * inner.sum + y := by
  classical
  induction outer generalizing x with
  | nil => simp only [wordCompose, wordProperCuts_nil, Finset.notMem_empty,
      false_and, exists_false, List.sum_nil, Nat.not_lt_zero, false_or]
  | cons a l ih =>
    have ha := ho a List.mem_cons_self
    have ht : ∀ b ∈ l, 0 < b := fun b hb => ho b (List.mem_cons_of_mem _ hb)
    by_cases hl : l = []
    · subst l
      simp only [wordCompose, List.append_nil, wordProperCuts_single,
        Finset.notMem_empty, false_and, exists_false, false_or, List.sum_singleton]
      exact wordNearPower_cuts inner hi a x
    · have hs : 0 < l.sum := by
        cases l with
        | nil => contradiction
        | cons b l => have := ht b List.mem_cons_self; simp only [List.sum_cons]; omega
      have hn1 := word_ne_nil_of_sum_pos (wordNearPower inner a)
        (by rw [wordNearPower_sum]; exact Nat.mul_pos ha hi)
      have hn2 := word_ne_nil_of_sum_pos (wordCompose inner l)
        (by rw [wordCompose_sum]; exact Nat.mul_pos hs hi)
      rw [wordCompose, wordProperCuts_append _ _ hn1 hn2, wordNearPower_sum,
        wordProperCuts_cons a l hl]
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨j, hj, y, hy, he⟩ := (wordNearPower_cuts inner hi a x).mp hx
          exact Or.inr ⟨j, by simp only [List.sum_cons]; omega, y, hy, he⟩
        · rcases Finset.mem_insert.mp hx with hx | hx
          · exact Or.inl ⟨a, Finset.mem_insert_self _ _, hx⟩
          · obtain ⟨z, hz, hx⟩ := Finset.mem_image.mp hx
            rcases (ih ht z).mp hz with ⟨t, ht, he⟩ | ⟨j, hj, y, hy, he⟩
            · refine Or.inl ⟨a + t, Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨t, ht, rfl⟩), ?_⟩
              nlinarith
            · refine Or.inr ⟨a + j, by simp only [List.sum_cons]; omega, y, hy, ?_⟩
              nlinarith
      · rintro (⟨t, hcut, hx⟩ | ⟨j, hj, y, hy, hx⟩)
        · rcases Finset.mem_insert.mp hcut with rfl | hcut
          · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _ |> fun h => hx ▸ h)
          · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hcut
            apply Finset.mem_union_right
            apply Finset.mem_insert_of_mem
            refine Finset.mem_image.mpr ⟨u * inner.sum, (ih ht _).mpr
              (Or.inl ⟨u, hu, rfl⟩), ?_⟩
            nlinarith
        · by_cases hja : j < a
          · apply Finset.mem_union_left
            exact (wordNearPower_cuts inner hi a x).mpr ⟨j, hja, y, hy, hx⟩
          · apply Finset.mem_union_right
            apply Finset.mem_insert_of_mem
            have hj' : j - a < l.sum := by simp only [List.sum_cons] at hj; omega
            refine Finset.mem_image.mpr ⟨(j - a) * inner.sum + y,
              (ih ht _).mpr (Or.inr ⟨j - a, hj', y, hy, rfl⟩), ?_⟩
            have he : a + (j - a) = j := by omega
            nlinarith

/-- The literal product's cut test is exactly the canonical quotient-and-remainder test. -/
theorem wordCompose_cuts_mod (inner outer : List ℕ)
    (hi : ∀ a ∈ inner, 0 < a) (hW : 0 < inner.sum)
    (ho : ∀ a ∈ outer, 0 < a) (x : ℕ)
    (hT : x < outer.sum * inner.sum) :
    x ∈ wordProperCuts (wordCompose inner outer) ↔
      if x % inner.sum = 0 then x / inner.sum ∈ wordProperCuts outer
      else x % inner.sum ∈ wordProperCuts inner := by
  classical
  rw [wordCompose_cuts inner outer hW ho x]
  have hd := Nat.div_add_mod x inner.sum
  by_cases hmod : x % inner.sum = 0
  · rw [ite_eq_left hmod]
    constructor
    · rintro (⟨t, ht, he⟩ | ⟨j, hj, y, hy, he⟩)
      · have hh : x / inner.sum = t := by nlinarith
        exact hh ▸ ht
      · have hyb := wordProperCuts_bounds inner hi y hy
        have hm : x % inner.sum = y := by
          simp only [he, Nat.add_mod, Nat.mul_mod_left, zero_add,
            Nat.mod_eq_of_lt hyb.2]
        omega
    · intro ht
      exact Or.inl ⟨x / inner.sum, ht, by nlinarith⟩
  · rw [ite_eq_right hmod]
    constructor
    · rintro (⟨t, ht, he⟩ | ⟨j, hj, y, hy, he⟩)
      · have hm : x % inner.sum = 0 := by rw [he, Nat.mul_mod_left]
        exact (hmod hm).elim
      · have hyb := wordProperCuts_bounds inner hi y hy
        simpa only [he, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt hyb.2] using hy
    · intro hc
      have hj : x / inner.sum < outer.sum := (Nat.div_lt_iff_lt_mul hW).mpr hT
      exact Or.inr ⟨x / inner.sum, hj, x % inner.sum, hc, by nlinarith⟩

/-- The actual composition obtained by concatenating the specified ordinary near powers. -/
def literalCompositionProduct {m n : ℕ} (γ : Composition m) (β : Composition n) :
    Composition (m * n) where
  blocks := wordCompose β.blocks γ.blocks
  blocks_pos := by
    intro a ha
    exact wordCompose_pos β.blocks γ.blocks (fun b hb => β.blocks_pos hb)
      (fun b hb => γ.blocks_pos hb) a ha
  blocks_sum := by rw [wordCompose_sum, γ.blocks_sum, β.blocks_sum]

/-- Canonical product cuts and the actual near-concatenated word define the same composition. -/
theorem compositionProduct_eq_literal {m n : ℕ} (γ : Composition m)
    (β : Composition n) (hn : 0 < n) :
    compositionProduct γ β = literalCompositionProduct γ β := by
  have he : properCuts (compositionProduct γ β) =
      properCuts (literalCompositionProduct γ β) := by
    ext x
    by_cases hx : 0 < x ∧ x < m * n
    · rw [compositionProduct_cuts γ β x hx.1 hx.2,
        ← wordProperCuts_blocks (literalCompositionProduct γ β)]
      change (if x % n = 0 then x / n ∈ properCuts γ else x % n ∈ properCuts β) ↔
        x ∈ wordProperCuts (wordCompose β.blocks γ.blocks)
      have hh := wordCompose_cuts_mod β.blocks γ.blocks (fun a ha => β.blocks_pos ha)
        (by rw [β.blocks_sum]; exact hn) (fun a ha => γ.blocks_pos ha) x
        (by simpa only [γ.blocks_sum, β.blocks_sum] using hx.2)
      simpa only [γ.blocks_sum, β.blocks_sum, wordProperCuts_blocks] using hh.symm
    · constructor <;> intro h <;> exact (hx (properCuts_bounds _ x h)).elim
  exact properCuts_injective he

/-- The full displayed list formula for the ordinary composition product. -/
theorem compositionProduct_blocks {m n : ℕ} (γ : Composition m)
    (β : Composition n) (hn : 0 < n) :
    (compositionProduct γ β).blocks =
      (γ.blocks.map (wordNearPower β.blocks)).flatten := by
  rw [compositionProduct_eq_literal γ β hn]
  exact wordCompose_eq_flatten β.blocks γ.blocks

/-- Ordinary composition distributes over literal outer concatenation. -/
theorem wordCompose_append (inner u v : List ℕ) :
    wordCompose inner (u ++ v) = wordCompose inner u ++ wordCompose inner v := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, wordCompose, ih, List.append_assoc]

/-- The actual ordinary composition product respects outer endpoint merging. -/
theorem wordCompose_near (inner : List ℕ) (hi : 0 < inner.sum)
    (u v : List ℕ) (hu : ∀ a ∈ u, 0 < a) (hv : ∀ a ∈ v, 0 < a) :
    wordCompose inner (wordNear u v) =
      wordNear (wordCompose inner u) (wordCompose inner v) := by
  rcases List.eq_nil_or_concat' u with rfl | ⟨u, a, rfl⟩
  · simp only [(wordNear_nil _).2, wordCompose]
  · cases v with
    | nil => simp only [(wordNear_nil _).1, wordCompose]
    | cons b v =>
      have ha := hu a (List.mem_append_right _ (List.mem_singleton_self _))
      have hb := hv b List.mem_cons_self
      have hna := word_ne_nil_of_sum_pos (wordNearPower inner a)
        (by rw [wordNearPower_sum]; exact Nat.mul_pos ha hi)
      have hnb := word_ne_nil_of_sum_pos (wordNearPower inner b)
        (by rw [wordNearPower_sum]; exact Nat.mul_pos hb hi)
      rw [wordNear_append_cons, wordCompose_append, wordCompose_append]
      simp only [wordCompose, List.append_nil]
      rw [wordNear_append_left _ _ _ hna, wordNear_append_right _ _ _ hnb,
        ← wordNearPower_add]

/-- Composing the outer ordinary near power equals taking the composed word's near power. -/
theorem wordCompose_nearPower (inner outer : List ℕ) (hi : 0 < inner.sum)
    (ho : ∀ a ∈ outer, 0 < a) (m : ℕ) :
    wordCompose inner (wordNearPower outer m) = wordNearPower (wordCompose inner outer) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change wordCompose inner (wordNear outer (wordNearPower outer m)) =
      wordNear (wordCompose inner outer) (wordNearPower (wordCompose inner outer) m)
    rw [wordCompose_near inner hi outer _ ho (wordNearPower_pos outer ho m), ih]

end SkewClassInflation
