/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ResiduePrefixWords
import SkewClassInflation.PeriodicCutFactorization

/-!
# Actual endpoint padding of positive compositions

The local-window construction for factor transport in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Padding changes only the first and last parts.  Its actual proper cuts
are translated uniformly, and padding by whole inner weights preserves
the complete residue word.  Sorry-free.
-/

namespace SkewClassInflation

/-- Add the specified natural amounts to the two actual endpoint parts. -/
def wordPadEnds (w : List ℕ) (L R : ℕ) : List ℕ := wordNear (wordNear [L] w) [R]

/-- Endpoint padding adds exactly the stated two amounts to the actual total weight. -/
theorem wordPadEnds_sum (w : List ℕ) (L R : ℕ) : (wordPadEnds w L R).sum = L + w.sum + R := by
  simp only [wordPadEnds, wordNear_sum, List.sum_singleton]

private theorem left_padding_cons (L b : ℕ) (w : List ℕ) :
    wordNear [L] (b :: w) = (L + b) :: w := by
  simpa only [List.nil_append] using wordNear_append_cons [] L b w

private theorem left_padding_pos (w : List ℕ) (L : ℕ) (hne : w ≠ [])
    (hw : ∀ a ∈ w, 0 < a) : ∀ a ∈ wordNear [L] w, 0 < a := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons b w =>
    rw [left_padding_cons]
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · have hb := hw b List.mem_cons_self
      omega
    · exact hw a (List.mem_cons_of_mem _ ha)

/-- Positive original parts remain positive even when one or both padding amounts vanish. -/
theorem wordPadEnds_pos (w : List ℕ) (L R : ℕ) (hne : w ≠ [])
    (hw : ∀ a ∈ w, 0 < a) : ∀ a ∈ wordPadEnds w L R, 0 < a := by
  have hu : wordNear [L] w ≠ [] := wordNear_ne_nil [L] w (by simp) hne
  have hpos := left_padding_pos w L hne hw
  obtain ⟨u, b, he⟩ := (List.eq_nil_or_concat' (wordNear [L] w)).resolve_left hu
  unfold wordPadEnds
  rw [he, wordNear_append_cons]
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · apply hpos a
    rw [he]
    exact List.mem_append_left _ ha
  · have hab : a = b + R := by simpa only [List.mem_cons, List.mem_nil_iff, or_false] using ha
    have hb : 0 < b := hpos b (by
      rw [he]
      exact List.mem_append_right _ (List.mem_singleton_self _))
    omega

/-- Padding a nonempty actual word changes no part count. -/
theorem wordPadEnds_length (w : List ℕ) (L R : ℕ) (hne : w ≠ []) :
    (wordPadEnds w L R).length = w.length := by
  have hleft : (wordNear [L] w).length = w.length := by
    cases w with
    | nil => exact (hne rfl).elim
    | cons b w => simp only [left_padding_cons, List.length_cons]
  have hu : wordNear [L] w ≠ [] := wordNear_ne_nil [L] w (by simp) hne
  obtain ⟨u, b, he⟩ := (List.eq_nil_or_concat' (wordNear [L] w)).resolve_left hu
  unfold wordPadEnds
  rw [he, wordNear_append_cons]
  rw [he] at hleft
  simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
    List.length_singleton] using hleft

/-- The actual padded proper cuts are exactly the translated original proper cuts. -/
theorem wordPadEnds_cuts (w : List ℕ) (L R : ℕ) (hne : w ≠ []) :
    wordProperCuts (wordPadEnds w L R) = (wordProperCuts w).image (fun x => L + x) := by
  have hu : wordNear [L] w ≠ [] := wordNear_ne_nil [L] w (by simp) hne
  rw [wordPadEnds, wordProperCuts_near _ [R] hu (by simp), wordProperCuts_single,
    Finset.image_empty, Finset.union_empty,
    wordProperCuts_near [L] w (by simp) hne, wordProperCuts_single, Finset.empty_union,
    List.sum_singleton]

private theorem left_padding_mod (w : List ℕ) (L n : ℕ) (hne : w ≠ []) (hL : n ∣ L) :
    (wordNear [L] w).map (fun x => x % n) = w.map (fun x => x % n) := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons b w =>
    rw [left_padding_cons]
    simp only [List.map_cons, Nat.add_mod, Nat.mod_eq_zero_of_dvd hL, zero_add, Nat.mod_mod]

private theorem right_padding_mod (w : List ℕ) (R n : ℕ) (hne : w ≠ []) (hR : n ∣ R) :
    (wordNear w [R]).map (fun x => x % n) = w.map (fun x => x % n) := by
  obtain ⟨u, b, rfl⟩ := (List.eq_nil_or_concat' w).resolve_left hne
  rw [wordNear_append_cons]
  simp only [List.map_append, List.map_cons, List.map_nil, Nat.add_mod,
    Nat.mod_eq_zero_of_dvd hR, add_zero, Nat.mod_mod]

/-- Whole-weight endpoint padding preserves every actual part residue, with multiplicity. -/
theorem wordPadEnds_mod (w : List ℕ) (L R n : ℕ) (hne : w ≠ []) (hL : n ∣ L) (hR : n ∣ R) :
    (wordPadEnds w L R).map (fun x => x % n) = w.map (fun x => x % n) := by
  rw [wordPadEnds, right_padding_mod _ R n (wordNear_ne_nil [L] w (by simp) hne) hR,
    left_padding_mod w L n hne hL]

/-- A genuine multipart positive composition has no part equal to its entire weight. -/
theorem composition_part_lt_of_multipart {N : ℕ} (α : Composition N) (hl : 2 ≤ α.length)
    (a : ℕ) (ha : a ∈ α.blocks) : a < N := by
  have hN : 0 < N := by have := α.length_le; omega
  have hne : α ≠ Composition.single N hN := by
    intro he
    have hh := congrArg Composition.length he
    rw [Composition.single_length] at hh
    omega
  have hparts := (Composition.ne_single_iff hN).mp hne
  rw [← α.ofFn_blocksFun] at ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact hparts i

/-- The full actual padded composition, with its exact larger total weight. -/
def paddedComposition {N : ℕ} (α : Composition N) (hN : 0 < N) (L R : ℕ) :
    Composition (L + N + R) where
  blocks := wordPadEnds α.blocks L R
  blocks_pos := by
    intro a ha
    apply wordPadEnds_pos α.blocks L R (fun he => (Nat.ne_of_gt hN) (α.blocks_eq_nil.mp he))
      (fun b hb => α.blocks_pos hb) a ha
  blocks_sum := by rw [wordPadEnds_sum, α.blocks_sum]

/-- Its actual proper cuts are exactly the translated original proper positions. -/
theorem paddedComposition_cuts {N : ℕ} (α : Composition N) (hN : 0 < N) (L R : ℕ) :
    properCuts (paddedComposition α hN L R) = (properCuts α).image (fun x => L + x) := by
  rw [← wordProperCuts_blocks, ← wordProperCuts_blocks α]
  exact wordPadEnds_cuts α.blocks L R (fun he => (Nat.ne_of_gt hN) (α.blocks_eq_nil.mp he))

/-- Padding retains the actual original number of positive parts. -/
theorem paddedComposition_length {N : ℕ} (α : Composition N) (hN : 0 < N) (L R : ℕ) :
    (paddedComposition α hN L R).length = α.length :=
  wordPadEnds_length α.blocks L R (fun he => (Nat.ne_of_gt hN) (α.blocks_eq_nil.mp he))

/-- Whole-weight padding of a multipart inner has exactly its original positive residue word. -/
theorem paddedComposition_residueWord {N : ℕ} (α : Composition N) (hN : 0 < N)
    (hl : 2 ≤ α.length) (L R : ℕ) (hL : N ∣ L) (hR : N ∣ R) :
    residueWord (paddedComposition α hN L R).blocks N = α.blocks := by
  have hne : α.blocks ≠ [] := fun he => (Nat.ne_of_gt hN) (α.blocks_eq_nil.mp he)
  have hmap : α.blocks.map (fun x => x % N) = α.blocks := by
    calc
      _ = α.blocks.map id := List.map_congr_left (by
        intro a ha
        exact Nat.mod_eq_of_lt (composition_part_lt_of_multipart α hl a ha))
      _ = _ := List.map_id α.blocks
  change ((wordPadEnds α.blocks L R).map (fun x => x % N)).filter
    (fun x => decide (x ≠ 0)) = α.blocks
  rw [wordPadEnds_mod α.blocks L R N hne hL hR, hmap]
  apply List.filter_eq_self.mpr
  intro a ha
  simp only [decide_eq_true_eq]
  exact Nat.ne_of_gt (α.blocks_pos ha)

end SkewClassInflation
