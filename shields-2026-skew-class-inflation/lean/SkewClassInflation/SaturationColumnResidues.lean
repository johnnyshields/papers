/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationPowerMerge
import SkewClassInflation.SaturationWeights
import SkewClassInflation.MergeBetaSets
import SkewClassInflation.ZeroPrefixContraction
import SkewClassInflation.SuffixWords

/-!
# Distinguished column residues of general repeated powers

The literal parsing used for parameter injectivity in
`thm:repeated-block-saturation` of `shields-2026-skew-class-inflation.tex`.
Zero is the only full column beta in the period-zero residue class of a
single repeated power; the proof includes zero internal gaps.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- Every original one-copy column lies in the actual half-open period interval. -/
theorem power_one_column_bounds {x : ℤ}
    (hx : x ∈ (A.power 1 (by decide)).toBetaDiagram.colSet) :
    0 ≤ x ∧ x < A.spanIncrement := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  change 0 ≤ (A.power 1 (by decide)).zeta i ∧
    (A.power 1 (by decide)).zeta i < A.spanIncrement
  refine ⟨(A.power 1 (by decide)).zeta_nonneg i, ?_⟩
  have hmax := (A.power 1 (by decide)).zeta_strictAnti.antitone (Fin.zero_le i)
  have hr := (A.power 1 (by decide)).xi_sub_zeta 0
  rw [A.power_first] at hr
  have hs := A.power_span 1 (by decide)
  simp only [Nat.cast_one, one_mul] at hs
  have hb : (A.d : ℤ) < A.r 0 := by
    have := A.first_bound
    omega
  linarith only [hmax, hr, hs, hb]

/-- A repeated power has no nonterminal column in the period-zero residue class. -/
theorem power_column_zero_residue (m : ℕ) (hm : 0 < m) (x : ℤ)
    (hx : x ∈ (A.power m hm).toBetaDiagram.colSet) (hmod : x % A.spanIncrement = 0) : x = 0 := by
  induction m generalizing x with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst m
      have hb := A.power_one_column_bounds hx
      rw [Int.emod_eq_of_lt hb.1 hb.2] at hmod
      exact hmod
    · have hmp : 0 < m := by omega
      have he := congrArg (fun D : ConnectedProfile => D.2.toBetaDiagram.colSet)
        (A.merge_powers m 1 hmp (by decide))
      rw [← he, Profile.merge_colSet] at hx
      have hs : (A.power 1 (by decide)).xi 0 - A.d = A.spanIncrement := by
        rw [A.power_span]
        simp only [Nat.cast_one, one_mul, add_sub_cancel_right]
      have hshift : (fun y : ℤ => y + (A.power 1 (by decide)).xi 0 - A.d) =
          fun y => y + A.spanIncrement := by
        funext y
        rw [A.power_span]
        simp only [Nat.cast_one, one_mul]
        ring
      rw [hshift, hs] at hx
      obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
        have hymod : y % A.spanIncrement = 0 := by
          rw [← heq] at hmod
          simpa only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod] using hmod
        have hy0 := ih hmp y hy hymod
        apply False.elim
        apply hne
        rw [← heq, hy0, zero_add]
      · have hb := A.power_one_column_bounds hx
        rw [Int.emod_eq_of_lt hb.1 hb.2] at hmod
        exact hmod

/-- The full span of the actual ordered source chain is independent of its number of outer cuts. -/
theorem chain_span (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ m ∈ l, 0 < m) :
    (A.chain a ha l hl).2.xi 0 = ((a + l.sum : ℕ) : ℤ) * A.spanIncrement + A.d := by
  let α : Composition (a + l.sum) :=
    ⟨a :: l, by
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ha
      · exact hl m hm, rfl⟩
  have he := A.diagram_span α (by omega)
  exact he

/-- Period multiples in the full columns are exactly the proper suffix cuts and zero. -/
theorem chain_column_multiple (a : ℕ) (ha : 0 < a) (l : List ℕ)
    (hl : ∀ m ∈ l, 0 < m) (s : ℕ) :
    (s : ℤ) * A.spanIncrement ∈ (A.chain a ha l hl).2.toBetaDiagram.colSet ↔
      s = 0 ∨ s ∈ wordSuffixSet (a :: l) := by
  induction l generalizing a with
  | nil =>
    simp only [wordSuffixSet_single, Finset.notMem_empty, or_false]
    constructor
    · intro hx
      have he := A.power_column_zero_residue a ha ((s : ℤ) * A.spanIncrement) hx
        (Int.mul_emod_left _ _)
      have hs : (s : ℤ) = 0 := (mul_eq_zero.mp he).resolve_right (ne_of_gt A.spanIncrement_pos)
      exact_mod_cast hs
    · intro hs
      subst s
      rw [Nat.cast_zero, zero_mul]
      change 0 ∈ (A.power a ha).toBetaDiagram.colSet
      exact profile_zero_mem_colSet (A.power a ha)
  | cons b l ih =>
    let hb := hl b List.mem_cons_self
    let ht : ∀ m ∈ l, 0 < m := fun m hm => hl m (List.mem_cons_of_mem _ hm)
    let R := A.chain b hb l ht
    have hp : A.d < (A.power a ha).r (Fin.last (a * A.k)) := A.power_rows_above_seam a ha _
    have hq : A.d < R.2.r 0 := by
      rw [A.chain_first]
      have := A.first_bound
      omega
    change (s : ℤ) * A.spanIncrement ∈
      (Profile.join (A.power a ha) R.2 A.d hp hq).toBetaDiagram.colSet ↔ _
    rw [Profile.join_colSet]
    have hs := A.chain_span b hb l ht
    have hshift : (fun y : ℤ => y + R.2.xi 0 - A.d) =
        fun y => y + ((b + l.sum : ℕ) : ℤ) * A.spanIncrement := by
      funext y
      rw [hs]
      ring
    rw [hshift, wordSuffixSet_cons a (b :: l) (by simp)]
    simp only [List.sum_cons, Finset.mem_union, Finset.mem_image, Finset.mem_insert]
    constructor
    · rintro (⟨y, hy, he⟩ | hx)
      · have hymod : y % A.spanIncrement = 0 := by
          have hh := congrArg (fun x : ℤ => x % A.spanIncrement) he
          simpa only [Int.add_emod, Int.mul_emod_left, add_zero, Int.emod_emod] using hh
        have hy0 := A.power_column_zero_residue a ha y hy hymod
        have hseam : b + l.sum = s := by
          have hh := mul_right_cancel₀ (ne_of_gt A.spanIncrement_pos)
            (by simpa only [hy0, zero_add] using he)
          exact_mod_cast hh
        exact Or.inr (Or.inl hseam.symm)
      · rcases (ih b hb ht).mp hx with hs0 | hcut
        · exact Or.inl hs0
        · exact Or.inr (Or.inr hcut)
    · rintro (hs0 | hseam | hcut)
      · subst s
        right
        simpa only [Nat.cast_zero, zero_mul] using profile_zero_mem_colSet R.2
      · left
        refine ⟨0, profile_zero_mem_colSet (A.power a ha), ?_⟩
        rw [hseam]
        simp only [zero_add]
      · exact Or.inr ((ih b hb ht).mpr (Or.inr hcut))

/-- Full column betas recover every proper suffix of an arbitrary positive outer composition. -/
theorem diagram_column_multiple {M : ℕ} (α : Composition M) (hM : 0 < M) (s : ℕ) :
    (s : ℤ) * A.spanIncrement ∈ (A.diagram α hM).2.toBetaDiagram.colSet ↔
      s = 0 ∨ s ∈ suffixSet α := by
  rw [← wordSuffixSet_blocks α]
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    have ha := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
    have hl : ∀ m ∈ l, 0 < m := fun m hm =>
      α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hm)
    simpa only [he] using A.chain_column_multiple a ha l hl s

/-- The full literal source retains its outer composition, including repeated equal parts.

**Differs from the paper's route.** Recovers proper suffix cuts from period-zero
column betas rather than parsing the larger-gap word. -/
theorem diagram_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (fun α : Composition M => A.diagram α hM) := by
  intro α β he
  have hc := congrArg (fun D : ConnectedProfile => D.2.toBetaDiagram.colSet) he
  apply suffixSet_injective
  ext s
  by_cases hs : s = 0
  · subst s
    have hα : 0 ∉ suffixSet α := by
      intro hh
      have hb := Finset.mem_Ioo.mp (suffixSet_subset α hh)
      omega
    have hβ : 0 ∉ suffixSet β := by
      intro hh
      have hb := Finset.mem_Ioo.mp (suffixSet_subset β hh)
      omega
    simp only [hα, hβ]
  · have hα := A.diagram_column_multiple α hM s
    have hβ := A.diagram_column_multiple β hM s
    rw [hc] at hα
    simpa only [hs, false_or] using hα.symm.trans hβ

end SkewClassInflation.SaturationInner
