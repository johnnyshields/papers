/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ExposureLabels

/-!
# Finite peeling reaches an active extreme

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
A strict extreme among active classes is reached by successively removing exposed inactive
classes. The induction consumes an exposure producer at each step and strictly decreases
the number of remaining classes. Sorry-free.
-/

namespace SkewCornerDescent

open Classical in
/-- Finite inactive removal cannot bypass the chosen active extreme. The exposure producer
must preserve the balance property for every removed class; the omitted-class alternative
then identifies the target without assuming an active exposure in advance. -/
theorem finite_inactive_peeling_reaches_active_extreme {α : Type*}
    [Finite α] (e : α → ℤ) (root : α → ℝ)
    (eligible balanced : α → Prop) (positive : Bool) (target omitted : α)
    (hactive : e target ≠ 0) (htarget : eligible target)
    (hextreme : ∀ b, eligible b → e b ≠ 0 → b ≠ target →
      responseSign positive (root target - root b))
    (expose : ∀ S : Finset α, (∀ a ∈ S, e a = 0) → (∀ a ∈ S, balanced a) →
      target ∉ S → ∃ a, a ∉ S ∧ eligible a ∧
        (∀ b, b ∉ S → eligible b → b ≠ a → responseSign positive (root a - root b)) ∧
        ((e a = 0 ∧ balanced a) ∨ (e a ≠ 0 ∧ omitted = a))) :
    omitted = target := by
  classical
  let := Fintype.ofFinite α
  have loop : ∀ l : ℕ, ∀ S : Finset α, Fintype.card α - S.card = l →
      (∀ a ∈ S, e a = 0) → (∀ a ∈ S, balanced a) → target ∉ S →
      omitted = target := by
    intro l
    induction l using Nat.strong_induction_on with
    | h l ih =>
      intro S hsize he hb ht
      obtain ⟨a, ha, heligible, horder, halternative⟩ := expose S he hb ht
      by_cases hea : e a = 0
      · have hbalance : balanced a := by
          rcases halternative with h | h
          · exact h.2
          · exact (h.1 hea).elim
        have hat : a ≠ target := fun h => hactive (h ▸ hea)
        have ht' : target ∉ insert a S := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨Ne.symm hat, ht⟩
        have hlt : Fintype.card α - (insert a S).card < l := by
          have hle := Finset.card_le_univ (insert a S)
          rw [Finset.card_insert_of_notMem ha] at hle ⊢
          omega
        apply ih _ hlt (insert a S) rfl
        · intro b hb'
          rcases Finset.mem_insert.mp hb' with h | h
          · exact h ▸ hea
          · exact he b h
        · intro b hb'
          rcases Finset.mem_insert.mp hb' with h | h
          · exact h ▸ hbalance
          · exact hb b h
        · exact ht'
      · have hat : a = target := by
          by_contra hne
          have h₁ := horder target ht htarget (Ne.symm hne)
          have h₂ := hextreme a heligible hea hne
          cases positive <;> simp only [responseSign, Bool.false_eq_true, ite_false,
            ite_true] at h₁ h₂ <;> linarith
        rcases halternative with h | h
        · exact (hea h.1).elim
        · exact h.2.trans hat
  exact loop _ ∅ rfl (by intro a ha; exact (Finset.notMem_empty a ha).elim)
    (by intro a ha; exact (Finset.notMem_empty a ha).elim) (Finset.notMem_empty target)

end SkewCornerDescent
